// Copyright 2021 Espressif Systems (Shanghai) PTE LTD
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <string.h>
#include "esp_partition.h"
#include "esp_diagnostics.h"
#include "esp_ota_ops.h"
#include "esp_log.h"
#include "sys/time.h"
#include "esp_system.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "soc/soc_memory_layout.h"
#include "esp_debug_helpers.h"
#include "esp_diagnostics_metrics.h"
#include "esp_diagnostics_variables.h"

#if ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 3
#include <esp_rom_crc.h>
#define ESP_CRC32_LE(crc, buf, len) esp_rom_crc32_le(crc, buf, len)
#else
#include <esp_crc.h>
#define ESP_CRC32_LE(crc, buf, len) esp_crc32_le(crc, buf, len)
#endif

#define TASK_SNAP_TAG       "task_snap"
#define TASK_INFO_FMT       "task:%s state:%d high_watermark:%d "
#define BT_FMT              "bt:"
#define BT_DEPTH_FMT_1      "0x%x "
#define BT_DEPTH_FMT_2      "0x%x 0x%x "
#define BT_DEPTH_FMT_3      "0x%x 0x%x 0x%x "
#define BT_DEPTH_FMT_4      "0x%x 0x%x 0x%x 0x%x "
#define BT_DEPTH_FMT_8      BT_DEPTH_FMT_4 BT_DEPTH_FMT_4
#define BT_DEPTH_FMT_16     BT_DEPTH_FMT_8 BT_DEPTH_FMT_8

#if ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 3
#define TASK_GET_NAME(handle) pcTaskGetName(handle)
#else
#define TASK_GET_NAME(handle) pcTaskGetTaskName(handle)
#endif

esp_err_t esp_diag_device_info_get(esp_diag_device_info_t *device_info)
{
    esp_chip_info_t chip;
    const esp_app_desc_t *app_desc;

    if (!device_info) {
        return ESP_ERR_INVALID_ARG;
    }

    esp_chip_info(&chip);
    device_info->chip_model = chip.model;
    device_info->chip_rev = chip.revision;
    device_info->reset_reason = esp_reset_reason();
    app_desc = esp_ota_get_app_description();
    strncpy(device_info->app_version, app_desc->version, sizeof(device_info->app_version) - 1);
    device_info->app_version[sizeof(device_info->app_version) - 1] = 0;
    strncpy(device_info->project_name, app_desc->project_name, sizeof(device_info->project_name) - 1);
    device_info->project_name[sizeof(device_info->project_name) - 1] = 0;
    esp_ota_get_app_elf_sha256(device_info->app_elf_sha256, sizeof(device_info->app_elf_sha256));
    return ESP_OK;
}

uint64_t esp_diag_timestamp_get(void)
{
    struct timeval tv_now;
    if (gettimeofday(&tv_now, NULL) == 0) {
        return ((uint64_t)tv_now.tv_sec * 1000000L + (uint64_t)tv_now.tv_usec);
    } else {
        /* esp_log_timestamp returns timestamp in milliseconds */
        return ((uint64_t)esp_log_timestamp() * 1000);
    }
}

#ifndef CONFIG_IDF_TARGET_ARCH_RISCV
static void diag_task_get_bt(esp_diag_task_bt_t *bt_info, XtExcFrame *stack)
{
    esp_backtrace_frame_t frame = {
        .pc = stack->pc,
        .sp = stack->a1,
        .next_pc = stack->a0,
    };
    uint32_t i = 0;
    uint32_t max_depth = sizeof(bt_info->bt) / sizeof(bt_info->bt[0]);
    bool corrupted = !(esp_stack_ptr_is_sane(frame.sp) &&
                     esp_ptr_executable((void *)esp_cpu_process_stack_pc(frame.pc)));

    bt_info->bt[i++] = esp_cpu_process_stack_pc(frame.pc);
    while (max_depth-- > 0 && frame.next_pc && !corrupted) {
        if (!esp_backtrace_get_next_frame(&frame)) {
            corrupted = true;
        }
        if (corrupted == false) {
            bt_info->bt[i++] = esp_cpu_process_stack_pc(frame.pc);
        }
    }
    bt_info->depth = i;
    bt_info->corrupted = corrupted;
}
#endif /* !CONFIG_IDF_TARGET_ARCH_RISCV */

uint32_t esp_diag_task_snapshot_get(esp_diag_task_info_t *tasks, size_t size)
{
    if (!tasks || !size) {
        return 0;
    }
    unsigned irq_state = portENTER_CRITICAL_NESTED();
#if !CONFIG_FREERTOS_UNICORE
    int other_cpu = xPortGetCoreID() ? 0 : 1;
    esp_cpu_stall(other_cpu);
#endif

    uint32_t i = 0;
    uint32_t task_count = uxTaskGetNumberOfTasks();
    TaskSnapshot_t *snapshots = calloc(task_count, sizeof(TaskSnapshot_t));
    if (!snapshots) {
        return 0;
    }
    size_t tcb_size; /* unused */
    uint32_t count = uxTaskGetSnapshotAll(snapshots, task_count, &tcb_size);
    if (count == 0) {
        free(snapshots);
        return 0;
    }
    for (i = 0; i < count; i++) {
        TaskHandle_t handle = (TaskHandle_t)snapshots[i].pxTCB;
        char *name = TASK_GET_NAME(handle);
        if (name && *name) {
            strncpy(tasks[i].name, name, strlen(name));
        }
        tasks[i].state = eTaskGetState(handle);
        tasks[i].high_watermark = uxTaskGetStackHighWaterMark(handle);
#ifndef CONFIG_IDF_TARGET_ARCH_RISCV
        diag_task_get_bt(&tasks[i].bt_info, (XtExcFrame *)snapshots[i].pxTopOfStack);
#endif /* !CONFIG_IDF_TARGET_ARCH_RISCV */
    }
    free(snapshots);

#if !CONFIG_FREERTOS_UNICORE
    esp_cpu_unstall(other_cpu);
#endif
    portEXIT_CRITICAL_NESTED(irq_state);
    return i;
}

#if CONFIG_IDF_TARGET_ARCH_RISCV
static void print_task_info(esp_diag_task_info_t *task)
{
    ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT, task->name, task->state, task->high_watermark);
}
#else
static void print_task_info(esp_diag_task_info_t *task)
{
    switch(task->bt_info.depth) {
        case 1:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_1,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0]);
            break;
        case 2:
             ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_2,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1]);
            break;
        case 3:
             ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_3,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2]);
            break;
        case 4:
             ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_4,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3]);
            break;
        case 5:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_4 BT_DEPTH_FMT_1,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4]);
            break;
        case 6:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_4 BT_DEPTH_FMT_2,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5]);
            break;
        case 7:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_4 BT_DEPTH_FMT_3,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6]);
            break;
        case 8:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7]);
            break;
        case 9:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8 BT_DEPTH_FMT_1,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8]);
            break;
        case 10:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8 BT_DEPTH_FMT_2,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8], task->bt_info.bt[9]);
            break;
        case 11:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8 BT_DEPTH_FMT_3,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8], task->bt_info.bt[9], task->bt_info.bt[10]);
            break;
        case 12:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8 BT_DEPTH_FMT_4,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8], task->bt_info.bt[9], task->bt_info.bt[10], task->bt_info.bt[11]);
            break;
        case 13:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8 BT_DEPTH_FMT_4 BT_DEPTH_FMT_1,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8], task->bt_info.bt[9], task->bt_info.bt[10], task->bt_info.bt[11],
                           task->bt_info.bt[12]);
            break;
        case 14:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8 BT_DEPTH_FMT_4 BT_DEPTH_FMT_2,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8], task->bt_info.bt[9], task->bt_info.bt[10], task->bt_info.bt[11],
                           task->bt_info.bt[12], task->bt_info.bt[13]);
            break;
        case 15:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_8 BT_DEPTH_FMT_4 BT_DEPTH_FMT_3,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8], task->bt_info.bt[9], task->bt_info.bt[10], task->bt_info.bt[11],
                           task->bt_info.bt[12], task->bt_info.bt[13], task->bt_info.bt[14]);
            break;
        case 16:
            ESP_DIAG_EVENT(TASK_SNAP_TAG, TASK_INFO_FMT BT_FMT BT_DEPTH_FMT_16,
                           task->name, task->state, task->high_watermark,
                           task->bt_info.bt[0], task->bt_info.bt[1], task->bt_info.bt[2], task->bt_info.bt[3],
                           task->bt_info.bt[4], task->bt_info.bt[5], task->bt_info.bt[6], task->bt_info.bt[7],
                           task->bt_info.bt[8], task->bt_info.bt[9], task->bt_info.bt[10], task->bt_info.bt[11],
                           task->bt_info.bt[12], task->bt_info.bt[13], task->bt_info.bt[14], task->bt_info.bt[15]);
            break;
    }
}
#endif /* CONFIG_IDF_TARGET_ARCH_RISCV */

void esp_diag_task_snapshot_dump(void)
{
    int i;
    size_t task_count = uxTaskGetNumberOfTasks();
    esp_diag_task_info_t *tasks = calloc(1, sizeof(esp_diag_task_info_t) * task_count);
    if (!tasks) {
        return;
    }
    uint32_t count = esp_diag_task_snapshot_get(tasks, task_count);
    for (i = 0; i < count; i++) {
        print_task_info(&tasks[i]);
    }
    free(tasks);
}

uint32_t esp_diag_meta_crc_get(void)
{
    uint32_t crc = 0;
#if CONFIG_DIAG_ENABLE_METRICS
    uint32_t metrics_len = 0;
    const esp_diag_metrics_meta_t *metrics = esp_diag_metrics_meta_get_all(&metrics_len);
    if (metrics) {
        uint32_t i;
        for (i = 0; i < metrics_len; i++) {
            crc = ESP_CRC32_LE(crc, (const uint8_t *)metrics[i].tag, strlen(metrics[i].tag));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)metrics[i].key, strlen(metrics[i].key));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)metrics[i].label, strlen(metrics[i].label));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)metrics[i].path, strlen(metrics[i].path));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)&metrics[i].type, sizeof(metrics[i].type));
        }
    }
#endif /* CONFIG_DIAG_ENABLE_METRICS */

#if CONFIG_DIAG_ENABLE_VARIABLES
    uint32_t variables_len = 0;
    const esp_diag_variable_meta_t *variables = esp_diag_variable_meta_get_all(&variables_len);
    if (variables) {
        uint32_t i;
        for (i = 0; i < variables_len; i++) {
            crc = ESP_CRC32_LE(crc, (const uint8_t *)variables[i].tag, strlen(variables[i].tag));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)variables[i].key, strlen(variables[i].key));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)variables[i].label, strlen(variables[i].label));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)variables[i].path, strlen(variables[i].path));
            crc = ESP_CRC32_LE(crc, (const uint8_t *)&variables[i].type, sizeof(variables[i].type));
        }
    }
#endif /* CONFIG_DIAG_ENABLE_VARIABLES */
    return crc;
}
