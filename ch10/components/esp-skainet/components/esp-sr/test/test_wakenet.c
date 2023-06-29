/* test_mean.c: Implementation of a testable component.

   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/

#include "string.h"
#include <limits.h>
#include "unity.h"

#include "model_path.h"
#include "esp_wn_iface.h"
#include "esp_wn_models.h"
#include "hilexin.h"
#include "dl_lib_convq_queue.h"
#include <sys/time.h>

TEST_CASE("wakenet create/destroy API & memory leak", "[wn]")
{
    vTaskDelay(500 / portTICK_PERIOD_MS);
    int start_size = heap_caps_get_free_size(MALLOC_CAP_8BIT);
    int start_internal_size = heap_caps_get_free_size(MALLOC_CAP_INTERNAL);
    srmodel_list_t *models = esp_srmodel_init("model");
    char *model_name = esp_srmodel_filter(models, ESP_WN_PREFIX, NULL);
    esp_wn_iface_t *wakenet = esp_wn_handle_from_name(model_name);

    // test model loading time
    struct timeval tv_start, tv_end;
    gettimeofday(&tv_start, NULL);
    model_iface_data_t *model_data = wakenet->create(model_name, DET_MODE_3CH_95);
    gettimeofday(&tv_end, NULL);
    int tv_ms = (tv_end.tv_sec - tv_start.tv_sec) * 1000 + (tv_end.tv_usec - tv_start.tv_usec) / 1000;
    printf("create latency:%d ms\n", tv_ms);

    // test model memory concumption
    int create_size = start_size - heap_caps_get_free_size(MALLOC_CAP_8BIT);
    int create_internal_size = start_internal_size - heap_caps_get_free_size(MALLOC_CAP_INTERNAL);
    printf("Internal RAM: %d, PSRAM:%d\n", create_internal_size, create_size - create_internal_size);
    wakenet->destroy(model_data);
    esp_srmodel_deinit(models);

    // test memory leak
    int first_end_size = heap_caps_get_free_size(MALLOC_CAP_8BIT);
    int last_end_size = first_end_size;
    int mem_leak = start_size - last_end_size;
    printf("create&destroy times:%d, memory leak:%d\n", 1, mem_leak);

    for (int i = 0; i < 6; i++) {
        printf("init partition ...\n");
        models = esp_srmodel_init("model");
        model_name = esp_srmodel_filter(models, ESP_WN_PREFIX, NULL);
        wakenet = esp_wn_handle_from_name(model_name);

        printf("create ...\n");
        // typedef enum {
        //     DET_MODE_90 = 0,       // Normal
        //     DET_MODE_95 = 1,       // Aggressive
        //     DET_MODE_2CH_90 = 2,
        //     DET_MODE_2CH_95 = 3,
        //     DET_MODE_3CH_90 = 4,
        //     DET_MODE_3CH_95 = 5,
        // } det_mode_t;
        model_data = wakenet->create(model_name, i);

        printf("destroy ...\n");
        wakenet->destroy(model_data);
        esp_srmodel_deinit(models);

        last_end_size = heap_caps_get_free_size(MALLOC_CAP_8BIT);
        mem_leak = start_size - last_end_size;
        printf("create&destroy times:%d, memory leak:%d\n", i + 2, mem_leak);
    }

    TEST_ASSERT_EQUAL(true, (mem_leak) < 1000 && last_end_size == first_end_size);
}

TEST_CASE("wakenet detect API & cpu loading", "[wn]")
{
    vTaskDelay(500 / portTICK_PERIOD_MS);
    srmodel_list_t *models = esp_srmodel_init("model");
    char *model_name = esp_srmodel_filter(models, ESP_WN_PREFIX, NULL);
    esp_wn_iface_t *wakenet = esp_wn_handle_from_name(model_name);
    model_iface_data_t *model_data = wakenet->create(model_name, DET_MODE_95);
    int frequency = wakenet->get_samp_rate(model_data);
    int audio_chunksize = wakenet->get_samp_chunksize(model_data) * sizeof(int16_t);
    int16_t *buffer = malloc(audio_chunksize);
    int chunks = 0;
    int detected = 0;
    struct timeval tv_start, tv_end;
    gettimeofday(&tv_start, NULL);

    while (1) {
        if ((chunks + 1)*audio_chunksize <= sizeof(hilexin)) {
            memcpy(buffer, hilexin + chunks * audio_chunksize, audio_chunksize);
        } else {
            memset(buffer, 0, audio_chunksize);
        }
        int res = wakenet->detect(model_data, buffer);
        if (res > 0) {
            detected = 1;
        }

        chunks++;
        if (detected == 1) {
            break;
        }
    }
    gettimeofday(&tv_end, NULL);
    int tv_ms = (tv_end.tv_sec - tv_start.tv_sec) * 1000 + (tv_end.tv_usec - tv_start.tv_usec) / 1000;
    int run_ms = (chunks) * audio_chunksize / sizeof(int16_t) * 1000 / frequency;
    float cpu_loading = tv_ms * 100.0 / run_ms;
    printf("Done! Took %d ms to parse %d ms worth of samples in %d iterations. CPU loading(single core):%.1f%%\n",
           tv_ms, run_ms, chunks, cpu_loading);

    wakenet->destroy(model_data);
    esp_srmodel_deinit(models);
    TEST_ASSERT_EQUAL(true, (cpu_loading < 75 && detected == 1));
}