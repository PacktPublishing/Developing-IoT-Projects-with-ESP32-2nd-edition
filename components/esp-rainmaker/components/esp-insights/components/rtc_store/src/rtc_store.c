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

#include <stdint.h>
#include <string.h>
#include "soc/soc_memory_layout.h"
#include "esp_system.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "rbuf.h"
#include "rtc_store.h"

#define DIAG_CRITICAL_BUF_SIZE        CONFIG_RTC_STORE_CRITICAL_DATA_SIZE
#define NON_CRITICAL_DATA_SIZE        (CONFIG_RTC_STORE_DATA_SIZE - DIAG_CRITICAL_BUF_SIZE)

/* If data is perfectly aligned then buffers get wrapped and we have to perform two read
 * operation to get all the data, +1 ensures that data will be moved to the start of buffer
 * when there is not enough space at the end of buffer.
 */
#if ((NON_CRITICAL_DATA_SIZE % 4) == 0)
#define DIAG_NON_CRITICAL_BUF_SIZE    (NON_CRITICAL_DATA_SIZE + 1)
#else
#define DIAG_NON_CRITICAL_BUF_SIZE    NON_CRITICAL_DATA_SIZE
#endif

/* When buffer is filled beyond configured capacity then we post an event.
 * In case of failure in sending data over the network, new critical data is dropped and
 * non-critical data is overwritten.
 */

/* When current free size of buffer drops below (100 - reporting_watermark)% then we post an event */
#define DIAG_CRITICAL_DATA_REPORTING_WATERMARK \
    ((DIAG_CRITICAL_BUF_SIZE * (100 - CONFIG_RTC_STORE_REPORTING_WATERMARK_PERCENT)) / 100)
#define DIAG_NON_CRITICAL_DATA_REPORTING_WATERMARK \
    ((DIAG_NON_CRITICAL_BUF_SIZE * (100 - CONFIG_RTC_STORE_REPORTING_WATERMARK_PERCENT)) / 100)

ESP_EVENT_DEFINE_BASE(RTC_STORE_EVENT);

typedef struct {
    size_t read_offset;
    uint32_t len;
    uint8_t *buf;
    uint32_t size;
} data_store_t;

typedef struct {
    rbuf_handle_t ringbuf;
    SemaphoreHandle_t lock;
    data_store_t *store;
} rbuf_data_t;

typedef struct {
    bool init;
    rbuf_data_t critical;
    rbuf_data_t non_critical;
    uint8_t dummy_buf[32];
} rtc_store_priv_data_t;

typedef struct {
    struct {
        data_store_t store;
        uint8_t buf[DIAG_CRITICAL_BUF_SIZE];
    } critical;
    struct {
        data_store_t store;
        uint8_t buf[DIAG_NON_CRITICAL_BUF_SIZE];
    } non_critical;
} rtc_store_t;

static rtc_store_priv_data_t s_priv_data;
RTC_NOINIT_ATTR static rtc_store_t s_rtc_store;

static void rtc_store_read_complete(uint32_t len, rbuf_data_t *rbuf_data)
{
    rbuf_data->store->len -= len;
    rbuf_get_info(rbuf_data->ringbuf, NULL,
                  &rbuf_data->store->read_offset,
                  NULL, NULL, NULL);
}

static void rtc_store_write_complete(uint32_t len, rbuf_data_t *rbuf_data)
{
    rbuf_data->store->len += len;
}

static void rtc_store_records_align(size_t dummy_data_len, rbuf_data_t *rbuf_data)
{
    size_t data_len;
    /* Receive all the data in the rbuf, to be inserted later */
    void *data = rbuf_receive(rbuf_data->ringbuf, &data_len, 0);
    if (data) {
        rbuf_return_item(rbuf_data->ringbuf, data);
    }

    while (dummy_data_len > 0) {
        if (dummy_data_len >= sizeof(s_priv_data.dummy_buf)) {
            rbuf_send(rbuf_data->ringbuf, s_priv_data.dummy_buf, sizeof(s_priv_data.dummy_buf), 0);
            dummy_data_len -= sizeof(s_priv_data.dummy_buf);
        } else {
            rbuf_send(rbuf_data->ringbuf, s_priv_data.dummy_buf, dummy_data_len , 0);
            dummy_data_len = 0;
        }
    }
    void *dummy_data = rbuf_receive(rbuf_data->ringbuf, &dummy_data_len, 0);
    if (dummy_data) {
        rbuf_return_item(rbuf_data->ringbuf, dummy_data);
    }
    /* Reinsert the previously received data */
    if (data) {
        rbuf_send(rbuf_data->ringbuf, data, data_len, 0);
    }
    /* reset the read offset */
    rbuf_data->store->read_offset = 0;
}

esp_err_t rtc_store_critical_data_write(void *data, size_t len)
{
    size_t write_size;
    esp_err_t ret;

    if (!data || !len) {
        return ESP_ERR_INVALID_ARG;
    }
    if (!s_priv_data.init) {
        return ESP_ERR_INVALID_STATE;
    }

    xSemaphoreTake(s_priv_data.critical.lock, portMAX_DELAY);
    rbuf_get_info(s_priv_data.critical.ringbuf, NULL, NULL, &write_size, NULL, NULL);
    write_size = DIAG_CRITICAL_BUF_SIZE - write_size;
    if ((rbuf_get_cur_free_size(s_priv_data.critical.ringbuf) > write_size) && (write_size < len)) {
        rtc_store_records_align(write_size, &s_priv_data.critical);
    }

    if (rbuf_send(s_priv_data.critical.ringbuf, data, len, 0) == pdTRUE) {
        rtc_store_write_complete(len, &s_priv_data.critical);
        ret = ESP_OK;
    } else {
        esp_event_post(RTC_STORE_EVENT, RTC_STORE_EVENT_CRITICAL_DATA_WRITE_FAIL, data, len, 0);
        ret = ESP_FAIL;
    }

    size_t curr_free = rbuf_get_cur_free_size(s_priv_data.critical.ringbuf);
    if (curr_free < DIAG_CRITICAL_DATA_REPORTING_WATERMARK) {
        esp_event_post(RTC_STORE_EVENT, RTC_STORE_EVENT_CRITICAL_DATA_LOW_MEM, NULL, 0, 0);
    }
    xSemaphoreGive(s_priv_data.critical.lock);
    return ret;
}

esp_err_t rtc_store_non_critical_data_write(const char *dg, void *data, size_t len)
{
    if (!dg || !len || !data) {
        return ESP_ERR_INVALID_ARG;
    }
    if (!esp_ptr_in_drom(dg)) {
        return ESP_ERR_INVALID_ARG;
    }
    if (!s_priv_data.init) {
        return ESP_ERR_INVALID_STATE;
    }
    rtc_store_non_critical_data_hdr_t header;
    size_t req_free = sizeof(header) + len;
    size_t write_size;
    size_t receive_size;

    if (xSemaphoreTake(s_priv_data.non_critical.lock, 0) == pdFALSE) {
        return ESP_FAIL;
    }
    /* Make enough room for the item */
    while (rbuf_get_cur_free_size(s_priv_data.non_critical.ringbuf) < req_free) {
        memcpy(&header, s_priv_data.non_critical.store->buf + s_priv_data.non_critical.store->read_offset, sizeof(header));

        void *__data = rbuf_receive_upto(s_priv_data.non_critical.ringbuf, &receive_size, 0, sizeof(header) + header.len);
        if (__data) {
            rbuf_return_item(s_priv_data.non_critical.ringbuf, __data);
            rtc_store_read_complete(receive_size, &s_priv_data.non_critical);
        }
    }
    /* get the current write head */
    rbuf_get_info(s_priv_data.non_critical.ringbuf, NULL, NULL, &write_size, NULL, NULL);
    /* Room at the end of buffer */
    write_size = DIAG_NON_CRITICAL_BUF_SIZE - write_size;
    if ((write_size < req_free)) {
        rtc_store_records_align(write_size, &s_priv_data.non_critical);
    }

    /* write header */
    memset(&header, 0, sizeof(header));
    header.dg = dg;
    header.len = len;
    rbuf_send(s_priv_data.non_critical.ringbuf, &header, sizeof(header), 0);
    /* write data */
    rbuf_send(s_priv_data.non_critical.ringbuf, data, len, 0);
    /* update indices */
    rtc_store_write_complete(req_free, &s_priv_data.non_critical);

    size_t curr_free = rbuf_get_cur_free_size(s_priv_data.non_critical.ringbuf);
    if (curr_free < DIAG_NON_CRITICAL_DATA_REPORTING_WATERMARK) {
        esp_event_post(RTC_STORE_EVENT, RTC_STORE_EVENT_NON_CRITICAL_DATA_LOW_MEM, NULL, 0, 0);
    }
    xSemaphoreGive(s_priv_data.non_critical.lock);
    return ESP_OK;
}

static const void *rtc_store_data_read_and_lock(size_t *size, rbuf_data_t *rbuf_data)
{
    if (!size) {
        return NULL;
    }
    if (!s_priv_data.init) {
        return NULL;
    }
    xSemaphoreTake(rbuf_data->lock, portMAX_DELAY);

    *size = rbuf_data->store->len;
    if (rbuf_data->store->read_offset + rbuf_data->store->len > rbuf_data->store->size) {
        /* data is wrapped */
        *size = rbuf_data->store->size - rbuf_data->store->read_offset;
    }
    if (*size) {
        return (rbuf_data->store->buf + rbuf_data->store->read_offset);
    }
    xSemaphoreGive(rbuf_data->lock);
    return NULL;
}

static esp_err_t rtc_store_data_release_and_unlock(size_t size, rbuf_data_t *rbuf_data)
{
    size_t receive_size;
    void *data;

    if (!s_priv_data.init) {
        return ESP_ERR_INVALID_STATE;
    }
    data = rbuf_receive_upto(rbuf_data->ringbuf, &receive_size, 0, size);
    if (data) {
        rbuf_return_item(rbuf_data->ringbuf, data);
        rtc_store_read_complete(receive_size, rbuf_data);
    }
    xSemaphoreGive(rbuf_data->lock);
    return ESP_OK;
}

static esp_err_t rtc_store_data_release(size_t size, rbuf_data_t *rbuf_data)
{
    if (!s_priv_data.init) {
        return ESP_ERR_INVALID_STATE;
    }
    size_t data_size;
    if (rtc_store_data_read_and_lock(&data_size, rbuf_data)) {
        rtc_store_data_release_and_unlock(size, rbuf_data);
    }
    return ESP_OK;
}

const void *rtc_store_critical_data_read_and_lock(size_t *size)
{
    return rtc_store_data_read_and_lock(size, &s_priv_data.critical);
}

const void *rtc_store_non_critical_data_read_and_lock(size_t *size)
{
    return rtc_store_data_read_and_lock(size, &s_priv_data.non_critical);
}

esp_err_t rtc_store_critical_data_release_and_unlock(size_t size)
{
    return rtc_store_data_release_and_unlock(size, &s_priv_data.critical);
}

esp_err_t rtc_store_non_critical_data_release_and_unlock(size_t size)
{
    return rtc_store_data_release_and_unlock(size, &s_priv_data.non_critical);
}

esp_err_t rtc_store_critical_data_release(size_t size)
{
    return rtc_store_data_release(size, &s_priv_data.critical);
}

esp_err_t rtc_store_non_critical_data_release(size_t size)
{
    return rtc_store_data_release(size, &s_priv_data.non_critical);
}

static void rtc_store_rbuf_deinit(rbuf_data_t *rbuf_data)
{
    if (rbuf_data->ringbuf) {
        rbuf_delete(rbuf_data->ringbuf);
        rbuf_data->ringbuf = NULL;
    }
    if (rbuf_data->lock) {
        vSemaphoreDelete(rbuf_data->lock);
        rbuf_data->lock = NULL;
    }
}

void rtc_store_deinit(void)
{
     rtc_store_rbuf_deinit(&s_priv_data.critical);
     rtc_store_rbuf_deinit(&s_priv_data.non_critical);
     s_priv_data.init = false;
}

static esp_err_t rtc_store_rbuf_init(rbuf_data_t *rbuf_data,
                                     data_store_t *rtc_store,
                                     uint8_t *rtc_buf,
                                     size_t rtc_buf_size)
{
    uint8_t *tmp_buf = NULL;
    size_t a_part_len = 0, b_part_len = 0;
    esp_reset_reason_t reset_reason = esp_reset_reason();

    rbuf_data->lock = xSemaphoreCreateMutex();
    if (!rbuf_data->lock) {
        return ESP_ERR_NO_MEM;
    }

    /* Check for stale data */
    if (reset_reason == ESP_RST_UNKNOWN
        || reset_reason == ESP_RST_POWERON
        || reset_reason == ESP_RST_BROWNOUT) {
        memset(rtc_store, 0, sizeof(data_store_t));
        memset(rtc_buf, 0, rtc_buf_size);
    } else {
        if (rtc_store->len > 0 && rtc_store->len <= rtc_buf_size) {
            /* If malloc fails, memset RTC memory to zero */
            tmp_buf = malloc(rtc_store->len);
            if (tmp_buf) {
                if (rtc_store->read_offset + rtc_store->len > rtc_buf_size) {
                    /* Data is split in two parts */
                    a_part_len = rtc_buf_size - rtc_store->read_offset;
                    b_part_len = rtc_store->len - a_part_len;
                } else {
                    a_part_len = rtc_store->len;
                }
                memcpy(tmp_buf, rtc_buf + rtc_store->read_offset, a_part_len);
                memcpy(tmp_buf + a_part_len, rtc_buf, b_part_len);
            } else {
                memset(rtc_store, 0, sizeof(data_store_t));
                memset(rtc_buf, 0, rtc_buf_size);
            }
        } else {
            memset(rtc_store, 0, sizeof(data_store_t));
            memset(rtc_buf, 0, rtc_buf_size);
        }
    }

    /* Point priv_data to actual RTC data */
    rbuf_data->store = rtc_store;
    rbuf_data->store->buf = rtc_buf;
    rbuf_data->store->size = rtc_buf_size;

    rbuf_data->ringbuf = rbuf_create(rtc_buf_size, rbuf_data->store->buf);
    if (!rbuf_data->ringbuf) {
        vSemaphoreDelete(rbuf_data->lock);
        rbuf_data->lock = NULL;
        free(tmp_buf);
        tmp_buf = NULL;
        return ESP_ERR_NO_MEM;
    }
    if (tmp_buf) {
        rbuf_send(rbuf_data->ringbuf, tmp_buf, rbuf_data->store->len, 0);
        /* During init, length will be valid, just reset read_offset */
        rbuf_data->store->read_offset = 0;
        free(tmp_buf);
        tmp_buf = NULL;
    }
    return ESP_OK;
}

esp_err_t rtc_store_init(void)
{
    esp_err_t err;
    if (s_priv_data.init) {
        return ESP_ERR_INVALID_STATE;
    }
    /* Initialize critical RTC rbuf */
    err = rtc_store_rbuf_init(&s_priv_data.critical,
                              &s_rtc_store.critical.store,
                              s_rtc_store.critical.buf,
                              DIAG_CRITICAL_BUF_SIZE);
    if (err != ESP_OK) {
        return err;
    }
    /* Initialize non critical RTC rbuf */
    err = rtc_store_rbuf_init(&s_priv_data.non_critical,
                              &s_rtc_store.non_critical.store,
                              s_rtc_store.non_critical.buf,
                              DIAG_NON_CRITICAL_BUF_SIZE);
    if (err != ESP_OK) {
        rtc_store_rbuf_deinit(&s_priv_data.critical);
        return err;
    }
    s_priv_data.init = true;
    return ESP_OK;
}
