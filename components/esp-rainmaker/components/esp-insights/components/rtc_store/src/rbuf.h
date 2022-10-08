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
#pragma once
#include "freertos/FreeRTOS.h"

/* Type by which ring buffers are referenced. */
typedef void * rbuf_handle_t;

/* Creates a ring buffer of type bytebuf with user provided storage */
rbuf_handle_t rbuf_create(size_t xBufferSize, uint8_t *pucRingbufferStorage);

/* Attempt to insert an item into the ring buffer */
BaseType_t rbuf_send(rbuf_handle_t xRingbuffer,
                     const void *pvItem,
                     size_t xItemSize,
                     TickType_t xTicksToWait);

/* Retrieve an data from the ring buffer */
void *rbuf_receive(rbuf_handle_t xRingbuffer, size_t *pxItemSize, TickType_t xTicksToWait);

/* Retrieve bytes from a byte buffer, specifying the maximum amount of bytes to retrieve */
void *rbuf_receive_upto(rbuf_handle_t xRingbuffer,
                        size_t *pxItemSize,
                        TickType_t xTicksToWait,
                        size_t xMaxSize);

/* Return a previously-retrieved item to the ring buffer */
void rbuf_return_item(rbuf_handle_t xRingbuffer, void *pvItem);

/* Deletes a ring buffer */
void rbuf_delete(rbuf_handle_t xRingbuffer);

/* Get current free size available for an item/data in the buffer */
size_t rbuf_get_cur_free_size(rbuf_handle_t xRingbuffer);

/* Get information about ring buffer status */
void rbuf_get_info(rbuf_handle_t xRingbuffer,
                   UBaseType_t *uxFree,
                   UBaseType_t *uxRead,
                   UBaseType_t *uxWrite,
                   UBaseType_t *uxAcquire,
                   UBaseType_t *uxItemsWaiting);
