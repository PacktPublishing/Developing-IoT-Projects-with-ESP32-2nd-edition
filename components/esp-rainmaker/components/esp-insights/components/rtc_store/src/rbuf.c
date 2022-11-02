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

/*
 * Following code is copied from the esp_ringbuf component in order to save 3K RAM
 */

#include <stdlib.h>
#include <string.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"

#include "rbuf.h"

//Ring buffer flags
#define rbALLOW_SPLIT_FLAG          ( ( UBaseType_t ) 1 )   //The ring buffer allows items to be split
#define rbBYTE_BUFFER_FLAG           ( ( UBaseType_t ) 2 )   //The ring buffer is a byte buffer
#define rbBUFFER_FULL_FLAG           ( ( UBaseType_t ) 4 )   //The ring buffer is currently full (write pointer == free pointer)
#define rbBUFFER_STATIC_STORAGE_FLAG ( ( UBaseType_t ) 16 )  //The ring buffer is using static storage provided by user and other things are allocated dynamically

#define rbGET_TX_SEM_HANDLE( pxRingbuffer ) ( pxRingbuffer->xTransSemHandle )
#define rbGET_RX_SEM_HANDLE( pxRingbuffer ) ( pxRingbuffer->xRecvSemHandle )

typedef struct RingbufferDefinition Ringbuffer_t;

typedef BaseType_t (*CheckItemFitsFunction_t)(Ringbuffer_t *pxRingbuffer, size_t xItemSize);
typedef void (*CopyItemFunction_t)(Ringbuffer_t *pxRingbuffer, const uint8_t *pcItem, size_t xItemSize);
typedef void *(*GetItemFunction_t)(Ringbuffer_t *pxRingbuffer, BaseType_t *pxIsSplit, size_t xMaxSize, size_t *pxItemSize);
typedef void (*ReturnItemFunction_t)(Ringbuffer_t *pxRingbuffer, uint8_t *pvItem);
typedef size_t (*GetCurMaxSizeFunction_t)(Ringbuffer_t *pxRingbuffer);

typedef struct RingbufferDefinition {
    size_t xSize;                               //Size of the data storage
    size_t xMaxItemSize;                        //Maximum item size
    UBaseType_t uxRingbufferFlags;              //Flags to indicate the type and status of ring buffer

    CheckItemFitsFunction_t xCheckItemFits;     //Function to check if item can currently fit in ring buffer
    CopyItemFunction_t vCopyItem;               //Function to copy item to ring buffer
    GetItemFunction_t pvGetItem;                //Function to get item from ring buffer
    ReturnItemFunction_t vReturnItem;           //Function to return item to ring buffer
    GetCurMaxSizeFunction_t xGetCurMaxSize;     //Function to get current free size

    uint8_t *pucAcquire;                        //Acquire Pointer. Points to where the next item should be acquired.
    uint8_t *pucWrite;                          //Write Pointer. Points to where the next item should be written
    uint8_t *pucRead;                           //Read Pointer. Points to where the next item should be read from
    uint8_t *pucFree;                           //Free Pointer. Points to the last item that has yet to be returned to the ring buffer
    uint8_t *pucHead;                           //Pointer to the start of the ring buffer storage area
    uint8_t *pucTail;                           //Pointer to the end of the ring buffer storage area

    BaseType_t xItemsWaiting;                   //Number of items/bytes(for byte buffers) currently in ring buffer that have not yet been read
    /*
     * TransSem: Binary semaphore used to indicate to a blocked transmitting tasks
     *           that more free space has become available or that the block has
     *           timed out.
     *
     * RecvSem: Binary semaphore used to indicate to a blocked receiving task that
     *          new data/item has been written to the ring buffer.
     */
    SemaphoreHandle_t xTransSemHandle;
    SemaphoreHandle_t xRecvSemHandle;
    portMUX_TYPE mux;                           //Spinlock required for SMP
} Ringbuffer_t;

/* --------------------------- Static Definitions --------------------------- */

static BaseType_t prvCheckItemFitsByteBuffer( Ringbuffer_t *pxRingbuffer, size_t xItemSize)
{
    //Check arguments and buffer state
    configASSERT(pxRingbuffer->pucAcquire >= pxRingbuffer->pucHead && pxRingbuffer->pucAcquire < pxRingbuffer->pucTail);    //Check acquire pointer is within bounds

    if (pxRingbuffer->pucAcquire == pxRingbuffer->pucFree) {
        //Buffer is either complete empty or completely full
        return (pxRingbuffer->uxRingbufferFlags & rbBUFFER_FULL_FLAG) ? pdFALSE : pdTRUE;
    }
    if (pxRingbuffer->pucFree > pxRingbuffer->pucAcquire) {
        //Free space does not wrap around
        return (xItemSize <= pxRingbuffer->pucFree - pxRingbuffer->pucAcquire) ? pdTRUE : pdFALSE;
    }
    //Free space wraps around
    return (xItemSize <= pxRingbuffer->xSize - (pxRingbuffer->pucAcquire - pxRingbuffer->pucFree)) ? pdTRUE : pdFALSE;
}

static void prvCopyItemByteBuf(Ringbuffer_t *pxRingbuffer, const uint8_t *pucItem, size_t xItemSize)
{
    //Check arguments and buffer state
    configASSERT(pxRingbuffer->pucAcquire >= pxRingbuffer->pucHead && pxRingbuffer->pucAcquire < pxRingbuffer->pucTail);    //Check acquire pointer is within bounds

    size_t xRemLen = pxRingbuffer->pucTail - pxRingbuffer->pucAcquire;    //Length from pucAcquire until end of buffer
    if (xRemLen < xItemSize) {
        //Copy as much as possible into remaining length
        memcpy(pxRingbuffer->pucAcquire, pucItem, xRemLen);
        pxRingbuffer->xItemsWaiting += xRemLen;
        //Update item arguments to account for data already written
        pucItem += xRemLen;
        xItemSize -= xRemLen;
        pxRingbuffer->pucAcquire = pxRingbuffer->pucHead;     //Reset acquire pointer to start of buffer
    }
    //Copy all or remaining portion of the item
    memcpy(pxRingbuffer->pucAcquire, pucItem, xItemSize);
    pxRingbuffer->xItemsWaiting += xItemSize;
    pxRingbuffer->pucAcquire += xItemSize;

    //Wrap around pucAcquire if it reaches the end
    if (pxRingbuffer->pucAcquire == pxRingbuffer->pucTail) {
        pxRingbuffer->pucAcquire = pxRingbuffer->pucHead;
    }
    //Check if buffer is full
    if (pxRingbuffer->pucAcquire == pxRingbuffer->pucFree) {
        pxRingbuffer->uxRingbufferFlags |= rbBUFFER_FULL_FLAG;      //Mark the buffer as full to avoid confusion with an empty buffer
    }

    //Currently, acquiring memory is not supported in byte mode. pucWrite tracks the pucAcquire.
    pxRingbuffer->pucWrite = pxRingbuffer->pucAcquire;
}

static void *prvGetItemByteBuf(Ringbuffer_t *pxRingbuffer,
                               BaseType_t *pxUnusedParam,
                               size_t xMaxSize,
                               size_t *pxItemSize)
{
    //Check arguments and buffer state
    configASSERT((pxRingbuffer->xItemsWaiting > 0) && ((pxRingbuffer->pucRead != pxRingbuffer->pucWrite) || (pxRingbuffer->uxRingbufferFlags & rbBUFFER_FULL_FLAG)));   //Check there are items to be read
    configASSERT(pxRingbuffer->pucRead >= pxRingbuffer->pucHead && pxRingbuffer->pucRead < pxRingbuffer->pucTail);    //Check read pointer is within bounds
    configASSERT(pxRingbuffer->pucRead == pxRingbuffer->pucFree);

    uint8_t *ret = pxRingbuffer->pucRead;
    if ((pxRingbuffer->pucRead > pxRingbuffer->pucWrite) || (pxRingbuffer->uxRingbufferFlags & rbBUFFER_FULL_FLAG)) {     //Available data wraps around
        //Return contiguous piece from read pointer until buffer tail, or xMaxSize
        if (xMaxSize == 0 || pxRingbuffer->pucTail - pxRingbuffer->pucRead <= xMaxSize) {
            //All contiguous data from read pointer to tail
            *pxItemSize = pxRingbuffer->pucTail - pxRingbuffer->pucRead;
            pxRingbuffer->xItemsWaiting -= pxRingbuffer->pucTail - pxRingbuffer->pucRead;
            pxRingbuffer->pucRead = pxRingbuffer->pucHead;  //Wrap around read pointer
        } else {
            //Return xMaxSize amount of data
            *pxItemSize = xMaxSize;
            pxRingbuffer->xItemsWaiting -= xMaxSize;
            pxRingbuffer->pucRead += xMaxSize;  //Advance read pointer past retrieved data
        }
    } else {    //Available data is contiguous between read and write pointer
        if (xMaxSize == 0 || pxRingbuffer->pucWrite - pxRingbuffer->pucRead <= xMaxSize) {
            //Return all contiguous data from read to write pointer
            *pxItemSize = pxRingbuffer->pucWrite - pxRingbuffer->pucRead;
            pxRingbuffer->xItemsWaiting -= pxRingbuffer->pucWrite - pxRingbuffer->pucRead;
            pxRingbuffer->pucRead = pxRingbuffer->pucWrite;
        } else {
            //Return xMaxSize data from read pointer
            *pxItemSize = xMaxSize;
            pxRingbuffer->xItemsWaiting -= xMaxSize;
            pxRingbuffer->pucRead += xMaxSize;  //Advance read pointer past retrieved data

        }
    }
    return (void *)ret;
}

static void prvReturnItemByteBuf(Ringbuffer_t *pxRingbuffer, uint8_t *pucItem)
{
    //Check pointer points to address inside buffer
    configASSERT((uint8_t *)pucItem >= pxRingbuffer->pucHead);
    configASSERT((uint8_t *)pucItem < pxRingbuffer->pucTail);
    //Free the read memory. Simply moves free pointer to read pointer as byte buffers do not allow multiple outstanding reads
    pxRingbuffer->pucFree = pxRingbuffer->pucRead;
    //If buffer was full before, reset full flag as free pointer has moved
    if (pxRingbuffer->uxRingbufferFlags & rbBUFFER_FULL_FLAG) {
        pxRingbuffer->uxRingbufferFlags &= ~rbBUFFER_FULL_FLAG;
    }
}

static size_t prvGetCurMaxSizeByteBuf(Ringbuffer_t *pxRingbuffer)
{
    BaseType_t xFreeSize;
    //Check if buffer is full
    if (pxRingbuffer->uxRingbufferFlags & rbBUFFER_FULL_FLAG) {
        return 0;
    }

    /*
     * Return whatever space is available depending on relative positions of the free
     * pointer and Acquire pointer. There is no overhead of headers in this mode
     */
    xFreeSize = pxRingbuffer->pucFree - pxRingbuffer->pucAcquire;
    if (xFreeSize <= 0) {
        xFreeSize += pxRingbuffer->xSize;
    }
    return xFreeSize;
}

static void prvInitializeNewRingbuffer(size_t xBufferSize,
                                       Ringbuffer_t *pxNewRingbuffer,
                                       uint8_t *pucRingbufferStorage)
{
    //Initialize values
    pxNewRingbuffer->xSize = xBufferSize;
    pxNewRingbuffer->pucHead = pucRingbufferStorage;
    pxNewRingbuffer->pucTail = pucRingbufferStorage + xBufferSize;
    pxNewRingbuffer->pucFree = pucRingbufferStorage;
    pxNewRingbuffer->pucRead = pucRingbufferStorage;
    pxNewRingbuffer->pucWrite = pucRingbufferStorage;
    pxNewRingbuffer->pucAcquire = pucRingbufferStorage;
    pxNewRingbuffer->xItemsWaiting = 0;
    pxNewRingbuffer->uxRingbufferFlags = 0;

    //Byte Buffer
    pxNewRingbuffer->uxRingbufferFlags |= rbBYTE_BUFFER_FLAG;
    pxNewRingbuffer->xCheckItemFits = prvCheckItemFitsByteBuffer;
    pxNewRingbuffer->vCopyItem = prvCopyItemByteBuf;
    pxNewRingbuffer->pvGetItem = prvGetItemByteBuf;
    pxNewRingbuffer->vReturnItem = prvReturnItemByteBuf;
    //Byte buffers do not incur any overhead
    pxNewRingbuffer->xMaxItemSize = pxNewRingbuffer->xSize;
    pxNewRingbuffer->xGetCurMaxSize = prvGetCurMaxSizeByteBuf;

    xSemaphoreGive(rbGET_TX_SEM_HANDLE(pxNewRingbuffer));
    vPortCPUInitializeMutex(&pxNewRingbuffer->mux);
}

static size_t prvGetFreeSize(Ringbuffer_t *pxRingbuffer)
{
    size_t xReturn;
    if (pxRingbuffer->uxRingbufferFlags & rbBUFFER_FULL_FLAG) {
        xReturn =  0;
    } else {
        BaseType_t xFreeSize = pxRingbuffer->pucFree - pxRingbuffer->pucAcquire;
        //Check if xFreeSize has underflowed
        if (xFreeSize <= 0) {
            xFreeSize += pxRingbuffer->xSize;
        }
        xReturn = xFreeSize;
    }
    configASSERT(xReturn <= pxRingbuffer->xSize);
    return xReturn;
}

static BaseType_t prvCheckItemAvail(Ringbuffer_t *pxRingbuffer)
{
    if ((pxRingbuffer->uxRingbufferFlags & rbBYTE_BUFFER_FLAG) && pxRingbuffer->pucRead != pxRingbuffer->pucFree) {
        return pdFALSE;     //Byte buffers do not allow multiple retrievals before return
    }
    if ((pxRingbuffer->xItemsWaiting > 0) && ((pxRingbuffer->pucRead != pxRingbuffer->pucWrite) || (pxRingbuffer->uxRingbufferFlags & rbBUFFER_FULL_FLAG))) {
        return pdTRUE;      //Items/data available for retrieval
    } else {
        return pdFALSE;     //No items/data available for retrieval
    }
}

static BaseType_t prvReceiveGeneric(Ringbuffer_t *pxRingbuffer,
                                    void **pvItem1,
                                    void **pvItem2,
                                    size_t *xItemSize1,
                                    size_t *xItemSize2,
                                    size_t xMaxSize,
                                    TickType_t xTicksToWait)
{
    BaseType_t xReturn = pdFALSE;
    BaseType_t xReturnSemaphore = pdFALSE;
    TickType_t xTicksEnd = xTaskGetTickCount() + xTicksToWait;
    TickType_t xTicksRemaining = xTicksToWait;
    while (xTicksRemaining <= xTicksToWait) {   //xTicksToWait will underflow once xTaskGetTickCount() > ticks_end
        //Block until more free space becomes available or timeout
        if (xSemaphoreTake(rbGET_RX_SEM_HANDLE(pxRingbuffer), xTicksRemaining) != pdTRUE) {
            xReturn = pdFALSE;     //Timed out attempting to get semaphore
            break;
        }

        //Semaphore obtained, check if item can be retrieved
        portENTER_CRITICAL(&pxRingbuffer->mux);
        if (prvCheckItemAvail(pxRingbuffer) == pdTRUE) {
            //Item is available for retrieval
            BaseType_t xIsSplit;
            if (pxRingbuffer->uxRingbufferFlags & rbBYTE_BUFFER_FLAG) {
                //Second argument (pxIsSplit) is unused for byte buffers
                *pvItem1 = pxRingbuffer->pvGetItem(pxRingbuffer, NULL, xMaxSize, xItemSize1);
            } else {
                //Third argument (xMaxSize) is unused for no-split/allow-split buffers
                *pvItem1 = pxRingbuffer->pvGetItem(pxRingbuffer, &xIsSplit, 0, xItemSize1);
            }
            //Check for item split if configured to do so
            if ((pxRingbuffer->uxRingbufferFlags & rbALLOW_SPLIT_FLAG) && (pvItem2 != NULL) && (xItemSize2 != NULL)) {
                if (xIsSplit == pdTRUE) {
                    *pvItem2 = pxRingbuffer->pvGetItem(pxRingbuffer, &xIsSplit, 0, xItemSize2);
                    configASSERT(*pvItem2 < *pvItem1);  //Check wrap around has occurred
                    configASSERT(xIsSplit == pdFALSE);  //Second part should not have wrapped flag
                } else {
                    *pvItem2 = NULL;
                }
            }
            xReturn = pdTRUE;
            if (pxRingbuffer->xItemsWaiting > 0) {
                xReturnSemaphore = pdTRUE;
            }
            portEXIT_CRITICAL(&pxRingbuffer->mux);
            break;
        }
        //No item available for retrieval, adjust ticks and take the semaphore again
        if (xTicksToWait != portMAX_DELAY) {
            xTicksRemaining = xTicksEnd - xTaskGetTickCount();
        }
        portEXIT_CRITICAL(&pxRingbuffer->mux);
        /*
         * Gap between critical section and re-acquiring of the semaphore. If
         * semaphore is given now, priority inversion might occur (see docs)
         */
    }

    if (xReturnSemaphore == pdTRUE) {
        xSemaphoreGive(rbGET_RX_SEM_HANDLE(pxRingbuffer));  //Give semaphore back so other tasks can retrieve
    }
    return xReturn;
}

/* --------------------------- Public Definitions --------------------------- */

rbuf_handle_t rbuf_create(size_t xBufferSize, uint8_t *pucRingbufferStorage)
{
    configASSERT(xBufferSize > 0);
    configASSERT(pucRingbufferStorage != NULL);

    //Allocate memory
    Ringbuffer_t *pxNewRingbuffer = calloc(1, sizeof(Ringbuffer_t));
    if (pxNewRingbuffer == NULL) {
        return NULL;
    }

    //Initialize Semaphores
    pxNewRingbuffer->xTransSemHandle = xSemaphoreCreateBinary();
    pxNewRingbuffer->xRecvSemHandle = xSemaphoreCreateBinary();
    if (pxNewRingbuffer->xTransSemHandle == NULL || pxNewRingbuffer->xRecvSemHandle == NULL) {
        if (pxNewRingbuffer->xTransSemHandle != NULL) {
            vSemaphoreDelete(pxNewRingbuffer->xTransSemHandle);
        }
        if (pxNewRingbuffer->xRecvSemHandle != NULL) {
            vSemaphoreDelete(pxNewRingbuffer->xRecvSemHandle);
        }
        goto err;
    }

    prvInitializeNewRingbuffer(xBufferSize, pxNewRingbuffer, pucRingbufferStorage);
    pxNewRingbuffer->uxRingbufferFlags |= rbBUFFER_STATIC_STORAGE_FLAG;
    return (rbuf_handle_t)pxNewRingbuffer;

err:
    //An error has occurred, Free memory and return NULL
    free(pxNewRingbuffer);
    return NULL;

}

BaseType_t rbuf_send(rbuf_handle_t xRingbuffer,
                     const void *pvItem,
                     size_t xItemSize,
                     TickType_t xTicksToWait)
{
    //Check arguments
    Ringbuffer_t *pxRingbuffer = (Ringbuffer_t *)xRingbuffer;
    configASSERT(pxRingbuffer);
    configASSERT(pvItem != NULL || xItemSize == 0);
    if (xItemSize > pxRingbuffer->xMaxItemSize) {
        return pdFALSE;     //Data will never ever fit in the queue.
    }
    if ((pxRingbuffer->uxRingbufferFlags & rbBYTE_BUFFER_FLAG) && xItemSize == 0) {
        return pdTRUE;      //Sending 0 bytes to byte buffer has no effect
    }

    //Attempt to send an item
    BaseType_t xReturn = pdFALSE;
    BaseType_t xReturnSemaphore = pdFALSE;
    TickType_t xTicksEnd = xTaskGetTickCount() + xTicksToWait;
    TickType_t xTicksRemaining = xTicksToWait;
    while (xTicksRemaining <= xTicksToWait) {   //xTicksToWait will underflow once xTaskGetTickCount() > ticks_end
        //Block until more free space becomes available or timeout
        if (xSemaphoreTake(rbGET_TX_SEM_HANDLE(pxRingbuffer), xTicksRemaining) != pdTRUE) {
            xReturn = pdFALSE;
            break;
        }
        //Semaphore obtained, check if item can fit
        portENTER_CRITICAL(&pxRingbuffer->mux);
        if(pxRingbuffer->xCheckItemFits(pxRingbuffer, xItemSize) == pdTRUE) {
            //Item will fit, copy item
            pxRingbuffer->vCopyItem(pxRingbuffer, pvItem, xItemSize);
            xReturn = pdTRUE;
            //Check if the free semaphore should be returned to allow other tasks to send
            if (prvGetFreeSize(pxRingbuffer) > 0) {
                xReturnSemaphore = pdTRUE;
            }
            portEXIT_CRITICAL(&pxRingbuffer->mux);
            break;
        }
        //Item doesn't fit, adjust ticks and take the semaphore again
        if (xTicksToWait != portMAX_DELAY) {
            xTicksRemaining = xTicksEnd - xTaskGetTickCount();
        }
        portEXIT_CRITICAL(&pxRingbuffer->mux);
        /*
         * Gap between critical section and re-acquiring of the semaphore. If
         * semaphore is given now, priority inversion might occur (see docs)
         */
    }

    if (xReturn == pdTRUE) {
        //Indicate item was successfully sent
        xSemaphoreGive(rbGET_RX_SEM_HANDLE(pxRingbuffer));
    }
    if (xReturnSemaphore == pdTRUE) {
        xSemaphoreGive(rbGET_TX_SEM_HANDLE(pxRingbuffer));  //Give back semaphore so other tasks can send
    }
    return xReturn;
}

void *rbuf_receive(rbuf_handle_t xRingbuffer, size_t *pxItemSize, TickType_t xTicksToWait)
{
    //Check arguments
    Ringbuffer_t *pxRingbuffer = (Ringbuffer_t *)xRingbuffer;
    configASSERT(pxRingbuffer);

    //Attempt to retrieve an item
    void *pvTempItem;
    size_t xTempSize;
    if (prvReceiveGeneric(pxRingbuffer, &pvTempItem, NULL, &xTempSize, NULL, 0, xTicksToWait) == pdTRUE) {
        if (pxItemSize != NULL) {
            *pxItemSize = xTempSize;
        }
        return pvTempItem;
    } else {
        return NULL;
    }
}

void *rbuf_receive_upto(rbuf_handle_t xRingbuffer,
                        size_t *pxItemSize,
                        TickType_t xTicksToWait,
                        size_t xMaxSize)
{
    //Check arguments
    Ringbuffer_t *pxRingbuffer = (Ringbuffer_t *)xRingbuffer;
    configASSERT(pxRingbuffer);
    configASSERT(pxRingbuffer->uxRingbufferFlags & rbBYTE_BUFFER_FLAG);    //This function should only be called for byte buffers
    if (xMaxSize == 0) {
        return NULL;
    }

    //Attempt to retrieve up to xMaxSize bytes
    void *pvTempItem;
    size_t xTempSize;
    if (prvReceiveGeneric(pxRingbuffer, &pvTempItem, NULL, &xTempSize, NULL, xMaxSize, xTicksToWait) == pdTRUE) {
        if (pxItemSize != NULL) {
            *pxItemSize = xTempSize;
        }
        return pvTempItem;
    } else {
        return NULL;
    }
}

void rbuf_return_item(rbuf_handle_t xRingbuffer, void *pvItem)
{
    Ringbuffer_t *pxRingbuffer = (Ringbuffer_t *)xRingbuffer;
    configASSERT(pxRingbuffer);
    configASSERT(pvItem != NULL);

    portENTER_CRITICAL(&pxRingbuffer->mux);
    pxRingbuffer->vReturnItem(pxRingbuffer, (uint8_t *)pvItem);
    portEXIT_CRITICAL(&pxRingbuffer->mux);
    xSemaphoreGive(rbGET_TX_SEM_HANDLE(pxRingbuffer));
}

void rbuf_delete(rbuf_handle_t xRingbuffer)
{
    Ringbuffer_t *pxRingbuffer = (Ringbuffer_t *)xRingbuffer;
    configASSERT(pxRingbuffer);

    vSemaphoreDelete(rbGET_TX_SEM_HANDLE(pxRingbuffer));
    vSemaphoreDelete(rbGET_RX_SEM_HANDLE(pxRingbuffer));

    if (!(pxRingbuffer->uxRingbufferFlags & rbBUFFER_STATIC_STORAGE_FLAG)) {
        free(pxRingbuffer->pucHead);
    }
    free(pxRingbuffer);
}

size_t rbuf_get_cur_free_size(rbuf_handle_t xRingbuffer)
{
    Ringbuffer_t *pxRingbuffer = (Ringbuffer_t *)xRingbuffer;
    configASSERT(pxRingbuffer);

    size_t xFreeSize;
    portENTER_CRITICAL(&pxRingbuffer->mux);
    xFreeSize = pxRingbuffer->xGetCurMaxSize(pxRingbuffer);
    portEXIT_CRITICAL(&pxRingbuffer->mux);
    return xFreeSize;
}

void rbuf_get_info(rbuf_handle_t xRingbuffer,
                   UBaseType_t *uxFree,
                   UBaseType_t *uxRead,
                   UBaseType_t *uxWrite,
                   UBaseType_t *uxAcquire,
                   UBaseType_t *uxItemsWaiting)
{
    Ringbuffer_t *pxRingbuffer = (Ringbuffer_t *)xRingbuffer;
    configASSERT(pxRingbuffer);

    portENTER_CRITICAL(&pxRingbuffer->mux);
    if (uxFree != NULL) {
        *uxFree = (UBaseType_t)(pxRingbuffer->pucFree - pxRingbuffer->pucHead);
    }
    if (uxRead != NULL) {
        *uxRead = (UBaseType_t)(pxRingbuffer->pucRead - pxRingbuffer->pucHead);
    }
    if (uxWrite != NULL) {
        *uxWrite = (UBaseType_t)(pxRingbuffer->pucWrite - pxRingbuffer->pucHead);
    }
    if (uxAcquire != NULL) {
        *uxAcquire = (UBaseType_t)(pxRingbuffer->pucAcquire - pxRingbuffer->pucHead);
    }
    if (uxItemsWaiting != NULL) {
        *uxItemsWaiting = (UBaseType_t)(pxRingbuffer->xItemsWaiting);
    }
    portEXIT_CRITICAL(&pxRingbuffer->mux);
}
