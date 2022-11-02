/**
 * @file
 * @version 0.1
 *
 * @copyright Copyright 2022 Chris Morgan <chmorgan@gmail.com>
 *
 *      Licensed under the Apache License, Version 2.0 (the "License");
 *      you may not use this file except in compliance with the License.
 *      You may obtain a copy of the License at
 *
 *               http://www.apache.org/licenses/LICENSE-2.0
 *
 *      Unless required by applicable law or agreed to in writing, software
 *      distributed under the License is distributed on an "AS IS" BASIS,
 *      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *      See the License for the specific language governing permissions and
 *      limitations under the License.
 */

#include <dirent.h>
#include <string.h>
#include "esp_check.h"
#include "esp_log.h"
#include "file_iterator.h"

static const char *TAG = "file_iterator";

/**
 * @brief Scans the given base_path, if any errors occur memory allocated and assigned
 * to instance entries is freed.
 */
static esp_err_t file_scan(file_iterator_instance_t *i, const char *base_path)
{
    i->count = 0;
    struct dirent *p_dirent = NULL;
    DIR *p_dir_stream = opendir(base_path);

    do {    /* Get total file count */
        p_dirent = readdir(p_dir_stream);
        if (NULL != p_dirent) {
            i->count++;
        } else {
            closedir(p_dir_stream);
            break;
        }
    } while (1);

    i->list = (char **) malloc(i->count * sizeof(char *));
    ESP_RETURN_ON_FALSE(NULL != i->list, ESP_ERR_NO_MEM,
        TAG, "Failed allocate audio list buffer");

    p_dir_stream = opendir(base_path);
    for (size_t file_index = 0; file_index < i->count; file_index++) {
        p_dirent = readdir(p_dir_stream);
        if (NULL != p_dirent) {
            i->list[file_index] = malloc(sizeof(p_dirent->d_name));
            ESP_LOGI(TAG, "File : %s", strcpy(i->list[file_index], p_dirent->d_name));
        } else {
            ESP_LOGE(TAG, "The file system may be corrupted");
            closedir(p_dir_stream);
            for (int j = file_index - 1; j >= 0; j--) {
                free(i->list[file_index]);
            }
            free(i->list);
            return ESP_ERR_INVALID_STATE;
        }
    }

    closedir(p_dir_stream);
    return ESP_OK;
}

size_t file_iterator_get_count(file_iterator_instance_t *i) {
    return i->count;
}

size_t file_iterator_get_index(file_iterator_instance_t *i)
{
    ESP_LOGI(TAG, "file_iterator_get_index() %d", i->index);
    return i->index;
}

void file_iterator_set_index(file_iterator_instance_t *i, size_t index)
{
    ESP_LOGI(TAG, "file_iterator_set_index() %d", index);

    if(index >= i->count) {
        index = 0;
    }

    i->index = index;
}

const char* file_iterator_get_name_from_index(file_iterator_instance_t *i, size_t index)
{
    ESP_RETURN_ON_FALSE(index < i->count, NULL,
        TAG, "File index out of range");

    ESP_RETURN_ON_FALSE(NULL != i->list, NULL,
        TAG, "File not found");

    ESP_RETURN_ON_FALSE(NULL != i->list[index], NULL,
        TAG, "File not found");

    return i->list[index];
}

int file_iterator_get_full_path_from_index(file_iterator_instance_t* i, size_t index, char* path, size_t path_len)
{
    const char* name = file_iterator_get_name_from_index(i, index);
    if(!name) {
        return 0;
    }

    int retval = snprintf(path, path_len, "%s/%s", i->directory_path, name);

    return retval;
}

esp_err_t file_iterator_next(file_iterator_instance_t *i)
{
    i->index++;
    if (i->index >= i->count) {
        i->index = 0;
    }
    return ESP_OK;
}

esp_err_t file_iterator_prev(file_iterator_instance_t *i)
{
    if (i->index == 0) {
        i->index = i->count;
    }
    i->index--;
    return ESP_OK;
}

file_iterator_instance_t* file_iterator_new(const char *base_path)
{
    file_iterator_instance_t *i = NULL;
    esp_err_t ret;

    /* Scan audio file */
    if (NULL != base_path) {
        i = malloc(sizeof(file_iterator_instance_t));
        i->index = 0;
        ret = file_scan(i, base_path);
        if(ret == ESP_OK) {
            i->directory_path = strdup(base_path);
        } else {
            free(i);
            i = NULL;
        }
    } else {
        ESP_LOGE(TAG, "Invalid base path");
    }

    return i;
}
