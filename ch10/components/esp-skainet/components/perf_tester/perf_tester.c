#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/dirent.h>
#include "assert.h"
#include "wav_decoder.h"
#include "esp_skainet_player.h"
#include "perf_tester.h"
#include "esp_board_init.h"
#include "esp_mn_speech_commands.h"
#include "esp_process_sdkconfig.h"


typedef struct {
    int rb_buffer_size;
    int frame_size;
    char **file_list;
    char *log_file;
    char *csv_file;
    int *csv_col2;            // the second csv column, may be command id or trigger times of wake word
    int *csv_col3;            // the third csv column, may be command id or trigger times of wake word
    int file_num;
    int max_file_num;
    int file_id;
    int nch;
    int *file_det_times;
    int *mn_det_times;
    int sample_rate;
    int64_t wave_time;
    int tester_mem_size;        //total memory for tester, include PSRAM and SRAM
    int tester_sram_size;       //internal SRAM size for tester

    //void *afe_handle;
    esp_afe_sr_iface_t *afe_handle;
    esp_afe_sr_data_t *afe_data;
    int64_t running_time;
    int afe_mem_size;            //total memory for afe, include PSRAM and SRAM
    int afe_sram_size;           //internal SRAM size for afe module
    int enable_afe_out;

    //multinet
    esp_mn_iface_t *multinet;
    model_iface_data_t *mn_data;
    int mn_frame_size;
    int64_t mn_running_time;
    int mn_running;
    int *command_no_trigger;
    int *command_false_trigger;
    int *command_right;
    tester_audio_t audio_type;
    int test_done;

} skainet_perf_tester;

int sdcard_scan(void *handle, const char *path, int audio_type)
{
    skainet_perf_tester *tester = handle;
    struct dirent *ret;
    DIR *dir;
    dir = opendir(path);
    int path_len = strlen(path);
    printf("Search files in %s\n", path);
    if (dir != NULL) {

        while ((ret = readdir(dir)) != NULL && tester->file_num < tester->max_file_num) {
            // NULL if reach the end of directory

            if (ret->d_type != 1) { // continue if d_type is not file
                continue;
            }

            int len = strlen(ret->d_name);
            if (len > FATFS_PATH_LENGTH_MAX - path_len - 1) { // continue if name is too long
                continue;
            }

            char *suffix = ret->d_name + len - 4;

            if (audio_type == TESTER_PCM_1CH || audio_type == TESTER_PCM_3CH) {
                if (strcmp(suffix, ".pcm") == 0 || strcmp(suffix, ".PCM") == 0) {
                    memset(tester->file_list[tester->file_num], 0, FATFS_PATH_LENGTH_MAX);
                    memcpy(tester->file_list[tester->file_num], path, path_len);
                    memcpy(tester->file_list[tester->file_num] + path_len, ret->d_name, len + 1);
                    printf("%d -> %s\n", tester->file_num, tester->file_list[tester->file_num]);
                    tester->file_num++;
                }
            } else if (audio_type == TESTER_WAV_1CH || audio_type == TESTER_WAV_3CH) {
                if (strcmp(suffix, ".wav") == 0 || strcmp(suffix, ".WAV") == 0) {
                    memset(tester->file_list[tester->file_num], 0, FATFS_PATH_LENGTH_MAX);
                    memcpy(tester->file_list[tester->file_num], path, path_len);
                    memcpy(tester->file_list[tester->file_num] + path_len, ret->d_name, len + 1);
                    printf("%d -> %s\n", tester->file_num, tester->file_list[tester->file_num]);
                    tester->file_num++;
                }
            }

        }
        closedir(dir);
        printf("Number of files: %d\n", tester->file_num);
    } else {
        printf("Fail to open %s\r\n", path);
    }
    return tester->file_num;
}

long get_file_size(FILE *fp)
{
    fseek(fp, 0L, SEEK_END);
    long size = ftell(fp);
    fseek(fp, 0L, SEEK_SET);

    return size;
}

int read_csv_file(skainet_perf_tester *tester)
{
    FILE *fp = fopen(tester->csv_file, "r");
    tester->file_num = 0;
    if (fp == NULL) {
        return tester->file_num;
    }
    char csv_line[512];
    char *token = NULL;
    fgets(csv_line, 512, fp);  //skip csv header
    while (fgets(csv_line, 512, fp) != NULL && tester->file_num < tester->max_file_num) {
        token = strtok(csv_line, ",");
        memset(tester->file_list[tester->file_num], 0, FATFS_PATH_LENGTH_MAX);
        memcpy(tester->file_list[tester->file_num], token, strlen(token));
        token = strtok(NULL, ",");
        if (token != NULL) {
            tester->csv_col2[tester->file_num] = atoi(token);
        } else {
            tester->csv_col2[tester->file_num] = 0;
        }

        token = strtok(NULL, ",");
        if (token != NULL) {
            tester->csv_col3[tester->file_num] = atoi(token);
        } else {
            tester->csv_col3[tester->file_num] = 0;
        }

        tester->file_num ++;
    }
    printf("Number of files: %d\n", tester->file_num);
    return tester->file_num;
}

void print_wn_report(skainet_perf_tester *tester)
{
    assert(tester != NULL);
    tester->tester_mem_size -= heap_caps_get_free_size(MALLOC_CAP_8BIT);
    tester->tester_sram_size -= heap_caps_get_free_size(MALLOC_CAP_INTERNAL);

    float wave_time = tester->wave_time / tester->sample_rate;
    printf("Tester PSRAM: %d KB\n", (tester->tester_mem_size - tester->tester_sram_size) / 1024);
    printf("Tester SRAM: %d KB\n", tester->tester_sram_size / 1024);

    if (tester->afe_handle != NULL) {
        float running_time = tester->running_time * 1.0 / 240 / 1000 / 1000;
        printf("FAR CPU: %d%%\n", (int)(100 * running_time / wave_time));
        printf("FAR PSRAM: %d KB\n", (tester->afe_mem_size - tester->afe_sram_size) / 1024);
        printf("FAR SRAM: %d KB\n", tester->afe_sram_size / 1024);
    } else {
        printf("Disable FAR Pipeline\n\n");
    }

    if (tester->file_num > 0) {
        int count = 0;
        int require_count = 0;
        int gt_count = 0;
        for (int i = 0; i < tester->file_num; i++) {
            printf("File%d: %s\n", i, tester->file_list[i]);
            printf("File%d, trigger times: %d\n", i, tester->file_det_times[i]);
            printf("File%d, required times: %d\n", i, tester->csv_col2[i]);
            printf("File%d, truth times: %d\n", i, tester->csv_col3[i]);
            count += tester->file_det_times[i];
            require_count += tester->csv_col2[i];
            gt_count += tester->csv_col3[i];
        }
        printf("Total trigger times: %d\n", count);
        printf("Total required times: %d\n", require_count);
        printf("Total truth times: %d\n", gt_count);
    }

    printf("TEST DONE\n");
}

void wav_feed_task(void *arg)
{
    printf("Create wav feed task ...\n");
    skainet_perf_tester *tester = arg;
    esp_afe_sr_iface_t *afe_handle = tester->afe_handle;
    esp_afe_sr_data_t *afe_data = tester->afe_data;
    void *wav_decoder = NULL;
    // printf("create speech enhancement task\n");
    int sample_rate = tester->sample_rate;
    int frame_size = tester->frame_size;
    int nch = tester->nch;
    int file_nch = 0;

    int i2s_buffer_size = frame_size * (nch + 1) * sizeof(int16_t);

    int16_t *i2s_buffer = calloc(frame_size * (nch + 1), sizeof(int16_t)); // nch channel MIC data and one channel reference data
    tester->running_time = 0;
    tester->wave_time = 0;

    for (int i = 0; i < tester->file_num; i++) {
        wav_decoder = wav_decoder_open(tester->file_list[i]);
        file_nch = wav_decoder_get_channel(wav_decoder);

        if (wav_decoder == NULL) {
            printf("can not find %s, play next song\n", tester->file_list[i]);
            continue;
        } else if (wav_decoder_get_sample_rate(wav_decoder) != sample_rate) {
            printf("The sample rate of %s does not meet the requirements, please resample to %d\n",
                   tester->file_list[i], sample_rate);
            wav_decoder_close(wav_decoder);
            continue;
        } else if (file_nch != nch + 1) {

            printf("The channel of %s does not meet the requirements(n=%d), please input %d channel MIC data and one channel reference data\n",
                   tester->file_list[i], file_nch, nch);
            wav_decoder_close(wav_decoder);
            continue;
        } else {
            printf("start to process %s\n", tester->file_list[i]);
        }

        tester->file_id = i;
        tester->file_det_times[i] = 0;
        int out_samples = 0;
        int size = i2s_buffer_size;

        while (1) {
            size = wav_decoder_run(wav_decoder, (unsigned char *)i2s_buffer, i2s_buffer_size);
            out_samples += frame_size;

            // size=i2s_buffer_size;
            if (size == i2s_buffer_size) {
                afe_handle->feed(afe_data, i2s_buffer);
                vTaskDelay(20 / portTICK_PERIOD_MS);
            } else {
                // wav decoder free
                vTaskDelay(1000 / portTICK_PERIOD_MS);
                wav_decoder_close(wav_decoder);
                wav_decoder = NULL;
                vTaskDelay(1000 / portTICK_PERIOD_MS);
                break;
            }
        }

        tester->wave_time += out_samples;
    }

    tester->test_done = 1;
    print_wn_report(tester);
    vTaskDelete(NULL);
}

void fetch_task(void *arg)
{
    printf("Create fetch task ...\n");
    skainet_perf_tester *tester = arg;
    esp_afe_sr_iface_t *afe_handle = tester->afe_handle;
    esp_afe_sr_data_t *afe_data = tester->afe_data;
    uint32_t c0, c1;
    tester->running_time = 0;
    tester->wave_time = 0;
    int file_id = 0;
    int chunk_num = 1;

    while (1) {
        RSR(CCOUNT, c0);
        afe_fetch_result_t *res = afe_handle->fetch(afe_data);
        if (!res || res->ret_value == ESP_FAIL) {
            break;
        }
        // int res = 0;
        RSR(CCOUNT, c1);
        tester->running_time += c1 - c0;
        chunk_num += 1;
        if (res->wakeup_state == WAKENET_DETECTED) {
            tester->file_det_times[file_id]++;
        }
        if (file_id != tester->file_id) {
            file_id = tester->file_id;
            chunk_num = 0;
        } else if (tester->test_done) {
            break;
        }
    }
    vTaskDelete(NULL);
}

void offline_wn_tester(const char *csv_file,
                       const char *log_file,
                       const esp_afe_sr_iface_t *afe_handle,
                       afe_config_t *afe_config,
                       int audio_type)
{
    skainet_perf_tester *tester = malloc(sizeof(skainet_perf_tester));
    // ringbuffer init
    tester->tester_mem_size = heap_caps_get_free_size(MALLOC_CAP_8BIT);
    tester->tester_sram_size = heap_caps_get_free_size(MALLOC_CAP_INTERNAL);

    int m1 = 0, m2 = 0;
    int sm1 = 0, sm2 = 0;
    tester->rb_buffer_size = 4096 * 2;

    // file list init
    tester->max_file_num = 50;
    tester->file_id = 0;
    tester->file_num = 0;
    tester->file_det_times = calloc(tester->max_file_num, sizeof(int));
    tester->file_list = malloc(sizeof(char *) * tester->max_file_num);
    tester->csv_col2 = malloc(sizeof(int) * tester->max_file_num);
    tester->csv_col3 = malloc(sizeof(int) * tester->max_file_num);

    tester->audio_type = audio_type;
    for (int i = 0; i < tester->max_file_num; i++) {
        tester->file_list[i] = calloc(FATFS_PATH_LENGTH_MAX, sizeof(char));
    }

    // sdcard_scan(tester, test_path, audio_type);
    tester->csv_file = (char *)csv_file;
    read_csv_file(tester);
    tester->log_file = (char *) log_file;
    tester->test_done = 0;

    // the memory before AFE init
    m1 = heap_caps_get_free_size(MALLOC_CAP_8BIT);
    sm1 = heap_caps_get_free_size(MALLOC_CAP_INTERNAL);

    // init AFE
    tester->afe_handle = (esp_afe_sr_iface_t *)afe_handle;
    tester->afe_data = afe_handle->create_from_config(afe_config);
    tester->frame_size = afe_handle->get_feed_chunksize(tester->afe_data);
    tester->sample_rate = afe_handle->get_samp_rate(tester->afe_data);
    tester->nch = afe_handle->get_channel_num(tester->afe_data);

    // the memory after AFE init
    m2 = heap_caps_get_free_size(MALLOC_CAP_8BIT);
    sm2 = heap_caps_get_free_size(MALLOC_CAP_INTERNAL);
    tester->afe_mem_size = m1 - m2;                      // the memory size of afe init
    tester->afe_sram_size = sm1 - sm2;

    // running time init
    tester->wave_time = 0;
    tester->running_time = 0;

    // printf("The memory info after init:\n");
    if (audio_type == TESTER_WAV_3CH) {
        xTaskCreatePinnedToCore(&wav_feed_task, "wav_feed_task", 4 * 1024, (void *)tester, 8, NULL, 1);
    }

    if (audio_type == TESTER_WAV_3CH) {
        xTaskCreatePinnedToCore(&fetch_task, "fetch_task", 4 * 1024, (void *)tester, 8, NULL, 0);
        vTaskDelay(2000 / portTICK_PERIOD_MS);
    }
}