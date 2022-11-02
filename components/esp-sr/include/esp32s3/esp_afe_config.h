#pragma once
#include "stdint.h"
#include "esp_wn_iface.h"
#include "esp_wn_models.h"
#include "esp_vad.h"

//AFE: Audio Front-End 
//SR:  Speech Recognition
//afe_sr/AFE_SR: the audio front-end for speech recognition

//Set AFE_SR mode
typedef enum {
    SR_MODE_LOW_COST = 0,
    SR_MODE_HIGH_PERF = 1
} afe_sr_mode_t;

typedef enum {
    AFE_MEMORY_ALLOC_MORE_INTERNAL = 1,             // malloc with more internal ram
    AFE_MEMORY_ALLOC_INTERNAL_PSRAM_BALANCE = 2,    // malloc with internal ram and psram in balance
    AFE_MEMORY_ALLOC_MORE_PSRAM = 3                 // malloc with more psram
} afe_memory_alloc_mode_t;

typedef enum {
    AFE_MN_PEAK_AGC_MODE_1 = -5,            // The peak amplitude of audio fed to multinet is -5dB
    AFE_MN_PEAK_AGC_MODE_2 = -4,            // The peak amplitude of audio fed to multinet is -4dB
    AFE_MN_PEAK_AGC_MODE_3 = -3,            // The peak amplitude of audio fed to multinet is -3dB
    AFE_MN_PEAK_NO_AGC = 0,                 // There is no agc gain
} afe_mn_peak_agc_mode_t;

typedef struct {
    int total_ch_num;                       // total channel num. It must be: total_ch_num = mic_num + ref_num
    int mic_num;                            // mic channel num
    int ref_num;                            // reference channel num
} afe_pcm_config_t;

typedef struct {
    bool aec_init;
    bool se_init;
    bool vad_init;
    bool wakenet_init;
    bool voice_communication_init;
    vad_mode_t vad_mode;                    // The value can be: VAD_MODE_0, VAD_MODE_1, VAD_MODE_2, VAD_MODE_3, VAD_MODE_4
    esp_wn_iface_t *wakenet_model;
    void *wakenet_coeff;
    det_mode_t wakenet_mode;
    afe_sr_mode_t afe_mode;
    int afe_perferred_core;
    int afe_perferred_priority;
    int afe_ringbuf_size;
    afe_memory_alloc_mode_t memory_alloc_mode;
    afe_mn_peak_agc_mode_t agc_mode;
    afe_pcm_config_t pcm_config;            // Config the channel num of original data which is fed to the afe feed function.
} afe_config_t;


#if CONFIG_IDF_TARGET_ESP32
#define AFE_CONFIG_DEFAULT() { \
    .aec_init = true, \
    .se_init = true, \
    .vad_init = true, \
    .wakenet_init = true, \
    .voice_communication_init = false, \
    .vad_mode = VAD_MODE_3, \
    .wakenet_model = &WAKENET_MODEL, \
    .wakenet_coeff = &WAKENET_COEFF, \
    .wakenet_mode = DET_MODE_90, \
    .afe_mode = SR_MODE_HIGH_PERF, \
    .afe_perferred_core = 0, \
    .afe_perferred_priority = 5, \
    .afe_ringbuf_size = 50, \
    .memory_alloc_mode = AFE_MEMORY_ALLOC_INTERNAL_PSRAM_BALANCE, \
    .agc_mode = AFE_MN_PEAK_AGC_MODE_2, \
    .pcm_config.total_ch_num = 2, \
    .pcm_config.mic_num = 1, \
    .pcm_config.ref_num = 1, \
}
#elif CONFIG_IDF_TARGET_ESP32S3
#define AFE_CONFIG_DEFAULT() { \
    .aec_init = true, \
    .se_init = true, \
    .vad_init = true, \
    .wakenet_init = true, \
    .voice_communication_init = false, \
    .vad_mode = VAD_MODE_3, \
    .wakenet_model = (esp_wn_iface_t *)&WAKENET_MODEL, \
    .wakenet_coeff = (void *)&WAKENET_COEFF, \
    .wakenet_mode = DET_MODE_2CH_90, \
    .afe_mode = SR_MODE_LOW_COST, \
    .afe_perferred_core = 0, \
    .afe_perferred_priority = 5, \
    .afe_ringbuf_size = 50, \
    .memory_alloc_mode = AFE_MEMORY_ALLOC_MORE_PSRAM, \
    .agc_mode = AFE_MN_PEAK_AGC_MODE_2, \
    .pcm_config.total_ch_num = 3, \
    .pcm_config.mic_num = 2, \
    .pcm_config.ref_num = 1, \
}
#endif