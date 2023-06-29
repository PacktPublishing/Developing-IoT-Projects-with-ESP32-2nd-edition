/*
 * SPDX-FileCopyrightText: 2023 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "driver/i2c.h"
#include "esp_idf_version.h"
#if ESP_IDF_VERSION >= ESP_IDF_VERSION_VAL(5, 0, 0)
#include "driver/i2s_std.h"
#include "soc/soc_caps.h"
#else
#include "driver/i2s.h"
#endif
#include "esp_codec_dev.h"
#include "esp_codec_dev_defaults.h"
#include "test_board.h"
#include "unity.h"

#if ESP_IDF_VERSION >= ESP_IDF_VERSION_VAL(5, 0, 0)

#define I2S_MAX_KEEP SOC_I2S_NUM

typedef struct {
    i2s_chan_handle_t tx_handle;
    i2s_chan_handle_t rx_handle;
} i2s_keep_t;

static i2s_keep_t *i2s_keep[I2S_MAX_KEEP];

#endif

static int ut_i2c_init(uint8_t port)
{
    i2c_config_t i2c_cfg = {
        .mode = I2C_MODE_MASTER,
        .sda_pullup_en = GPIO_PULLUP_ENABLE,
        .scl_pullup_en = GPIO_PULLUP_ENABLE,
        .master.clk_speed = 100000,
    };
    i2c_cfg.sda_io_num = TEST_BOARD_I2C_SDA_PIN;
    i2c_cfg.scl_io_num = TEST_BOARD_I2C_SCL_PIN;
    esp_err_t ret = i2c_param_config(port, &i2c_cfg);
    if (ret != ESP_OK) {
        return -1;
    }
    return i2c_driver_install(port, i2c_cfg.mode, 0, 0, 0);
}

static int ut_i2c_deinit(uint8_t port)
{
    return i2c_driver_delete(port);
}

static int ut_i2s_init(uint8_t port)
{
#if ESP_IDF_VERSION >= ESP_IDF_VERSION_VAL(5, 0, 0)
    if (port >= I2S_MAX_KEEP) {
        return -1;
    }
    // Already installed
    if (i2s_keep[port]) {
        return 0;
    }
    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_0, I2S_ROLE_MASTER);
    i2s_std_config_t std_cfg = {
        .clk_cfg = I2S_STD_CLK_DEFAULT_CONFIG(48000),
        .slot_cfg = I2S_STD_MSB_SLOT_DEFAULT_CONFIG(16, I2S_SLOT_MODE_STEREO),
        .gpio_cfg =
            {
                       .mclk = TEST_BOARD_I2S_MCK_PIN,
                       .bclk = TEST_BOARD_I2S_BCK_PIN,
                       .ws = TEST_BOARD_I2S_DATA_WS_PIN,
                       .dout = TEST_BOARD_I2S_DATA_OUT_PIN,
                       .din = TEST_BOARD_I2S_DATA_IN_PIN,
                       },
    };
    i2s_keep[port] = (i2s_keep_t *) calloc(1, sizeof(i2s_keep_t));
    if (i2s_keep[port] == NULL) {
        return -1;
    }
    int ret = i2s_new_channel(&chan_cfg, &i2s_keep[port]->tx_handle, &i2s_keep[port]->rx_handle);
    i2s_channel_init_std_mode(i2s_keep[port]->tx_handle, &std_cfg);
    i2s_channel_init_std_mode(i2s_keep[port]->rx_handle, &std_cfg);
    i2s_channel_enable(i2s_keep[port]->tx_handle);
    i2s_channel_enable(i2s_keep[port]->rx_handle);
#else
    i2s_config_t i2s_config = {
        .mode = (i2s_mode_t) (I2S_MODE_TX | I2S_MODE_RX | I2S_MODE_MASTER),
        .sample_rate = 44100,
        .bits_per_sample = I2S_BITS_PER_SAMPLE_16BIT,
        .channel_format = I2S_CHANNEL_FMT_RIGHT_LEFT,
        .communication_format = I2S_COMM_FORMAT_STAND_I2S,
        .intr_alloc_flags = ESP_INTR_FLAG_LEVEL2 | ESP_INTR_FLAG_IRAM,
        .dma_buf_count = 2,
        .dma_buf_len = 128,
        .use_apll = true,
        .tx_desc_auto_clear = true,
    };
    int ret = i2s_driver_install(port, &i2s_config, 0, NULL);
    i2s_pin_config_t i2s_pin_cfg = {
        .mck_io_num = TEST_BOARD_I2S_MCK_PIN,
        .bck_io_num = TEST_BOARD_I2S_BCK_PIN,
        .ws_io_num = TEST_BOARD_I2S_DATA_WS_PIN,
        .data_out_num = TEST_BOARD_I2S_DATA_OUT_PIN,
        .data_in_num = TEST_BOARD_I2S_DATA_IN_PIN,
    };
    i2s_set_pin(port, &i2s_pin_cfg);
#endif
    return ret;
}

static int ut_i2s_deinit(uint8_t port)
{
#if ESP_IDF_VERSION >= ESP_IDF_VERSION_VAL(5, 0, 0)
    if (port >= I2S_MAX_KEEP) {
        return -1;
    }
    // already installed
    if (i2s_keep[port] == NULL) {
        return 0;
    }
    i2s_channel_disable(i2s_keep[port]->tx_handle);
    i2s_channel_disable(i2s_keep[port]->rx_handle);
    i2s_del_channel(i2s_keep[port]->tx_handle);
    i2s_del_channel(i2s_keep[port]->rx_handle);
    free(i2s_keep[port]);
    i2s_keep[port] = NULL;
#else
    i2s_driver_uninstall(port);
#endif
    return 0;
}

static int codec_max_sample(uint8_t *data, int size)
{
    int16_t *s = (int16_t *) data;
    size >>= 1;
    int i = 0, max = 0;
    while (i < size) {
        if (s[i] > max) {
            max = s[i];
        }
        i++;
    }
    return max;
}

TEST_CASE("esp codec dev test using S3 board", "[esp_codec_dev]")
{
    // Need install driver (i2c and i2s) firstly
    int ret = ut_i2c_init(0);
    TEST_ESP_OK(ret);
    ret = ut_i2s_init(0);
    TEST_ESP_OK(ret);
    // Do initialize of related interface: data_if, ctrl_if and gpio_if
    audio_codec_i2s_cfg_t i2s_cfg = {
#if ESP_IDF_VERSION >= ESP_IDF_VERSION_VAL(5, 0, 0)
        .rx_handle = i2s_keep[0]->rx_handle,
        .tx_handle = i2s_keep[0]->tx_handle,
#endif
    };
    const audio_codec_data_if_t *data_if = audio_codec_new_i2s_data(&i2s_cfg);
    TEST_ASSERT_NOT_NULL(data_if);

    audio_codec_i2c_cfg_t i2c_cfg = {.addr = ES8311_CODEC_DEFAULT_ADDR};
    const audio_codec_ctrl_if_t *out_ctrl_if = audio_codec_new_i2c_ctrl(&i2c_cfg);
    TEST_ASSERT_NOT_NULL(out_ctrl_if);

    i2c_cfg.addr = ES7210_CODEC_DEFAULT_ADDR;
    const audio_codec_ctrl_if_t *in_ctrl_if = audio_codec_new_i2c_ctrl(&i2c_cfg);
    TEST_ASSERT_NOT_NULL(in_ctrl_if);

    const audio_codec_gpio_if_t *gpio_if = audio_codec_new_gpio();
    TEST_ASSERT_NOT_NULL(gpio_if);
    // New output codec interface
    es8311_codec_cfg_t es8311_cfg = {
        .codec_mode = ESP_CODEC_DEV_WORK_MODE_DAC,
        .ctrl_if = out_ctrl_if,
        .gpio_if = gpio_if,
        .pa_pin = TEST_BOARD_PA_PIN,
        .use_mclk = true,
    };
    const audio_codec_if_t *out_codec_if = es8311_codec_new(&es8311_cfg);
    TEST_ASSERT_NOT_NULL(out_codec_if);
    // New input codec interface
    es7210_codec_cfg_t es7210_cfg = {
        .ctrl_if = in_ctrl_if,
        .mic_selected = ES7120_SEL_MIC1 | ES7120_SEL_MIC2 | ES7120_SEL_MIC3,
    };
    const audio_codec_if_t *in_codec_if = es7210_codec_new(&es7210_cfg);
    TEST_ASSERT_NOT_NULL(in_codec_if);
    // New output codec device
    esp_codec_dev_cfg_t dev_cfg = {
        .codec_if = out_codec_if,
        .data_if = data_if,
        .dev_type = ESP_CODEC_DEV_TYPE_OUT,
    };
    esp_codec_dev_handle_t play_dev = esp_codec_dev_new(&dev_cfg);
    TEST_ASSERT_NOT_NULL(play_dev);
    // New input codec device
    dev_cfg.codec_if = in_codec_if;
    dev_cfg.dev_type = ESP_CODEC_DEV_TYPE_IN;
    esp_codec_dev_handle_t record_dev = esp_codec_dev_new(&dev_cfg);
    TEST_ASSERT_NOT_NULL(record_dev);

    ret = esp_codec_dev_set_out_vol(play_dev, 60.0);
    TEST_ESP_OK(ret);
    ret = esp_codec_dev_set_in_gain(record_dev, 30.0);
    TEST_ESP_OK(ret);

    esp_codec_dev_sample_info_t fs = {
        .sample_rate = 48000,
        .channel = 2,
        .bits_per_sample = 16,
    };
    ret = esp_codec_dev_open(play_dev, &fs);
    TEST_ESP_OK(ret);

    ret = esp_codec_dev_open(record_dev, &fs);
    TEST_ESP_OK(ret);
    uint8_t *data = (uint8_t *) malloc(512);
    int limit_size = 10 * fs.sample_rate * fs.channel * (fs.bits_per_sample >> 3);
    int got_size = 0;
    int max_sample = 0;
    // Playback the recording content directly
    while (got_size < limit_size) {
        ret = esp_codec_dev_read(record_dev, data, 512);
        TEST_ESP_OK(ret);
        ret = esp_codec_dev_write(play_dev, data, 512);
        TEST_ESP_OK(ret);
        int max_value = codec_max_sample(data, 512);
        if (max_value > max_sample) {
            max_sample = max_value;
        }
        got_size += 512;
    }
    // Verify recording data not zero
    TEST_ASSERT(max_sample > 0);
    free(data);

    ret = esp_codec_dev_close(play_dev);
    TEST_ESP_OK(ret);
    ret = esp_codec_dev_close(record_dev);
    TEST_ESP_OK(ret);
    esp_codec_dev_delete(play_dev);
    esp_codec_dev_delete(record_dev);

    // Delete codec interface
    audio_codec_delete_codec_if(in_codec_if);
    audio_codec_delete_codec_if(out_codec_if);
    // Delete codec control interface
    audio_codec_delete_ctrl_if(in_ctrl_if);
    audio_codec_delete_ctrl_if(out_ctrl_if);
    audio_codec_delete_gpio_if(gpio_if);
    // Delete codec data interface
    audio_codec_delete_data_if(data_if);

    ut_i2c_deinit(0);
    ut_i2s_deinit(0);
}
