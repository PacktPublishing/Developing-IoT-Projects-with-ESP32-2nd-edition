/* SPDX-FileCopyrightText: 2022-2023 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include "esp_log.h"
#include "driver/gpio.h"
#include "button_gpio.h"
#include "esp_sleep.h"

static const char *TAG = "gpio button";

#define GPIO_BTN_CHECK(a, str, ret_val)                          \
    if (!(a))                                                     \
    {                                                             \
        ESP_LOGE(TAG, "%s(%d): %s", __FUNCTION__, __LINE__, str); \
        return (ret_val);                                         \
    }

esp_err_t button_gpio_init(const button_gpio_config_t *config)
{
    GPIO_BTN_CHECK(NULL != config, "Pointer of config is invalid", ESP_ERR_INVALID_ARG);
    GPIO_BTN_CHECK(GPIO_IS_VALID_GPIO(config->gpio_num), "GPIO number error", ESP_ERR_INVALID_ARG);

    gpio_config_t gpio_conf;
    gpio_conf.intr_type = GPIO_INTR_DISABLE;
    gpio_conf.mode = GPIO_MODE_INPUT;
    gpio_conf.pin_bit_mask = (1ULL << config->gpio_num);
    if (config->active_level) {
        gpio_conf.pull_down_en = GPIO_PULLDOWN_ENABLE;
        gpio_conf.pull_up_en = GPIO_PULLUP_DISABLE;
    } else {
        gpio_conf.pull_down_en = GPIO_PULLDOWN_DISABLE;
        gpio_conf.pull_up_en = GPIO_PULLUP_ENABLE;
    }
    gpio_config(&gpio_conf);

#if CONFIG_GPIO_BUTTON_SUPPORT_POWER_SAVE
    if (config->enable_power_save) {
        /* Enable wake up from GPIO */
        esp_err_t ret = gpio_wakeup_enable(config->gpio_num, config->active_level == 0 ? GPIO_INTR_LOW_LEVEL : GPIO_INTR_HIGH_LEVEL);
        GPIO_BTN_CHECK(ret == ESP_OK, "Enable gpio wakeup failed", ESP_FAIL);
        ret = esp_sleep_enable_gpio_wakeup();
        GPIO_BTN_CHECK(ret == ESP_OK, "Configure gpio as wakeup source failed", ESP_FAIL);
    }
#endif

    return ESP_OK;
}

esp_err_t button_gpio_deinit(int gpio_num)
{
    return gpio_reset_pin(gpio_num);;
}

uint8_t button_gpio_get_key_level(void *gpio_num)
{
    return (uint8_t)gpio_get_level((uint32_t)gpio_num);
}

esp_err_t button_gpio_set_intr(int gpio_num, gpio_int_type_t intr_type, gpio_isr_t isr_handler, void *args)
{
    static bool isr_service_installed = false;
    gpio_set_intr_type(gpio_num, intr_type);
    if (!isr_service_installed) {
        gpio_install_isr_service(ESP_INTR_FLAG_IRAM);
        isr_service_installed = true;
    }
    gpio_isr_handler_add(gpio_num, isr_handler, args);
    return ESP_OK;
}

esp_err_t button_gpio_intr_control(int gpio_num, bool enable)
{
    if (enable) {
        gpio_intr_enable(gpio_num);
    } else {
        gpio_intr_disable(gpio_num);
    }
    return ESP_OK;
}
