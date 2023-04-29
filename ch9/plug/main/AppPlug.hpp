// https://rainmaker.espressif.com/docs/standard-types.html

#pragma once

#include "AppNode.hpp"
#include "driver/gpio.h"
#include "AppEsp32C3Bsp.hpp"

namespace app
{
    class AppPlug : public AppNode, private AppEsp32C3Bsp
    {
    private:
        esp_rmaker_param_t *m_power_param;
        bool m_state;

        void update(bool val);
        static void buttonHandler(void *arg);
        static void definePlug(esp_rmaker_device_t *device, void *arg);
        static esp_err_t requestHandler(const esp_rmaker_device_t *device, const esp_rmaker_param_t *param, const esp_rmaker_param_val_t val, void *priv_data, esp_rmaker_write_ctx_t *ctx);

    public:
        AppPlug() : AppNode({"Plug Node", "esp.node.plug", "Plug", "esp.device.plug", definePlug, this}), m_state(false)
        {
        }

        void init() override
        {
            gpio_config_t config{GPIO_SEL_19,
                                 GPIO_MODE_OUTPUT,
                                 GPIO_PULLUP_DISABLE,
                                 GPIO_PULLDOWN_DISABLE,
                                 GPIO_INTR_DISABLE};
            gpio_config(&config);

            AppEsp32C3Bsp::init();
            addButtonHandler(button_cb_type_t::BUTTON_CB_RELEASE, buttonHandler, this);
            AppNode::init();
        }
    };

    void AppPlug::update(bool val)
    {
        m_state = val;
        gpio_set_level(gpio_num_t::GPIO_NUM_19, val ? 1u : 0);
        esp_rmaker_param_update_and_report(m_power_param, esp_rmaker_bool(val));
        setLed({val, 360, 50, 50});
    }

    void AppPlug::buttonHandler(void *arg)
    {
        AppPlug *obj = reinterpret_cast<AppPlug *>(arg);
        obj->update(!obj->m_state);
    }

    esp_err_t AppPlug::requestHandler(const esp_rmaker_device_t *device, const esp_rmaker_param_t *param, const esp_rmaker_param_val_t val, void *priv_data, esp_rmaker_write_ctx_t *ctx)
    {
        AppPlug *obj = reinterpret_cast<AppPlug *>(priv_data);
        obj->update(val.val.b);
        return ESP_OK;
    }

    void AppPlug::definePlug(esp_rmaker_device_t *device, void *arg)
    {
        AppPlug *obj = reinterpret_cast<AppPlug *>(arg);
        obj->m_power_param = esp_rmaker_power_param_create("power", false);
        esp_rmaker_device_add_param(device, obj->m_power_param);
        esp_rmaker_device_assign_primary_param(device, obj->m_power_param);

        esp_rmaker_device_add_cb(device, requestHandler, nullptr);
    }

}
