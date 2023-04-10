
#include "AppWifi.hpp"

#include "wifi_provisioning/scheme_ble.h"

#define PROV_TRANSPORT_BLE "ble"

namespace app
{
    class AppWifiBle : public AppWifi
    {
    public:
        void connect(void) override
        {
            wifi_prov_mgr_config_t config = {
                .scheme = wifi_prov_scheme_ble,
                .scheme_event_handler = WIFI_PROV_EVENT_HANDLER_NONE,
            };

            wifi_prov_mgr_init(config);
            bool provisioned = false;
            wifi_prov_mgr_is_provisioned(&provisioned);
            if (!provisioned)
            {
                esp_netif_create_default_wifi_ap();
                uint8_t custom_service_uuid[] = {
                    0xb4,
                    0xdf,
                    0x5a,
                    0x1c,
                    0x3f,
                    0x6b,
                    0xf4,
                    0xbf,
                    0xea,
                    0x4a,
                    0x82,
                    0x03,
                    0x04,
                    0x90,
                    0x1a,
                    0x02,
                };
                wifi_prov_scheme_ble_set_service_uuid(custom_service_uuid);
                wifi_prov_security_t security = WIFI_PROV_SECURITY_1;
                wifi_prov_mgr_start_provisioning(security, nullptr, PROV_SSID, nullptr);
                printQrCode(PROV_TRANSPORT_BLE);
                wifi_prov_mgr_wait();
                wifi_prov_mgr_deinit();
            }
            else
            {
                wifi_prov_mgr_deinit();
                esp_wifi_set_mode(WIFI_MODE_STA);
                esp_wifi_start();
            }
        }
    };

}