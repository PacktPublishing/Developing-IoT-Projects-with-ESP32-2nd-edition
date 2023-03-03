
#include "AppWifi.hpp"

#include "wifi_provisioning/scheme_softap.h"

#define PROV_TRANSPORT_SOFTAP "softap"


namespace app
{
    class AppWifiSoftAp : public AppWifi
    {
    public:
        void connect(void) override
        {
            wifi_prov_mgr_config_t config = {
                .scheme = wifi_prov_scheme_softap,
                .scheme_event_handler = WIFI_PROV_EVENT_HANDLER_NONE,
            };

            wifi_prov_mgr_init(config);
            bool provisioned = false;
            wifi_prov_mgr_is_provisioned(&provisioned);
            if (!provisioned)
            {
                esp_netif_create_default_wifi_ap();
                wifi_prov_security_t security = WIFI_PROV_SECURITY_1;
                wifi_prov_mgr_start_provisioning(security, nullptr, PROV_SSID, nullptr);
                printQrCode(PROV_TRANSPORT_SOFTAP);
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