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

#include <string.h>
#include <esp_event.h>
#include <esp_wifi.h>
#include <esp_netif_ip_addr.h>
#include <esp_diagnostics_variables.h>

#define TAG_IP             "ip"
#define TAG_WIFI           "wifi"

/* Wifi keys */
#define KEY_CONNECTED      "conn"
#define KEY_SSID           "ssid"
#define KEY_BSSID          "bssid"
#define KEY_CHANNEL        "channel"
#define KEY_AUTHMODE       "auth"
#define KEY_REASON         "reason"

/* IP keys */
#define KEY_IPv4           "ipv4"
#define KEY_NETMASK        "netmask"
#define KEY_GATEWAY        "gw"

#define PATH_WIFI_STATION  "Wi-Fi.Station"
#define PATH_IP_STATION    "IP.Station"

typedef struct {
    wifi_event_sta_connected_t prev_sta_data;
    bool wifi_connected;
} priv_data_t;

static priv_data_t s_priv_data;

static bool bssid_matched(uint8_t *bssid1, uint8_t *bssid2)
{
    uint8_t i;
    for (i = 0; i < 6; i++) {
        if (bssid1[i] != bssid2[i]) {
            return false;
        }
    }
    return true;
}

static void evt_handler(void *arg, esp_event_base_t evt_base, int32_t evt_id, void *evt_data)
{
    if (evt_base == WIFI_EVENT) {
        switch (evt_id) {
            case WIFI_EVENT_STA_CONNECTED:
            {
                s_priv_data.wifi_connected = true;
                wifi_event_sta_connected_t *data = evt_data;
                esp_diag_variable_add_bool(KEY_CONNECTED, s_priv_data.wifi_connected);

                if (strncmp((char *)s_priv_data.prev_sta_data.ssid, (char *)data->ssid, data->ssid_len) != 0) {
                    esp_diag_variable_add_str(KEY_SSID, (char *)data->ssid);
                }
                if (!bssid_matched(s_priv_data.prev_sta_data.bssid, data->bssid)) {
                    esp_diag_variable_add_mac(KEY_BSSID, data->bssid);
                }
                if (s_priv_data.prev_sta_data.channel != data->channel) {
                    esp_diag_variable_add_int(KEY_CHANNEL, data->channel);
                }
                if (s_priv_data.prev_sta_data.authmode != data->authmode) {
                    esp_diag_variable_add_uint(KEY_AUTHMODE, data->authmode);
                }
                memcpy(&s_priv_data.prev_sta_data, data, sizeof(s_priv_data.prev_sta_data));
                break;
            }
            case WIFI_EVENT_STA_DISCONNECTED:
            {
                if (s_priv_data.wifi_connected) {
                    s_priv_data.wifi_connected = false;
                    wifi_event_sta_disconnected_t *data = evt_data;
                    esp_diag_variable_add_bool(KEY_CONNECTED, s_priv_data.wifi_connected);
                    esp_diag_variable_add_int(KEY_REASON, data->reason);
                }
                break;
            }
            case WIFI_EVENT_STA_AUTHMODE_CHANGE:
            {
                wifi_event_sta_authmode_change_t *data = evt_data;
                esp_diag_variable_add_uint(KEY_AUTHMODE, data->new_mode);
                s_priv_data.prev_sta_data.authmode = data->new_mode;
                break;
            }
            default:
                break;
        }
    } else if (evt_base == IP_EVENT) {
        switch(evt_id) {
            case IP_EVENT_STA_GOT_IP:
            {
                ip_event_got_ip_t *data = evt_data;
                esp_diag_variable_add_ipv4(KEY_IPv4, data->ip_info.ip.addr);
                esp_diag_variable_add_ipv4(KEY_NETMASK, data->ip_info.netmask.addr);
                esp_diag_variable_add_ipv4(KEY_GATEWAY, data->ip_info.gw.addr);
                break;
            }
            case IP_EVENT_STA_LOST_IP:
            {
                uint32_t ip = 0x0;
                esp_diag_variable_add_ipv4(KEY_IPv4, ip);
                break;
            }
            default:
                break;
        }
    }
}

esp_err_t esp_diag_network_variables_init(void)
{
    wifi_ap_record_t ap_info;
    esp_netif_ip_info_t ip_info;

    /* Register the event handler for wifi events */
    esp_err_t err = esp_event_handler_register(WIFI_EVENT, ESP_EVENT_ANY_ID, evt_handler, NULL);
    if (err != ESP_OK) {
        return err;
    }
    /* Register the event handler for ip events */
    err = esp_event_handler_register(IP_EVENT, ESP_EVENT_ANY_ID, evt_handler, NULL);
    if (err != ESP_OK) {
        return err;
    }

    /* wifi variables */
    esp_diag_variable_register(TAG_WIFI, KEY_CONNECTED, "Connected", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_BOOL);
    esp_diag_variable_register(TAG_WIFI, KEY_SSID, "SSID", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_STR);
    esp_diag_variable_register(TAG_WIFI, KEY_BSSID, "BSSID", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_MAC);
    esp_diag_variable_register(TAG_WIFI, KEY_CHANNEL, "Channel", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_INT);
    esp_diag_variable_register(TAG_WIFI, KEY_AUTHMODE, "Auth Mode", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_UINT);
    esp_diag_variable_register(TAG_WIFI, KEY_REASON, "Last Wi-Fi disconnect reason", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_INT);

    /* IP address variables */
    esp_diag_variable_register(TAG_IP, KEY_IPv4, "IPv4", PATH_IP_STATION, ESP_DIAG_DATA_TYPE_IPv4);
    esp_diag_variable_register(TAG_IP, KEY_NETMASK, "Netmask", PATH_IP_STATION, ESP_DIAG_DATA_TYPE_IPv4);
    esp_diag_variable_register(TAG_IP, KEY_GATEWAY, "Gateway", PATH_IP_STATION, ESP_DIAG_DATA_TYPE_IPv4);

    memset(&s_priv_data.prev_sta_data, 0, sizeof(s_priv_data.prev_sta_data));
    /* If wifi is not connected then wifi details are recorded in event handler */
    if (esp_wifi_sta_get_ap_info(&ap_info) == ESP_OK) {
        /* If wifi is connected then record the wifi details */
        memcpy(s_priv_data.prev_sta_data.ssid, ap_info.ssid, sizeof(s_priv_data.prev_sta_data.ssid));
        memcpy(s_priv_data.prev_sta_data.bssid, ap_info.bssid, sizeof(s_priv_data.prev_sta_data.bssid));
        s_priv_data.prev_sta_data.channel = ap_info.primary;
        s_priv_data.prev_sta_data.authmode = ap_info.authmode;
        s_priv_data.wifi_connected = true;

        esp_diag_variable_add_bool(KEY_CONNECTED, s_priv_data.wifi_connected);
        esp_diag_variable_add_str(KEY_SSID, (char *)ap_info.ssid);
        esp_diag_variable_add_mac(KEY_BSSID, ap_info.bssid);
        esp_diag_variable_add_int(KEY_CHANNEL, ap_info.primary);
        esp_diag_variable_add_uint(KEY_AUTHMODE, ap_info.authmode);
    }

    memset(&ip_info, 0, sizeof(ip_info));
    /* If wifi interface is up and running then record the details */
    if (esp_netif_is_netif_up(esp_netif_get_handle_from_ifkey("WIFI_STA_DEF"))
        && esp_netif_get_ip_info(esp_netif_get_handle_from_ifkey("WIFI_STA_DEF"), &ip_info) == ESP_OK) {
        esp_diag_variable_add_ipv4(KEY_IPv4, ip_info.ip.addr);
        esp_diag_variable_add_ipv4(KEY_NETMASK, ip_info.netmask.addr);
        esp_diag_variable_add_ipv4(KEY_GATEWAY, ip_info.gw.addr);
    }
    return ESP_OK;
}
