/*
   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/

#pragma once

#include <app_priv.h>
#include <esp_err.h>

esp_err_t app_matter_init();
esp_err_t app_matter_endpoint_create();
esp_err_t app_matter_start();
esp_err_t app_matter_pre_rainmaker_start();
void app_matter_enable_matter_console();
esp_err_t app_matter_report_power(bool val);
