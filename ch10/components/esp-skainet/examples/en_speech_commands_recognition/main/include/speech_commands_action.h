/* 
   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/
#ifndef _SPEECH_COMMANDS_ACTION_H_
#define _SPEECH_COMMANDS_ACTION_H_

#ifdef CONFIG_ESP_LYRAT_MINI_V1_1_BOARD
#define LED_GPIO 22
#endif

void led_init(void);

void led_on(int gpio);

void led_off(int gpio);

void led_Task(void *arg);

void speech_commands_action(int command_id);

void wake_up_action(void);
#endif