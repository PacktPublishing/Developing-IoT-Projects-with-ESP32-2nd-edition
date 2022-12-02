#include "bsp_board.h"
#include "bsp_storage.h"

#include "AppUi.hpp"
#include "AppButton.hpp"

#include <cstdio>

namespace
{
    app::AppUi m_app_ui;
    app::AppButton m_app_btn;
}

extern "C" void app_main(void)
{
    bsp_board_init();
    bsp_board_power_ctrl(POWER_MODULE_AUDIO, true);
    bsp_spiffs_init("storage", "/spiffs", 10);

    auto btn_evt_handler = [](app::sAppButtonEvent &e)
    {
        m_app_ui.buttonEventHandler(e);
    };

    m_app_ui.init();
    m_app_btn.init(btn_evt_handler);
}
