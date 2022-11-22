#include "bsp_board.h"

#include "AppUi.hpp"
#include "AppButton.hpp"

namespace
{
    app::AppUi m_app_ui;
    app::AppButton m_app_btn;
}

extern "C" void app_main(void)
{
    bsp_board_init();

    auto btn_evt_handler = [](app::sAppButtonEvent &e)
    {
        m_app_ui.buttonEventHandler(e);
    };

    m_app_ui.init();
    m_app_btn.init(btn_evt_handler);
}
