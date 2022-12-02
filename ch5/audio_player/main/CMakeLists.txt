idf_component_register(SRCS 
    audio_player.cpp  
    ui.c
    ui_events.c
    ui_helpers.c
    ui_img_1258062811.c
    ui_img_1258080204.c
    ui_img_1310788941.c
    ui_img_1310804284.c
    ui_img_1552218578.c
    ui_img_1552235971.c
    ui_img_603081905.c
    ui_img_603097248.c
    INCLUDE_DIRS ".")
spiffs_create_partition_image(storage ../spiffs FLASH_IN_PROJECT)