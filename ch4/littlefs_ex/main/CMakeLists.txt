idf_component_register(SRCS "littlefs_ex.cpp" INCLUDE_DIRS ".")
littlefs_create_partition_image(storage ../files FLASH_IN_PROJECT)
