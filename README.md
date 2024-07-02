# Developing-IoT-Projects-with-ESP32, Second-edition
This is the code repository for [Developing-IoT-Projects-with-ESP32, Second-edition](https://www.packtpub.com/product/developing-iot-projects-with-esp32-2nd-edition-second-edition/9781803237688), published by Packt.

>**Important!**
>This branch contains major updates to the examples in the book.   
>
>1. The devkits of this branch are:
>    - [ESP-S3-BOX-3 - Successor of ESP-S3-Box-Lite](https://github.com/espressif/esp-box/blob/master/docs/hardware_overview/esp32_s3_box_3/hardware_overview_for_box_3.md)
>    - [ESP32-C3-DevKitM-1](https://docs.espressif.com/projects/esp-dev-kits/en/latest/esp32c3/esp32-c3-devkitm-1/user_guide.html#getting-started)
>
>2. The ESP-IDF version is now [v5.2.2](https://github.com/espressif/esp-idf/tree/v5.2.2). The documentation is [here](https://docs.espressif.com/projects/esp-idf/en/stable/esp32s3/index.html)
>3. All other frameworks and libraries are updated to their latest master branches, compatible with ESP-IDF v5.2.2. (such as ESP-Rainmaker, LVGL, Edge-Impulse, AWS-IoT-Core, ESP-Skainet, ESP-ADF, and others)


**Unlock the full Potential of ESP32 in IoT development to create production-grade smart devices**

The author of this book is -[Vedat Ozan Oner](https://www.linkedin.com/in/vedatozanoner/)

## About the book

ESP32, a low-cost and energy-efficient system-on-a-chip microcontroller, has become the backbone of numerous WiFi devices, fueling IoT innovation. This book offers a holistic approach to building an IoT system from the ground up, ensuring secure data communication from sensors to cloud platforms, empowering you to create production-grade IoT solutions using the ESP32 SoC.
Starting with IoT essentials supported by real-world use cases, this book takes you through the entire process of constructing an IoT device using ESP32. Each chapter introduces new dimensions to your IoT applications, covering sensor communication, the integration of prominent IoT libraries like LittleFS and LVGL, connectivity options via WiFi, security measures, cloud integration, and the visualization of real-time data using Grafana. Furthermore, a dedicated section explores AI/ML for embedded systems, guiding you through building and running ML applications with tinyML and ESP32-S3 to create state-of-the-art embedded products.
This book adopts a hands-on approach, ensuring you can start building IoT solutions right from the beginning. As you reach towards the end of the book, you'll tackle a full-scale Smart Home project, applying all the techniques you've learned in real-time.
Embark on your journey to build secure, production-grade IoT systems with ESP32 today!


## Key Takeaways
* Explore ESP32 with IDE and debugging tools for effective IoT creation
* Drive GPIO, I2C, multimedia, and storage for seamless integration of external devices
* Utilize handy IoT libraries to enhance your ESP32 projects
* Manage WiFi like a pro with STA & AP modes, provisioning, and ESP Rainmaker framework features
* Ensure robust IoT security with secure boot and OTA firmware updates
* Harness AWS IoT for data handling and achieve stunning visualization using Grafana
* Enhance your projects with voice capabilities using ESP AFE and Speech Recognition
* Innovate with tinyML on ESP32-S3 and the Edge Impulse platformr


## New Edition v/s Previous Edition
The author highlights the Internet of Things' (IoT) revolutionary journey since the first edition in this new edition, highlighting technological advancements and the expansion of Espressif Systems' chip range. The advent of the ESP32-C family, with its affordable RISC-V architecture, and the ESP32-S family, which offers Artificial Intelligence-of-Things (AIoT) solutions, serve as examples of the evolution. The introduction highlights how ubiquitous the Internet of Things is among the younger age, giving instances such as a three-year-old who uses an Echo device as a music box. Notable modifications include the use of ESP-IDF and C++ as examples, which facilitate hardware configuration using various development kits. The content realignment mirrors the shifting landscape of IoT development by giving machine learning projects priority while Bluetooth/BLE topics are marginalised. Incorporating conversations on third-party library integration enhances comprehension. The author presents the new version as a study of developing technologies, presenting in-depth insights and useful examples that speak to the contemporary IoT innovation spirit, while acknowledging the first edition's relevance for IoT beginners
 

## Outline and Chapter Summary
 It has been a long time since the first Internet of Things (IoT) devices entered our lives, and now they are helping us in many ways. We have smart TVs, voice assistants, connected appliances at home, or Industrial IoT (IIoT) devices being used in the transportation, healthcare, agriculture, and energy sectors – virtually everywhere. The new generation has been growing up with this technology and using IoT devices effectively (my 3-year-old daughter’s music box, for example, is an Echo device). Furthermore, new IoT products are introduced on the market every day with novel features or improved capabilities. 
 
We all appreciate how fast technology is changing. It is hard for everybody to keep up with all those changes: technology manufacturers, technology consumers, and, in between them, people like us – IoT developers that make technology available to consumers. Since the 1st edition of this book, Espressif Systems has added many chips to their portfolio in response to market needs. For instance, we see the single-core ESP32-C family of System-on-Chip (SoC) devices with RISC-V architecture. They have a reduced set of capabilities and memory but are much cheaper compared to the first ESP32. There is also the ESP32-S family as a new branch of the original ESP32 SoCs with more capabilities and peripherals to support Artificial Intelligence-of-Things (AIoT) solutions. On top of hardware, we see state-of-the-art frameworks and libraries that enable us to use those SoCs in different types of applications. In this book, I’ve tried to cover them from a bit of a different perspective in addition to the basics of ESP32 development as a starting point.

There are several key differences between the first edition and this one. First of all, the examples of this edition are developed in C++ by employing ESP-IDF, compared to the C programming language and the PlatformIO environment in the first edition. We will also use different development kits from Espressif Systems in this edition, which makes hardware setup easier in some examples. In terms of content, we will discuss machine learning on ESP32 with hands-on projects, but the Bluetooth/BLE topics have been excluded from the book and some others have been condensed to make room for the machine learning examples. A noteworthy addition that I expect you would find interesting in this edition is the exploration of integration with third-party libraries. In the relevant chapter, various methods of incorporating third-party libraries into ESP32 projects will be discussed. 

This doesn’t mean the 1st edition is now obsolete. On the contrary, it is still perfectly valid if you are new to IoT with ESP32. With this edition of the book, we have a chance to discuss the subjects where the 1st edition With this edition of the book, we have a chance to discuss in detail about the emerging new technology in terms of new technology. I really enjoyed preparing the examples for this book, and I hope you enjoy them, too. I want to share a wise quote from a distinguished historian and women’s rights activist, Mary Ritter Beard, before delving into the topics. 


1. Chapter 1, [Introduction to IoT Development and the ESP32 Platform]
2. Chapter 2, [Understanding the Development Tools](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch2)
3. Chapter 3, [Using ESP32 Peripherals](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch3)
4. Chapter 4, [Employing Third-party Libraries in ESP32 Projects](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch4)
5. Chapter 5, [Project – Audio Player](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch5/audio_player)
6. Chapter 6, [Using Wi-Fi Communication for Connectivity](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch6)
7. Chapter 7, [ESP32 Security Features for Production-Grade devices](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch7)
8. Chapter 8, [Connecting to Cloud Platforms and Using Services](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch8)
9. Chapter 9, [Project - Smart home](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch9)
10. Chapter 10, [Machine Learning with ESP32](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch10)
11. Chapter 11, [Developing on Edge Impulse](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch11/edgeimpulse_ex)
12. Chapter 12, [Project – Baby Monitor](https://github.com/PacktPublishing/Developing-IoT-Projects-with-ESP32-2nd-edition/tree/main/ch12/baby_monitor)


### Chapter 01, Introduction to IoT Development and the ESP32 Platform
Chapter 1 provides an overview of IoT development and introduces the ESP32 platform, emphasizing both its hardware and software aspects. IoT, as a concept, involves interconnected devices sharing data over the internet to optimize decision-making based on the available information. Beyond this fundamental understanding, the chapter delves into the broader implications of IoT and its multifaceted aspects, laying the groundwork for in-depth exploration throughout the book. 

Espressif's ESP32 emerges as a versatile tool for developers engaged in various IoT projects. The chapter underscores the critical role of proper tool selection in solving domain-specific problems and highlights how ESP32, with its affordability, processing power, connectivity features, and security attributes, stands out in the IoT landscape. The discussion encompasses the ESP32 product family's diverse applications, ranging from simple connected sensors for homes to complex Artificial Intelligence of Things (AIoT) solutions in manufacturing. By the chapter's end, readers gain insights into IoT's basic architecture, the ESP32's role as a tool in IoT solutions, and key considerations for developers new to IoT or considering ESP32 for their projects. The covered topics include the structure of IoT solutions, the ESP32 product family, development platforms and frameworks, and Real-Time Operating System (RTOS) options. 

#### Key Insight Points:
- **IoT Fundamentals**: The chapter establishes a foundational understanding of the Internet of Things (IoT), emphasizing its essence in connecting devices for data exchange over the internet. This basic architecture sets the stage for a deeper exploration of IoT throughout the book. 
- **ESP32 as a Powerful Tool**: Espressif's ESP32 is introduced as a robust tool for IoT developers. The discussion highlights its affordability, processing capabilities, connectivity features, and modern security attributes. The ESP32's versatility is underscored, making it suitable for a wide range of IoT applications, from simple home sensors to complex AIoT projects in manufacturing. 
- **Tool Selection Significance**: The chapter underscores the critical importance of selecting the right tools for IoT development. It draws parallels between software and hardware tools, emphasizing their pivotal role in determining the success of IoT projects. The affordability and capabilities of ESP32 position it as a compelling choice for developers. 
- **Diverse ESP32 Applications**: The ESP32 product family's diverse applications are explored, showcasing its adaptability for various IoT scenarios. Developers can leverage ESP32 for both basic and advanced projects, making it a go-to option for those looking to maximize the value of their IoT solutions. 
- **Key Topics Covered**: The chapter outlines key topics for readers, including the fundamental structure of IoT solutions, an in-depth look at the ESP32 product family, available development platforms and frameworks, and the options for Real-Time Operating Systems (RTOS). These insights provide a comprehensive overview for individuals new to IoT or considering ESP32 for their projects.


### Chapter 02, Understanding the Development Tools
Chapter 2 delves into the essential development tools for working with ESP32, focusing on ESP-IDF and PlatformIO. The chapter initiates hands-on development with real hardware, guiding readers through the installation of the development environment and demonstrating how to run and debug applications using development kits. Covering ESP-IDF, PlatformIO, FreeRTOS, debugging, and unit testing, the chapter lays the groundwork for readers to gain proficiency in ESP32 development. By the end, readers will have acquired fundamental knowledge and practical experience to embark on ESP32 application development. 

The chapter introduces ESP-IDF as the official framework for developing applications across the ESP32 microcontroller series, maintained by Espressif Systems. ESP-IDF provides a comprehensive set of command-line utilities crucial for ESP32 projects. Additionally, the chapter explores PlatformIO, enhancing the development experience with added IDE features, strong integration with VSCode, and a declarative project configuration approach. As readers progress, they are equipped with the tools and insights necessary for professional embedded development.In the upcoming chapter, the focus will shift to ESP32 peripherals, offering practical examples to familiarize readers with common peripherals. While it acknowledges the impossibility of covering all peripherals in a single chapter, the aim is to provide sufficient understanding for readers to confidently handle real projects and experiments presented in the book. 

#### Key Insight Points:
- **Introduction to ESP32 Development Tools**: The chapter provides an introduction to the popular development environments ESP-IDF and PlatformIO, essential for working with the ESP32 microcontroller. It emphasizes the importance of understanding these tools to initiate hands-on development with real hardware. 
- **Hands-On Experience**: Readers are guided through the installation of the development environment, offering a practical and step-by-step approach to set up ESP-IDF and PlatformIO on their machines. The chapter underscores the learning process involved in gaining fundamental knowledge and practical experience in ESP32 application development. 
- **Tool Overview**: The chapter explores ESP-IDF, the official framework for ESP32 development, outlining its command-line utilities crucial for projects. It also introduces PlatformIO, which adds IDE features and enhances the development experience, emphasizing its integration with VSCode and declarative project configuration. 
- **Foundation for Future Chapters**: The chapter sets the foundation for subsequent chapters by covering key topics such as FreeRTOS, debugging, and unit testing. This groundwork is crucial for readers to confidently progress in developing applications for ESP32 microcontrollers. 
- **Upcoming Focus on Peripherals**: The chapter concludes by providing a glimpse into the next topic: ESP32 peripherals. While acknowledging the impossibility of covering all peripherals in a single chapter, it promises practical examples to equip readers with the skills needed for real projects and experiments discussed in the book. 
 
### Chapter 03, Using ESP32 Peripherals
Chapter 3 of the book explores the practical integration of ESP32 peripherals, offering hands-on examples and insights into their application. After laying the groundwork with a discussion on development tools in the previous chapter, this section takes a deeper dive into the role of peripherals as the crucial connection between microcontrollers and the external environment. Readers are introduced to various peripherals such as GPIO, I2C, SPI, I2S, and LCD, each playing a unique role in interacting with the surrounding world. The chapter not only covers their functionalities but also demonstrates their practical use through example applications, providing a foundational understanding of how these peripherals can be leveraged in real-world IoT projects. 

In this exploration of ESP32 peripherals, the chapter emphasizes on the versatility of the ESP32 series chips, catering to different application needs. From GPIO's flexibility to I2S's support for stereo audio output and the graphical capabilities of LCD using LVGL, readers gain valuable insights into employing these peripherals effectively. This practical knowledge sets the stage for the upcoming chapter, where the focus shifts to popular IoT libraries, essential for expediting development and reducing costs in IoT projects. 

#### Key Insight Points:
- **Peripheral Variety**: The chapter delves into the wide array of ESP32 peripherals, including GPIO, I2C, SPI, I2S, and LCD, showcasing their diverse applications in IoT projects. 
- **Practical Application**: Through example applications, readers gain hands-on experience in using ESP32 peripherals, understanding how to interface with sensors, SD cards, and audio and implement graphical user interfaces. 
- **ESP32 Series Distinctions**: Highlighting the distinct features of ESP32 series chips, the chapter notes variations in GPIO pins, USB OTG capabilities, and reduced peripheral sets in different families like ESP32-S2/S3 and ESP32-C. 
- **Foundational IoT Knowledge**: Readers not only learn about the functionalities of each peripheral but also understand their role in connecting microcontrollers to the outer world, laying a foundational understanding for IoT development. 
- **Versatility for IoT Projects**: The chapter underscores the ESP32's versatility, making it suitable for a broad spectrum of IoT applications, from simple GPIO applications to more complex scenarios involving sensors, audio, and graphical interfaces. 


### Chapter 04, Employing Third-party Libraries in ESP32 Projects
This chapter focuses on the integration of third-party libraries into ESP-IDF projects, emphasizing the practical advantages of leveraging external libraries to enhance development efficiency and address specific project needs. The author underscores the financial and temporal benefits of incorporating established libraries, reducing the necessity for in-house development and ensuring compatibility with market requirements. Various methods of integrating third-party libraries are explored, including defining library dependencies for download from the IDF Component Registry, cloning from GitHub, and directly adding libraries as IDF components. The chapter introduces several **Free and Open Source Software** (**FOSS**) libraries, such as LittleFS, nlohmann/json, Miniz, FlatBuffers, LVGL (Light and Versatile Embedded Graphics Library), ESP-IDF Components library (UncleRus), and frameworks by Espressif Systems. 

In-depth discussions and examples showcase the utility of each library, elucidating their applications in ESP32 projects. The chapter not only provides insights into incorporating specific libraries but also it helps in imparting a broader understanding of the diverse integration methods available. The practical examples serve as a valuable resource for developers seeking to efficiently implement third-party libraries in their ESP32 projects, laying the groundwork for more streamlined and feature-rich IoT applications. 

#### Key Insight Points:
- **Strategic Use of Third-Party Libraries**: The chapter emphasizes the strategic use of third-party libraries in ESP-IDF projects to optimize development resources. It underscores the importance of minimizing in-house development to save time and costs while meeting specific project requirements. 
- **Integration Methods**: Developers gain insights into various methods of integrating third-party libraries, ranging from defining dependencies for downloads to cloning from GitHub. The chapter provides a comprehensive understanding of these methods, allowing developers to choose the most suitable approach for their projects. 
- **FOSS Libraries Overview**: A detailed exploration of **Free and Open Source Software** (**FOSS**) libraries is presented. LittleFS is introduced as an alternative to SPIFFS, nlohmann/json as a modern C++ JSON library, Miniz for data compression, FlatBuffers for efficient serialization, and LVGL for creating graphical interfaces. These libraries cover a wide range of functionalities applicable to ESP32 projects. 
- **ESP-IDF Components Library**: The inclusion of the ESP-IDF Components library by UncleRus is highlighted, showcasing its relevance for ESP32 developers. The library provides a collection of device drivers, contributing to the versatility of ESP32 projects. 
- **Frameworks by Espressif Systems**: The chapter discusses important frameworks by Espressif Systems, offering developers a head-start and simplifying the initiation of new ESP32 projects. Understanding these frameworks provides valuable insights for efficient project development. 
- **Application of Integration Methods**: Practical examples demonstrate the application of different integration methods, empowering developers to incorporate third-party libraries seamlessly into their ESP32 projects. The showcased examples serve as practical guidance for future projects, fostering effective library utilization. 


### Chapter 05, Project – Audio Player
Real-World Application of Knowledge: Chapter 5 marks a pivotal moment in the book, transitioning from theoretical concepts to practical application. Drawing on the foundational understanding of IoT development, ESP32 peripherals, and third-party libraries, this chapter provides a hands-on experience by guiding readers through the creation of a fully-functional audio player. The project not only reinforces the acquired knowledge but also allows developers to apply their skills in a comprehensive manner. 

Comprehensive Project Lifecycle: The chapter takes readers through the entire lifecycle of developing an audio player, covering crucial aspects such as defining features, designing the solution architecture, implementing the project, conducting thorough testing, addressing troubleshooting challenges, and exploring opportunities for new features. The emphasis on UI/UX design underscores the importance of creating a user-friendly interface, showcasing how developers can optimize the **Graphical User Interface** (**GUI**) to enhance the overall product. As the first reference project in the book, this chapter serves as a capstone for the initial part, paving the way for the upcoming chapters that delve into the development of connected ESP32 products on cloud systems.

#### Key Insight Points:
- **Hands-On Application**: Chapter 5 focuses on the practical application of theoretical knowledge gained in earlier chapters. Readers engage in a real-world project, creating an audio player that incorporates various aspects of ESP32 development, including peripherals, third-party libraries, and UI/UX design. 
- **Full Project Lifecycle**: The chapter guides readers through the entire lifecycle of developing an IoT project. From defining features to designing the solution architecture, coding, testing, and troubleshooting, readers gain a comprehensive understanding of what it takes to bring an ESP32 project to fruition. 
- **UI/UX Importance**: Emphasizing the significance of **User Interface** (**UI**) and **User Experience** (**UX**) design, the project underscores how a well-designed GUI can enhance the functionality and appeal of an IoT product. This aligns with the broader industry trend of prioritizing user-friendly interfaces for IoT devices. 
- **Skill Application**: By developing a complete audio player, developers get hands-on experience applying their knowledge and skills. This practical approach reinforces learning and prepares readers for more complex projects in subsequent chapters. 
- **Transition to Cloud Systems**: The completion of this project marks the end of the first part of the book. Readers are now primed for the next phase, which explores the development of connected ESP32 products on cloud systems, indicating a progression from local device development to broader IoT ecosystem integration. 


### Chapter 06, Using Wi-Fi Communication for Connectivity
Chapter 6, "Using Wi-Fi Communication for Connectivity," delves into the essential aspect of communication in ESP32 development—Wi-Fi connectivity. As Wi-Fi stands as a cornerstone in IoT, the chapter guides readers through the process of connecting ESP32 to a local Wi-Fi network, unlocking the vast realm of IoT possibilities. ESP-IDF's robust support for TCP/IP applications is explored, providing a foundation for communication with servers and other connected devices. Practical examples are presented, illustrating Wi-Fi connectivity basics and the implementation of popular IoT protocols, including MQTT (Message Queue Telemetry Transport) and REST (Representational State Transfer) services over TCP/IP. The chapter covers topics such as Wi-Fi connection, ESP32 provisioning on a Wi-Fi network, MQTT communication with a central broker, running a RESTful server on ESP32, and consuming RESTful services. 

In this chapter, readers gain insights into the crucial role of Wi-Fi as the networking infrastructure for ESP32, enabling device connectivity to the internet. Practical demonstrations showcase ESP32's capabilities in establishing Wi-Fi connections, provisioning in the absence of configured Wi-Fi networks, and employing MQTT for many-to-many IoT communication. Additionally, the chapter explores REST as another common method for IoT communication, detailing the development of RESTful server applications on ESP32 and its use as a client consuming RESTful services. The upcoming chapter promises to expand the readers' knowledge by elucidating how to develop secure applications on ESP32, addressing the vital aspect of cybersecurity in IoT devices.

#### Key Insight Points:
- **Wi-Fi Connectivity Basics**: The chapter emphasizes the pivotal role of Wi-Fi in ESP32 development, serving as the primary wireless standard for communication. Readers gain a comprehensive understanding of connecting ESP32 to a local Wi-Fi network, a fundamental step enabling broader IoT capabilities. 
- **TCP/IP Application Development**: ESP-IDF's support for TCP/IP applications is highlighted, providing the necessary software foundation for developing applications that leverage the internet protocol suite. This support is crucial for communication with servers and other devices on the network. 
- **MQTT for Many-to-Many Communication**: Practical examples showcase the implementation of MQTT, a powerful many-to-many IoT communication protocol. The chapter guides readers on setting up an MQTT broker, such as Mosquitto, and developing ESP32 applications capable of subscribing to and publishing messages on MQTT topics. 
- **RESTful Communication**: The chapter introduces REST as another common IoT communication method. Readers learn how to run a RESTful server on ESP32 and utilize ESP32 as a client to consume RESTful services. Practical applications demonstrate the versatility of ESP32 in handling REST-based communication. 
- **Further Reading Resources**: The chapter provides additional resources for further exploration, allowing readers to delve deeper into the basics of modern networking and the TCP/IP family of protocols, including REST and MQTT. This encourages continuous learning beyond the chapter's content. 


### Chapter 07, ESP32 Security Features for Production-Grade devices
The chapter delves into the critical realm of IoT security, emphasizing the imperative of a "security-first" approach in designing internet-facing solutions, particularly in the context of IoT products. With IoT devices often reaching end users lacking a profound understanding of security, the ESP32 platform stands out for its robust hardware support and integration of industry-standard encryption libraries within ESP-IDF. The chapter focuses on the essentials of developing production-grade IoT devices, providing examples of secure firmware updates and communication techniques. Utilizing the ESP RainMaker platform by Espressif Systems, the chapter offers insights into securing IoT solutions for market deployment. 

Security considerations span the entire IoT solution, encompassing connected devices, backend services, and client applications. The discussion covers ESP32 security features, including Secure Boot and flash encryption, crucial for safeguarding firmware. The chapter introduces **Over-the-Air** (**OTA**) updates as a pivotal feature for IoT products, emphasizing the need for continuous monitoring of devices in the field. Two distinct examples of OTA updates are presented, highlighting the significance of real-world monitoring solutions. ESP RainMaker serves as a demonstrative platform, showcasing the comprehensive features expected in an IoT platform for developing practical projects, further enhancing the understanding of cybersecurity in IoT product development. 

#### Key Insight Points:
- **Security-First Approach**: The chapter advocates for a "security-first" mindset in designing IoT solutions, recognizing the vulnerability of internet-facing devices and the potential lack of cybersecurity awareness among end users. 
- **ESP32 Security Features**: It explores the security features of the ESP32 platform, emphasizing the hardware support and integration of encryption libraries within ESP-IDF to provide a robust foundation for IoT security. 
- **Secure Firmware Updates**: The significance of **Over-the-Air** (**OTA**) updates is highlighted as a crucial feature for IoT products, ensuring the ability to deploy secure and timely firmware updates to devices in the field. 
- **Secure Boot and Flash Encryption**: The chapter delves into the importance of Secure Boot and flash encryption in ESP32 devices, essential components for safeguarding firmware integrity and preventing unauthorized access. 
- **ESP RainMaker Platform**: Practical examples are demonstrated using the ESP RainMaker platform by Espressif Systems, offering insights into developing secure IoT projects and showcasing the features expected from a comprehensive IoT platform. 
- **Real-World Monitoring**: The need for continuous monitoring of IoT devices in the field is emphasized, with practical examples illustrating the importance of vigilance and proactive security practices. 
- **ESP Insights and Monitoring Solutions**: The chapter introduces ESP Insights as an example of a monitoring solution, showcasing the role of monitoring in ensuring the ongoing security and performance of deployed IoT devices. 
- **Holistic Security Approach**: Security considerations extend across the entire IoT solution, covering connected devices, backend services, and client applications, highlighting the need for a comprehensive and integrated security strategy. 
- **Cryptographic Fundamentals**: The chapter suggests a background understanding of cryptography fundamentals for readers to follow the examples effectively, providing further reading resources for those seeking to enhance their knowledge in this area.


### Chapter 08, Connecting to Cloud Platforms and Using Services
Chapter 8 delves into the crucial aspect of cloud computing as an enabler for IoT, emphasizing the significance of cloud connectivity for enhancing the capabilities of ESP32 devices. While ESP32 devices excel in local network interactions, the chapter underscores the necessity of accessing devices remotely from anywhere globally and leveraging cloud technologies for data analysis and insights. The integration of ESP32 with **Amazon Web Services** (**AWS**) IoT Core is explored, demonstrating the process of creating IoT things, configuring credentials, and sending sensor data to AWS IoT Core over MQTT. The chapter extends into the realm of cloud services, showcasing the visualization of IoT data using Grafana and integrating ESP32 with Amazon **Alexa Voice Services** (**AVS**) for voice-assisted interactions. 

The narrative highlights the pivotal role of cloud platforms in IoT products, making benefits such as remote access, analytics, and visualization readily available. Practical examples, including an AWS-connected light sensor and integration with Grafana for time-series data visualization, provide a hands-on understanding of cloud integration. Furthermore, the chapter explores voice assistants as an alternative user interface, illustrating the integration of an IoT sensor with Amazon Alexa through the creation of a smart home skill. The chapter serves as a comprehensive guide, showcasing end-to-end IoT product development skills, from sensor readings to cloud connectivity. The upcoming chapter promises a practical application of these skills in a smart home project involving ESP32 devices communicating with each other and the cloud.

#### Key Insight Points:
- **IoT and Cloud Synergy**: The chapter underscores the symbiotic relationship between IoT and cloud computing. While ESP32 devices excel in local interactions, the integration with cloud platforms, specifically AWS IoT Core, unlocks the potential for remote accessibility, data analysis, and enhanced functionalities. 
- **AWS Integration Steps**: The practical guide walks through the steps of integrating ESP32 with AWS IoT Core. It covers the creation of IoT things, configuration of credentials, and the use of MQTT for sending sensor data to the AWS cloud, showcasing the seamless connection between ESP32 devices and the AWS infrastructure. 
- **Data Visualization with Grafana**: The chapter introduces Grafana as a powerful tool for visualizing time-series IoT data. Through AWS IoT Core rules, data from ESP32 devices is forwarded to a managed Timestream database, and Grafana is configured to display the data, providing insights through graphical representations. 
- **Voice Interaction with Alexa**: Recognizing the prevalence of voice assistants in IoT, the chapter demonstrates the integration of ESP32 devices with Amazon **Alexa Voice Services** (**AVS**). By creating a smart home skill and using a lambda function as a bridge, ESP32 devices can respond to voice commands, showcasing a practical implementation of voice interactions in IoT products. 
- **End-to-End IoT Development**: The chapter contributes to a holistic understanding of IoT product development, covering sensor readings, local network connectivity, and cloud integration. It serves as a bridge between local device capabilities and the broader capabilities offered by cloud platforms, emphasizing the importance of cloud services in realizing the full potential of IoT solutions. 


### Chapter 09, Project - Smart home
Chapter 9 delves into the creation of a comprehensive smart home solution on the ESP RainMaker platform, showcasing the integration of various devices to operate seamlessly within a single product. The chapter emphasizes the complexity of IoT product development, where multiple hardware and software components must harmonize for an optimal customer experience. By constructing a smart home solution, the chapter provides a practical example of IoT in action, incorporating sensors, actuators, and entertainment systems within the same local network. The discussion spans the entire development process, from defining the feature list and solution architecture to implementation, testing, troubleshooting, and considering potential new features. It serves as a valuable learning opportunity for IoT developers to gain hands-on experience in building integrated solutions. 

Throughout the chapter, two distinct devices, a plug, and a multisensor, are developed and integrated into the RainMaker platform, offering cloud connectivity for the devices. The mobile application associated with RainMaker facilitates device provisioning and management, with additional support for voice services like Alexa and Google Assistant. The testing phase involves validating the functionality using the Alexa mobile application after linking RainMaker and Alexa accounts. Overall, the chapter provides insights into the intricacies of designing a smart home solution and sets the stage for the exploration of machine learning applications on the ESP32 in the subsequent chapter. 

#### Key Insight Points:
- **IoT Product Development Complexity**: The chapter underscores the intricate nature of IoT product development, highlighting the need for multiple hardware and software components to seamlessly work together. It emphasizes the importance of gaining practical experience in integrating these components for optimal customer experiences. 
- **Smart Home Solution**: The development of a smart home solution serves as a concrete example of IoT in action. The solution incorporates various devices, including sensors, actuators, and entertainment systems, operating within the same local network. The chapter covers the entire development lifecycle, offering insights into defining features, creating a solution architecture, implementation, testing, troubleshooting, and potential feature enhancements. 
- **ESP RainMaker Platform**: The integration of devices into the ESP RainMaker platform demonstrates the capabilities of cloud connectivity in IoT solutions. The platform facilitates provisioning and management of devices through a mobile application, showcasing its practical utility in real-world applications. Additionally, the platform supports voice services like Alexa and Google Assistant, expanding the scope of user interaction with IoT devices. 
- **Comprehensive Testing and Troubleshooting**: The chapter emphasizes the importance of thorough testing and troubleshooting in the development process. The validation of device functionality using the Alexa mobile application after linking RainMaker and Alexa accounts showcases a robust approach to ensuring the reliability of the smart home solution. 
- **Foundation for Machine Learning Exploration**: The chapter sets the stage for the exploration of machine learning applications on the ESP32 in the next chapter. This indicates a progression in the complexity and capabilities of IoT projects, introducing developers to advanced functionalities beyond basic device integration. 


### Chapter 10, Machine Learning with ESP32
This chapter delves into the intricate realm of **Machine Learning** (**ML**) with a specific focus on implementing it in **Internet of Things** (**IoT**) projects using the ESP32. Acknowledging the multifaceted nature of ML, the chapter sets a pragmatic goal of instructing readers on applying ML techniques in IoT endeavors, emphasizing the challenges posed by the resource constraints of IoT devices. The concept of tinyML, tailored for constrained devices like IoT hardware, becomes pivotal in navigating these challenges. 

The chapter unfolds with a comprehensive exploration of ML basics, elucidating the stages in the tinyML pipeline: data collection, ML model design and optimization, and inference. **TensorFlow Lite for Microcontrollers** (**TFLM**) emerges as a crucial framework within TensorFlow, equipped with tools and libraries optimized for constrained IoT devices. The practical application of tinyML is demonstrated through the development of a speech recognition application on the ESP32, employing models such as WakeNet and MultiNet provided by Espressif for voice applications. 

#### Key Insight Points:
- **tinyML for Constrained Devices**: The chapter emphasizes the importance of tinyML, a field of machine learning tailored for constrained devices like IoT hardware.It highlights the challenges posed by the resource constraints of IoT devices, including limited processing capabilities, memory, and power. 
- **TensorFlow Lite for Microcontrollers (TFLM)**: **TensorFlow Lite for Microcontrollers** (**TFLM**) is introduced as a crucial framework within TensorFlow, specifically designed to optimize and deploy ML models on constrained IoT devices.TFLM is presented as a valuable tool equipped with essential libraries and capabilities for developing ML applications in resource-constrained environments. 
- **Practical Application of tinyML on ESP32**: The chapter provides practical insights into applying tinyML concepts on the ESP32, a popular IoT platform. 
A speech recognition application is developed as a hands-on example, showcasing the implementation of wake-word activation and voice command detection using Espressif's WakeNet and MultiNet models. 
- **Advances in MCU and AI/ML Algorithms**: **Advances in microcontroller units** (**MCUs**) and AI/ML algorithms are discussed, highlighting the progress that enables the deployment of small ML models on IoT devices.This progress empowers developers to perform ML inferences directly on IoT devices without the need for extensive backend systems or cloud resources. 
- **Edge Impulse as an ML Platform**: The chapter sets the stage for the next chapter by mentioning Edge Impulse, an ML platform specializing in IoT devices. 
Edge Impulse is positioned as a platform that provides **ML operations** (**MLOps**) features, allowing for the effective management of ML models in production on IoT devices. 


### Chapter 11, Developing on Edge Impulse
Chapter 11, "Developing on Edge Impulse," delves into the intricacies of machine learning application development on ESP32 using the Edge Impulse platform. In the realm of TinyML, the chapter underscores the multifaceted process involved, including data collection, preprocessing, model development, optimization, deployment, performance tracking, and maintenance. Drawing a parallel to DevOps in traditional software projects, the concept of **Machine Learning Operations** (**MLOps**) is introduced, emphasizing the need for platforms that facilitate the end-to-end management of machine learning applications, incorporating data and model versioning. Edge Impulse emerges as a leading MLOps platform for TinyML, offering features such as a web-based development environment (Edge Impulse Studio), RESTful API, device SDKs for data acquisition, an Inference SDK for running models on IoT devices, and a command-line interface for managing devices without direct internet connections. The chapter guides readers through the practical application of Edge Impulse Studio, covering aspects like cloning projects, generating models, and running them on ESP32. 

Throughout the chapter, readers gain insights into the essential components of Edge Impulse, including its online development environment, API functionalities, and SDKs. The practical demonstration involves cloning an existing ML project from Edge Impulse's repository, utilizing Edge Impulse Studio to build the project, downloading the Edge Impulse C++ library containing the ML model, and integrating this library into an ESP-IDF project. The detailed exploration includes discussions on the application's intricacies, illustrating how the model makes inferences on audio data captured by the devkit's microphone. The chapter sets the stage for applying the knowledge gained in the final chapter, solidifying the understanding of TinyML concepts learned throughout the book. 

#### Key Insight Points:
- **MLOps for TinyML**: The chapter introduces the concept of Machine Learning Operations (MLOps) in the context of TinyML. It emphasizes the importance of managing the complete life cycle of machine learning applications, covering various stages from data collection to model deployment, tracking performance, and ongoing maintenance. 
- **Edge Impulse Features**: Edge Impulse is highlighted as a leading MLOps platform for TinyML, offering a range of features to streamline the development process. Key features include Edge Impulse Studio, a web-based environment for managing ML projects; a RESTful API for remote access; device SDKs for data acquisition; Inference SDK for running models on IoT devices; and a command-line interface for managing devices with limited internet connectivity. 
- **Practical Application**: The chapter provides a hands-on demonstration of using Edge Impulse Studio to clone an existing ML project, generate models, and run them on ESP32. The step-by-step guide covers essential aspects such as project cloning, model building, library downloading, and integration into an ESP-IDF project. The practical example involves making inferences on audio data from a devkit's microphone, showcasing the real-world application of Edge Impulse in the TinyML landscape. 
- **Transition to the Final Chapter**: The chapter serves as a bridge to the final chapter of the book, setting the stage for the culmination of TinyML concepts learned throughout the book. It prepares readers for the design and development of another project, allowing them to solidify their understanding and practical skills in the TinyML domain. 


### Chapter 12, Project – Baby Monitor
In the concluding chapter, "Project – Baby Monitor," the book presents a final project that integrates machine learning into an ESP32-S3 to detect baby cries. Employing the Edge Impulse platform for ML capabilities and ESP RainMaker for cloud connectivity, this project provides a practical demonstration of designing a connected machine learning product. The chapter covers essential aspects such as defining the feature list, outlining the solution architecture, implementing the project, conducting tests, troubleshooting, and exploring potential new features. The integration with ESP RainMaker adds a cloud component to the IoT solution, showcasing the real-world complexity and challenges often encountered in IoT product development, particularly in terms of memory usage, which is addressed by utilizing SPIRAM. 

In reflection, the author encourages readers to explore further by trying other chips from Espressif Systems, expanding their knowledge and capabilities in the vast field of IoT. The book concludes with a sense of accomplishment, inviting readers to continue their ESP32 journey, emphasizing the joy of solving real-world problems with ESP32 and expressing gratitude for the shared learning experience throughout the book's examples.

#### Key Insight Points:
- **Practical Integration of Machine Learning in IoT**: The chapter demonstrates the practical integration of machine learning into an ESP32-S3 for a specific application – detecting baby cries. It underscores the effectiveness of machine learning in audio analysis and classification, highlighting the success of Edge Impulse as a suitable ML platform for constrained devices like ESP32-S3. 
- **Challenges and Real-World Problem Solving**: The project highlights the challenges often faced in IoT product development, such as memory constraints. The author addresses the issue by employing SPIRAM, offering readers hands-on experience in overcoming practical obstacles. This emphasizes the importance of addressing real-world challenges in IoT projects. 
- **Integration with Cloud Services**: The inclusion of ESP RainMaker in the project emphasizes the significance of cloud connectivity in IoT solutions. Readers gain insights into integrating their projects with cloud platforms, showcasing the complexity and considerations involved in building comprehensive IoT systems. 
- **Encouragement for Further Exploration**: The author encourages readers to explore beyond the book's content, suggesting trying other chips from Espressif Systems and delving into the broader field of IoT. This reflects the ongoing nature of learning in IoT development and the need for continuous exploration to stay updated with new technologies and standards. 
- **Reflection and Shared Learning Experience**: The concluding remarks express the author's enjoyment of solving real-world problems with ESP32 and convey gratitude for the readers who joined in the learning journey. The collaborative and shared learning experience is acknowledged, creating a sense of accomplishment and community among those who have engaged with the book's examples.




> If you feel this book is for you, get your [copy](https://www.amazon.in/Developing-IoT-Projects-ESP32-production-grade-ebook/dp/B0BM9LQXMD) today! <img alt="Coding" height="15" width="35"  src="https://media.tenor.com/ex_HDD_k5P8AAAAi/habbo-habbohotel.gif">



With the following software and hardware list you can run all code files present in the book.

## Software and hardware list

| Software required    | Link to the software    | Hardware specifications    | OS required    |
|:---:  |:---:  |:---:  |:---:  |
| Git client (latest) | [https://git-scm.com/downloads] (https://git-scm.com/downloads) | PC/laptop | Any|
| VS Code (latest version)  | [https://code.visualstudio.com/download](https://code.visualstudio.com/download) | PC/laptop | Any|
|   ESP-IDF (>=4.4.4 and < 5)  | [https://github.com/espressif/esp-idf](https://github.com/espressif/esp-idf) | PC/laptop | Any|
| Python3 (>= 3.10.11 and < 3.11) | [https://www.python.org/downloads/](https://www.python.org/downloads/) | PC/laptop | Any|
| SquareLine Studio (>=1.1.1)  | [https://squareline.io/downloads](https://squareline.io/downloads) | PC/laptop | Any|
| Curl (>8) | [https://curl.se/download.html](https://curl.se/download.html) | PC/laptop | Any|
| Mosquitto (>2) | [https://mosquitto.org/download/](https://mosquitto.org/download/) | PC/laptop | Any|
| ESP SoftAP Provisioning (latest) | Mobile App stores | Mobile devices | Any|
| Pyenv (latest) | [https://github.com/pyenv/pyenv](https://github.com/pyenv/pyenv) | PC/laptop | Any|
| ESP Rainmaler (latest)| Mobile App stores | Mobile devices | Any|
| Openssl (latest) | [https://www.openssl.org/community/binaries.html](https://www.openssl.org/community/binaries.html) | PC/laptop | Any|
| Amazon Alexa (latest) | Mobile App stores | Mobile devices | Any|

## Detailed installation steps (software-wise)
Installation instructions:
1. Git client:
   - Follow the steps as given in the download page for your specific platform (MacOS, Windows, Linux/Unix)
2. Visual Studio Code
   - Follow the steps as given in the download page for your specific platform (MacOS, Windows, Linux/Unix)
3. Python3:
   - Download and run the platform-specific installer
4. ESP-IDF 4.4.4 (You can follow the Getting Started guide or clone the GitHub repository)
   - Create a new directory with name “esp” in your home directory.
   - Clone the repository (git clone --recursive --branch v4.4.4 [https://github.com/espressif/esp-idf](https://github.com/espressif/esp-idf))
   - Run the install script for your platform
   - For Windows users, there are binary installers for easy setup here: [https://docs.espressif.com/projects/esp-idf/en/latest/esp32/get-started/windows-setup.html](https://docs.espressif.com/projects/esp-idf/en/latest/esp32/get-started/windows-setup.html)
5. SquareLine Studio
    - Download and run the platform-specific installer
6. Curl
    - Download and run the platform-specific installer
7. Mosquitto
    - Download and run the platform-specific installer
8. Pyenv
    - Follow the steps as given in the GitHub repository for your specific platform (MacOS, Windows, Linux/Unix)
9. OpenSSL: It doesn’t provide direct binaries. See the 3rd-party providers as listed in the wiki: [https://wiki.openssl.org/index.php/Binaries](https://wiki.openssl.org/index.php/Binaries)
10. ESP SoftAP Provisioning: Install from the mobile app store for your specific platform (Android, iOS)
11. ESP Rainmaler: Install from the mobile app store for your specific platform (Android, iOS)
12. Amazon Alexa: Install from the mobile app store for your specific platform (Android, iOS)

## Know more on the Discord server <img alt="Coding" height="25" width="32"  src="https://cliply.co/wp-content/uploads/2021/08/372108630_DISCORD_LOGO_400.gif">
You can get more engaged on the Discord server for more latest updates and discussions in the community at [Discord](https://discord.gg/3Q9egBjWVZ)

## Download a free PDF <img alt="Coding" height="25" width="40" src="https://emergency.com.au/wp-content/uploads/2021/03/free.gif">

_If you have already purchased a print or Kindle version of this book, you can get a DRM-free PDF version at no cost. Simply click on the link to claim your free PDF._
[Free-Ebook](https://packt.link/free-ebook/9781803237688) <img alt="Coding" height="15" width="35"  src="https://media.tenor.com/ex_HDD_k5P8AAAAi/habbo-habbohotel.gif">

We also provide a PDF file that has color images of the screenshots/diagrams used in this book at [GraphicBundle](https://packt.link/gbp/9781803237688) <img alt="Coding" height="15" width="35"  src="https://media.tenor.com/ex_HDD_k5P8AAAAi/habbo-habbohotel.gif">


## Get to know the Author
_Vedat Ozan Oner_ is an IoT product developer and software architect, with an excellent blend of technical knowledge and experience. During his career, he has contributed to several IoT projects in different roles, which allowed him to discover all key aspects of developing successful IoT products in highly competitive markets. Vedat has a bachelor's degree in METU/computer engineering and holds several industry-recognized credentials and qualifications, including PMP®, ITIL®, and AWS Certified Developer.
Vedat started his limited company, Mevoo Ltd, in London in 2018 to provide consultancy services to his clients as well as develop his own IoT products. He still lives in London with his family.

## Other Related Books
- [Architectural Patterns and Techniques for Developing IoT Solutions](https://www.packtpub.com/product/architectural-patterns-and-techniques-for-developing-iot-solutions/9781803245492)
- [Terraform Cookbook – Second Edition](https://www.packtpub.com/product/terraform-cookbook-second-edition/9781804616420)


