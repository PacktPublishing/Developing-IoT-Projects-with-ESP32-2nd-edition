
# Rainmaker installation

Note: you can skip the Rainmaker installation if you've already worked on the Rainmaker OTA update example.

You can clone the Rainmaker library and tools here: https://github.com/espressif/esp-rainmaker


```
# clone the repo (or use the copy coming with the book repo, Developing-IoT-Projects-with-ESP32-2nd-edition/ch7/common/esp-rainmaker/cli)
$ git clone --recurse-submodules https://github.com/espressif/esp-rainmaker.git
$ cd esp-rainmaker
$ git submodule update --init --recursive

# create a virtual environment and install requirements
$  pyenv virtualenv  3.9.18 rmaker_cli
$  pyenv local rmaker_cli 
$  pip install --upgrade pip
$  pip install -r requirements.txt 

# run the tool to sign-up and login
$  export IDF_PATH=$HOME/esp/v5.2.2/esp-idf/
$  ./rainmaker.py signup
$  ./rainmaker.py signup <your_email>
$  ./rainmaker.py login <your_email>
$  ./rainmaker.py login 
```

See this if any error after installation:
https://stackoverflow.com/questions/72441758/typeerror-descriptors-cannot-not-be-created-directly

