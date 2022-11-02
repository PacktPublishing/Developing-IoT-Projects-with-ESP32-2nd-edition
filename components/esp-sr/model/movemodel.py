import io
import os
import argparse
import shutil
def calculate_total_size(folder_path):
    total_size = 0
    for file_name in os.listdir(folder_path):
        path = os.path.join(folder_path, file_name)
        if os.path.isdir(path):
            total_size = total_size + calculate_total_size(path)
        if os.path.isfile(path):
            total_size = total_size + os.path.getsize(path)
    return total_size

if __name__ == '__main__':
    # input parameter
    parser = argparse.ArgumentParser(description='Model generator tool')
    parser.add_argument('-d1', '--project_path')
    parser.add_argument('-d2', '--model_path')
    args = parser.parse_args()

    sdkconfig_path = args.project_path + '/sdkconfig'
    model_path = args.model_path + '/model'

    print(sdkconfig_path)
    print(model_path)

with io.open(sdkconfig_path, "r") as f:
    WN_STRING = ''
    MN_STRING = ''
    for label in f:
        label = label.strip("\n")
        if 'CONFIG_SR_WN' in label and label[0] != '#':
            WN_STRING += label
        if 'CONFIG_SR_MN' in label and label[0] != '#':
            MN_STRING += label

wakenet_model = []
if "CONFIG_SR_WN_WN7Q8_XIAOAITONGXUE" in WN_STRING and len(wakenet_model) < 2:
    wakenet_model.append('xiaoaitongxue7q8')
if "CONFIG_SR_WN_WN7_XIAOAITONGXUE" in WN_STRING and len(wakenet_model) < 2:
    wakenet_model.append('xiaoaitongxue7')
if "CONFIG_SR_WN_WN7Q8_HILEXIN" in WN_STRING and len(wakenet_model) < 2:
    wakenet_model.append('hilexin7q8')
if "CONFIG_SR_WN_WN8_HILEXIN" in WN_STRING and len(wakenet_model) < 2:
    wakenet_model.append('hilexin8')
if "CONFIG_SR_WN_WN8_ALEXA" in WN_STRING and len(wakenet_model) < 2:
    wakenet_model.append('alexa8')
if "CONFIG_SR_WN_WN8Q8_HIESP" in WN_STRING and len(wakenet_model) < 2:
    wakenet_model.append('hiesp8q8')
if "CONFIG_SR_WN_WN8_HIESP" in WN_STRING and len(wakenet_model) < 2:
    wakenet_model.append('hiesp8')

multinet_model = []
if "CONFIG_SR_MN_CN_MULTINET3_SINGLE_RECOGNITION" in MN_STRING and len(multinet_model) < 2:
    multinet_model.append('mn3cn')
elif "CONFIG_SR_MN_CN_MULTINET4_SINGLE_RECOGNITION" in MN_STRING and len(multinet_model) < 2:
    multinet_model.append('mn4cn')
elif "CONFIG_SR_MN_CN_MULTINET4_5_SINGLE_RECOGNITION" in MN_STRING and len(multinet_model) < 2:
    multinet_model.append('mn4_5cn')

if "CONFIG_SR_MN_EN_MULTINET5_SINGLE_RECOGNITION_QUANT8" in MN_STRING and len(multinet_model) < 2:
    multinet_model.append('mn5q8en')
elif "CONFIG_SR_MN_EN_MULTINET5_SINGLE_RECOGNITION" in MN_STRING and len(multinet_model) < 2:
    multinet_model.append('mn5en')

print(wakenet_model)
print(multinet_model)

target_model = model_path + '/target'
if os.path.exists(target_model):
    shutil.rmtree(target_model)
os.makedirs(target_model)
if len(wakenet_model) != 0:
    for wakenet_model_item in wakenet_model:
        shutil.copytree(model_path + '/wakenet_model/' + wakenet_model_item, target_model+'/'+wakenet_model_item)
if len(multinet_model) != 0:
    for multinet_model_item in multinet_model:
        shutil.copytree(model_path + '/multinet_model/' + multinet_model_item, target_model+'/'+multinet_model_item)

# os.system("cp %s %s" % (wakenet_model+'/_MODEL_INFO_', target_model))

total_size = calculate_total_size(target_model)
print("Recommended model partition size: ", str(int((total_size / 1024 + 900) / 4 ) * 4) + 'KB')
