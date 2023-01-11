from flask import Flask, request, jsonify, make_response
app = Flask(__name__)

sensor_config = {"name": "sensor-0", "enabled": True}
sensor_data = {}

@app.route('/config', methods=['GET', 'PUT'])
def getConfig():
    if request.method == 'GET':
       return jsonify(sensor_config)
    
    # PUT
    sensor_config.update(request.get_json(force=True))
    return 'done'

@app.route('/data', methods=['GET', 'PUT'])
def getData():
    if request.method == 'GET':
       return jsonify(sensor_data)
    
    # PUT
    sensor_data.update(request.get_json(force=True))
    return 'done'
