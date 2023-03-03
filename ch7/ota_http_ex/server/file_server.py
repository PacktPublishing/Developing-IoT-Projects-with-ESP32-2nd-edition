import ssl 
from flask import Flask, request, make_response

app = Flask(__name__)

@app.route('/info', methods=['GET'])
def otaInfo():
    with open('static/info.txt') as f:
        return f.readline().strip('\n')
