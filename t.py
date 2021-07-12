import re
import sys
def filter_log_file(source, outputdir, idx, funcname):
    filename = "{}{}{}/log.txt".format(outputdir, source, idx)
    res = []
    start_record = False
    with open(filename, 'r') as file1:
        lines = file1.readlines()
        for line in lines:
            if ("single infer: {}\n".format(funcname) == line) or ("single infer: {}.{}\n".format(source.capitalize(), funcname) == line):
                start_record = True
                continue
            if start_record:
                if re.search("delta\[pos_verify_update_env\]:.+", line):
                    p = re.compile('delta\[pos_verify_update_env\]:')
                    data = p.sub('', line)
                    res.append(float(data))
    return res

def handle_data(data):
    total_num = 100
    if len(data) < total_num:
        print("need more data")
        exit(0)
    interval = int(len(data)/total_num)
    iteri=0
    interval_iter = 0
    result=[]
    interval_sum=0.0
    for d in data:
        interval_iter += 1
        if interval_iter >= interval:
            iteri += 1
            if iteri >= 100:
                break;
            interval_iter = 0
            result.append(interval_sum/interval)
            interval_sum=0.0
        interval_sum = interval_sum + d
    return result

import numpy as np
import matplotlib.pyplot as plt

def build_figure_aux(outputdir, figure_config):
    x=np.arange(10,1000,10)
    for entry in figure_config:
        result = handle_data(filter_log_file(entry['source'], outputdir, entry['idx'], entry['funcname']))
        plt.plot(x,result,'-',label=entry['name'])
    plt.xlabel('#Weakening')
    plt.ylabel('Time(s)')
    plt.tick_params(axis='both',which='major',labelsize=10)
    plt.legend(loc=2, bbox_to_anchor=(1.05,1.0),borderaxespad = 0.)
    plt.yscale('log')
    plt.show()

import json
def build_figure5(config_file):
    with open(config_file) as f:
        config = json.load(f)
        build_figure_aux("_" + config['outputprefix'], config['figure'])

