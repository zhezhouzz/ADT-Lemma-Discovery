import json
import subprocess
import sys
import argparse
import os

verbose=False

def parse_config(table_file):
    with open(table_file) as f:
        table4 = json.load(f)
        datadir = table4['datadir']
        outputprefix = table4['outputprefix']
        sourcepostfix = table4['sourcepostfix']
        assertioninfix = table4['assertioninfix']
        assertionpostfix = table4['assertionpostfix']
        benchmarks = table4['benchmarks']
    return datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks

def run_table4_consistent(table_file):
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        print("working on {}".format(adt))
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            source_file = datadir + "/" + source + sourcepostfix
            assertion_file = datadir + "/" + source + assertioninfix + str(idx) + assertionpostfix
            output_dir = outputprefix + source + str(idx)
            log_file_name = "consistent_log.txt"
            arguments = []
            if 'arguments' in info:
                arguments = info['arguments']
            cmd = ["dune", "exec", "--", "main/main.exe", "infer", "consistent",
                   source_file, assertion_file, output_dir] + arguments
            with open(log_file_name, "w") as log_file:
                if verbose:
                    print(" ".join(cmd))
                subprocess.run(cmd, stdout=log_file)
                subprocess.run(["mv", log_file_name, "_" + output_dir + "/" + log_file_name])

def run_table4_weakening(table_file, shortbench, longbench, timebound):
    if not (shortbench or longbench):
        shortbench = True
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        print("working on {}".format(adt))
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            source_file = datadir + "/" + source + sourcepostfix
            assertion_file = datadir + "/" + source + assertioninfix + str(idx) + assertionpostfix
            output_dir = outputprefix + source + str(idx)
            long_time = False
            if 'weakening_long_time' in info:
                long_time = info['weakening_long_time']
            if ((not shortbench) and (not long_time)) or ((not longbench) and (long_time)):
                if verbose:
                    print("skip")
                continue
            if timebound > 0:
                arguments = ["-tb", "{}".format(timebound)]
            cmd = ["dune", "exec", "--", "main/main.exe", "infer", "weakening", output_dir] + arguments
            log_file_name = "log.txt"
            with open(log_file_name, "w") as log_file:
                if verbose:
                    print(" ".join(cmd))
                subprocess.run(cmd, stdout=log_file)
                if os.path.is_file(output_dir):
                    subprocess.run(["mv", log_file_name, "_" + output_dir + "/" + log_file_name])

def run_table4_diff(table_file):
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        print("working on {}".format(adt))
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            source_file = datadir + "/" + source + sourcepostfix
            assertion_file = datadir + "/" + source + assertioninfix + str(idx) + assertionpostfix
            output_dir = outputprefix + source + str(idx)
            cmd = ["dune", "exec", "--", "main/main.exe", "diff",
                   source_file, assertion_file, output_dir]
            if verbose:
                print(" ".join(cmd))
            subprocess.run(cmd)

def run_table4_count(table_file, shortbench, longbench):
    if not (shortbench or longbench):
        shortbench = True
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        print("working on {}".format(adt))
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            output_dir = outputprefix + source + str(idx)
            long_time = False
            if 'count_long_time' in info:
                long_time = info['count_long_time']
            if ((not shortbench) and (not long_time)) or ((not longbench) and (long_time)):
                if verbose:
                    print("skip")
                continue
            cmd = ["dune", "exec", "--", "main/main.exe", "count",
                   output_dir, (source.capitalize() + "." + info['funcname'])]
            if verbose:
                print(" ".join(cmd))
            subprocess.run(cmd)

def build_table4_c1(output_dir):
    with open(output_dir + "/" + "_basic_info.json") as basic_info_file:
        return json.load(basic_info_file)
    return None

def build_table4_c2(output_dir):
    with open(output_dir + "/" + "_consistent_stat.json") as stat_file:
        stat = json.load(stat_file)
        return stat['consist_list'][-1]
    return None

def build_table4_c3(source, info, output_dir):
    c3 = {'if_weakened': False, 'info': None, 'num_phi': None, 'time_d': None}
    funcfile_prefix = output_dir + "/" + source.capitalize() + "." + info['funcname']
    try:
        # print(output_dir + "/" + "_count_" + source.capitalize() + "." +info['funcname'] +".json")
        with open(output_dir + "/" + "_count_" + source.capitalize() + "." +info['funcname'] +".json") as count_file:
            c3['num_phi'] = "{}".format(json.load(count_file)['num_phi'])
    except IOError:
        c3['num_phi'] = None

    try:
        with open( output_dir + "/" + "_diff.json") as count_file:
            c3['time_d'] = "{}".format(json.load(count_file)['diff'])
    except IOError:
        c3['time_d'] = None

    try:
        with open(funcfile_prefix + "_3600.000000_stat.json") as stat_file:
            stat = json.load(stat_file)
            try:
                with open(funcfile_prefix + "_none_stat.json") as none_stat_file:
                    none_stat = json.load(none_stat_file)
                    stat['end_negfv'] = none_stat['end_negfv']
            except IOError:
                stat['end_negfv'] = stat['end_negfv']
            c3['if_weakened'] = True
            c3['info'] = stat
    except IOError:
        c3['if_weakened'] = False
        c3['info'] = None
    return c3

def build_table4_all(table_file):
    tab = []
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        res = []
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            output_dir = "_" + outputprefix + source + str(idx)
            # init
            basic_info = build_table4_c1(output_dir)
            stat2 = build_table4_c2(output_dir)
            c3 = build_table4_c3(source, info, output_dir)
            res.append((basic_info, stat2, c3))
        tab.append({'name': adt, 'stat': res})
    print("\t(|𝐹| , |𝑅| )  |𝑃|   |𝑢|   |𝑐𝑒𝑥| time𝑐 (s)  #Gather/|𝜙+|      time𝑤 (s)  time𝑑 (ms)")
    for x in tab:
        print(x['name'])
        for basic_info, stat2, c3 in x['stat']:
            num_f = None
            num_r = None
            num_p = None
            if basic_info is not None:
                num_f = basic_info['num_f']
                num_r = basic_info['num_r']
                num_p = basic_info['num_p']

            num_qv = None
            num_cex = None
            time_c = None
            if stat2 is not None:
                num_qv = stat2['num_qv']
                num_cex = stat2['num_cex']
                time_c = "{:.2f}".format(stat2['run_time'])

            if_weakened = c3['if_weakened']
            gather = None
            time_w = None
            time_d = None
            if c3['time_d'] is not None:
                time_d = c3['time_d']
            if c3['info'] is not None:
                gather = c3['info']['end_posfv'] + c3['info']['end_negfv']
                time_w = c3['info']['run_time']
                if time_w >= 3600.0:
                    time_w = "Limit"
                else:
                    time_w = "{:.1f}".format(time_w)
                    if time_d == "Timeout":
                        time_d = "Max"
            num_phi = c3['num_phi']
            num_f = "{}".format(num_f).ljust(4)
            num_r = "{}".format(num_r).ljust(4)
            num_p = "{}".format(num_p).ljust(4)
            num_qv = "{}".format(num_qv).ljust(4)
            num_cex = "{}".format(num_cex).ljust(4)
            time_c = "{}".format(time_c).ljust(9)
            gather = "{}".format(gather).ljust(7)
            num_phi = "{}".format(num_phi).ljust(8)
            time_w = "{}".format(time_w).ljust(9)
            time_d = "{}".format(time_d).ljust(9)
            print("\t({}, {})  {}  {}  {}  {}  {}/{}  {}  {}".format(
                num_f, num_r, num_p,
                num_qv, num_cex, time_c,
                gather, num_phi, time_w, time_d
            ))

def solve_name(name):
    if name == "BankersqConcat":
        return("concat")
    if name == "BankersqCons":
        return("cons")
    if name == "BankersqNil":
        return("nil")
    if name == "BankersqReverse":
        return("reverse")
    if name == "ListCons":
        return("cons")
    if name == "Cons":
        return("cons")
    if name == "cons":
        return("cons")
    if name == "ListIsEmpty":
        return("is_empty")
    if name == "ListRev":
        return("rev")
    if name == "ListNil":
        return("nil")
    if name == "Nil":
        return("nil")
    if name == "nil":
        return("nil")
    if name == "Force":
        return("libforce")
    if name == "Lazy":
        return("liblazy")
    if name == "e":
        return("leaf")
    if name == "t":
        return("node")
    if name == "triet":
        return("node")
    if name == "maket":
        return("make_tree")
    if name == "top":
        return("top")
    if name == "push":
        return("push")
    if name == "tail":
        return("tail")
    if name == "is_empty":
        return("is_empty")
    print(name)
    exit(0)

def rename(source, funcfile_prefix, filename):
    with open(funcfile_prefix + "/" + filename) as stat_file:
        j = json.load(stat_file)
        for i in range(len(j['spectable'])):
            name=solve_name(j['spectable'][i]['name'])
            if (source == "Rbset" or source == "Leftisthp") and name == "node":
                name = "tree"
            j['spectable'][i]['name'] = source + "." + name
    with open(funcfile_prefix + "/" + filename, 'w') as stat_file:
        json.dump(j, stat_file)

import re
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
        print("Failed, expect more iterations from the weakening inference runing.")
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
    plt.subplots_adjust(right=0.76, bottom=0.42)
    figure_path = outputdir + "figure5.png"
    print("Figure 5 saved as {}".format(figure_path))
    plt.savefig(figure_path)

def build_figure5(config_file):
    with open(config_file) as f:
        config = json.load(f)
        build_figure_aux("_" + config['outputprefix'], config['figure'])

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("action", type=str,
                        help="the expected you want: consistent | weakening | count | diff | table | figure")
    parser.add_argument("config", type=str,
                        help="the config file")
    parser.add_argument("timebound", nargs='?', type=int, default=3600,
                        help="the time bound in second for weakening, default is 3600s")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="show executing commands")
    parser.add_argument("-s", "--shortbench", action="store_true",
                        help="work on benchmarks not labeled as [weakening|count]long time")
    parser.add_argument("-l", "--longbench", action="store_true",
                        help="work on benchmarks labeled as [weakening|count]long time")
    args = parser.parse_args()
    action = args.action
    table_file = args.config
    timebound = args.timebound
    verbose=args.verbose
    if action == "consistent":
        run_table4_consistent(table_file)
    elif action == "weakening":
        run_table4_weakening(table_file, args.shortbench, args.longbench, args.timebound)
    elif action == "count":
        run_table4_count(table_file, args.shortbench, args.longbench)
    elif action == "diff":
        run_table4_diff(table_file)
    elif action == "table":
        print("Generating Table 4...")
        build_table4_all(table_file)
    elif action == "figure":
        print("Generating Figure 5...")
        build_figure5(table_file)
    elif action == "rename":
        f1 = "_consistent.json"
        f2 = "_bound_maximal.json"
        f3 = "_oracle_maximal.json"
        # rename(sys.argv[2], sys.argv[3], f3)
        # rename(sys.argv[2], f2)
    else:
        print("unknown arguments, try -h to get the usage")
