import json
import subprocess
import sys

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
            log_file_name = "log.txt"
            arguments = []
            if 'arguments' in info:
                arguments = info['arguments']
            cmd = ["dune", "exec", "--", "main/main.exe", "infer", "consistent",
                   source_file, assertion_file, output_dir] + arguments
            print(" ".join(cmd))
            with open(log_file_name, "w") as log_file:
                subprocess.run(cmd, stdout=log_file)
                subprocess.run(["mv", log_file_name, "_" + output_dir + "/" + log_file_name])

def build_table4_c1(table_file):
    c1 = []
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        res = []
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            output_dir = "_" + outputprefix + source + str(idx)
            with open(output_dir + "/" + "_basic_info.json") as basic_info_file:
                basic_info = json.load(basic_info_file)
                res.append(basic_info)
        c1.append({'name': adt, 'info': res})
    print("\t(|F|, |R|) |P|")
    for x in c1:
        print(x['name'])
        for info in x['info']:
            print("\t({}, {}) {}".format(info['num_f'], info['num_r'], info['num_p']))

def build_table4_c2(table_file):
    c2 = []
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        res = []
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            output_dir = "_" + outputprefix + source + str(idx)
            with open(output_dir + "/" + "_consistent_stat.json") as stat_file:
                stat = json.load(stat_file)
                res.append(stat['consist_list'][-1])
        c2.append({'name': adt, 'stat': res})
    print("\t |u| |cex| |time_c|")
    for x in c2:
        print(x['name'])
        for info in x['stat']:
            print("\t{} {} {:.2f}".format(info['num_qv'], info['num_cex'], info['run_time']))


def end_with_help():
    print("python3 build_table4.py <consistent | weakening | column1 | column2 | column3> <config file>")
    exit(1)

if __name__ == "__main__":
    if len(sys.argv) == 1:
        end_with_help()
    action = sys.argv[1]
    if (action == "help") or (action == "-help") or (action == "--help"):
        end_with_help()
    elif action == "consistent":
        table_file = sys.argv[2]
        run_table4_consistent(table_file)
    elif action == "weakening":
        table_file = sys.argv[2]
        run_table4_consistent(table_file)
    elif action == "column1":
        table_file = sys.argv[2]
        build_table4_c1(table_file)
    elif action == "column2":
        table_file = sys.argv[2]
        build_table4_c2(table_file)
    elif action == "column3":
        table_file = sys.argv[2]
        build_table4_c2(table_file)
    else:
        print("unknown arguments")
        exit(1)
