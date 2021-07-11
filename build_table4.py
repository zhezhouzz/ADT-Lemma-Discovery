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

def run_table4_weakening(table_file, timebound, if_skip):
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
            long_time = False
            if 'long_time' in info:
                long_time = info['long_time']
            arguments = []
            if 'arguments' in info:
                arguments = info['arguments']
            if if_skip and long_time:
                print("skip")
                return
            if timebound >= 0:
                arguments = arguments + ["-tb", "{}".format(timebound)]
            cmd = ["dune", "exec", "--", "main/main.exe", "infer", "weakening",
                   source_file, assertion_file, output_dir] + arguments
            print(" ".join(cmd))
            with open(log_file_name, "w") as log_file:
                subprocess.run(cmd, stdout=log_file)
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
            print(" ".join(cmd))
            subprocess.run(cmd)

def run_table4_count(table_file, if_all):
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        print("working on {}".format(adt))
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            output_dir = outputprefix + source + str(idx)
            if_complicate = False
            if 'if_complicate' in info:
                if_complicate = info['if_complicate']
            print(if_complicate)
            if if_all or (not if_complicate):
                cmd = ["dune", "exec", "--", "main/main.exe", "count",
                       output_dir, (source.capitalize() + "." + info['funcname'])]
                print(" ".join(cmd))
                subprocess.run(cmd)

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
    print("\t(|𝐹|,|𝑅|) |𝑃|")
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
    print("\t |𝑢| |𝑐𝑒𝑥| time𝑐 (s)")
    for x in c2:
        print(x['name'])
        for info in x['stat']:
            print("\t{} {} {:.2f}".format(info['num_qv'], info['num_cex'], info['run_time']))

def build_table4_c3(table_file):
    c3 = []
    datadir, outputprefix, sourcepostfix, assertioninfix, assertionpostfix, benchmarks = parse_config(table_file)
    for benchmark in benchmarks:
        adt = benchmark['adt']
        res = []
        infos = benchmark['infos']
        for info in infos:
            source = info['source']
            idx = info['idx']
            output_dir = "_" + outputprefix + source + str(idx)
            funcfile_prefix = output_dir + "/" + source.capitalize() + "." + info['funcname']
            # print(output_dir + "/" + funcfile)
            # exit(0)
            try:
                # print(output_dir + "/" + "_count_" + source.capitalize() + "." +info['funcname'] +".json")
                with open(output_dir + "/" + "_count_" + source.capitalize() + "." +info['funcname'] +".json") as count_file:
                    num_phi = "{}".format(json.load(count_file)['num_phi'])
            except IOError:
                num_phi = "None"

            try:
                with open( output_dir + "/" + "_diff.json") as count_file:
                    time_d = "{}".format(json.load(count_file)['diff'])
            except IOError:
                time_d = "None"

            try:
                with open(funcfile_prefix + "_3600.000000_stat.json") as stat_file:
                    stat = json.load(stat_file)
                    try:
                        with open(funcfile_prefix + "_none_stat.json") as none_stat_file:
                            # print(funcfile_prefix + "_none_stat.json")
                            none_stat = json.load(none_stat_file)
                            stat['end_negfv'] = none_stat['end_negfv']
                    except IOError:
                        res=res
                    res.append((True, stat, num_phi, time_d))
            except IOError:
                res.append((False,{}, num_phi, time_d))
        c3.append({'name': adt, 'stat': res})
    print("\t #Gather/|𝜙+| time𝑤 (s)  time𝑑 (ms)")
    for x in c3:
        print(x['name'])
        for if_weakened, info, num_phi, time_d in x['stat']:
            if if_weakened:
                if info['run_time'] >= 3600.0:
                    run_time = "Limit"
                else:
                    run_time = "{:.1f}".format(info['run_time'])
                    if time_d == "Timeout":
                         time_d = "Max"
                print("\t{}/{} {}  {}".format(info['end_posfv'] + info['end_negfv'], num_phi, run_time, time_d))
            else:
                print("\tNone")

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


def end_with_help():
    print("python3 build_table4.py <consistent | weakening | count | column1 | column2 | column3 | column4 > <config file>")
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
        if_skip = True
        timebound = 3600
        if len(sys.argv) >= 4:
            if sys.argv[3] == "all":
                if_skip = False
            if sys.argv[3] == "unlimited":
                if_skip = False
                timebound = -1
        run_table4_weakening(table_file, timebound, if_skip )
    elif action == "count":
        table_file = sys.argv[2]
        if_all = False
        if len(sys.argv) >= 4:
            if_all = (sys.argv[3] == "all")
        run_table4_count(table_file, if_all)
    elif action == "diff":
        table_file = sys.argv[2]
        run_table4_diff(table_file)
    elif action == "column1":
        table_file = sys.argv[2]
        build_table4_c1(table_file)
    elif action == "column2":
        table_file = sys.argv[2]
        build_table4_c2(table_file)
    elif action == "column3":
        table_file = sys.argv[2]
        build_table4_c3(table_file)
    elif action == "rename":
        f1 = "_consistent.json"
        f2 = "_bound_maximal.json"
        f3 = "_oracle_maximal.json"
        rename(sys.argv[2], sys.argv[3], f3)
        # rename(sys.argv[2], f2)
    else:
        print("unknown arguments")
        end_with_help()
