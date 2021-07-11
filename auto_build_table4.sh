#!/bin/bash
config=result_table4.config
python3 build_table4.py count $config
python3 build_table4.py diff $config
python3 build_table4.py column1 $config
python3 build_table4.py column2 $config
python3 build_table4.py column3 $config
