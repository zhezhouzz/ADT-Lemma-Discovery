#!/bin/bash

for file in *.dfy; do dafny $file; done
