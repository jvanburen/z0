#!/usr/bin/env python3
"""check.py
Driver program / entry point for static analysis
"""
import os
import os.path as path
import subprocess as sp
import argparse

# Top-level Configuration (can change)
# Make sure path prefixes end in "/"
CC0_BIN_PREFIX = "/home/user/cc0/bin/"
LLVM_BIN_PREFIX = "/home/user/llvm-3.9.1.install/bin/"
CC0_INCLUDE_PATHS = ["/home/user/cc0/include/", "/home/user/cc0/runtime/"]

# Derived config (shouldn't need to change)
CC0 = CC0_BIN_PREFIX + "cc0.bin"
CLANG = LLVM_BIN_PREFIX + "clang"
OPT = LLVM_BIN_PREFIX + "opt"
DIS = LLVM_BIN_PREFIX + "llvm-dis"

CLANG_OPTIONS = ["-O0",'-std=c99', '-g', '-fwrapv', '-w']
OPT_BEFORE_PASSES = ['-mem2reg', '-jump-threading']
Z3_PASS_NAME = []

def main(args):
  c_file = args.file + ".c"
  h_file = args.file + ".h"
  sp.check_call([CC0, "-d", "--save-files", "--no-log", "-c", "-###", args.file])
  # Generate llvm bitcode with clang
  include_flags = ["-I"+path for path in CC0_INCLUDE_PATHS]
  sp.check_call([CLANG, "-S", "-emit-llvm", c_file] + include_flags + CLANG_OPTIONS)
  bc_file = args.file + ".bc"
  opt_file = args.file + ".bc"

  #analyze llvm code
  # TODO: don't forget load the analysis pass
  sp.check_call([OPT, bc_file, '-o', opt_file] + OPT_BEFORE_PASSES + Z3_PASS_NAME)
  if args.debug_ll:
    ll_file = args.file + ".ll"
    sp.check_call([DIS, opt_file, '-o', ll_file])
  os.remove(bc_file, opt_file)

if __name__ == '__main__':
  parser = argparse.ArgumentParser(description='Static Analysis for C0')
  parser.add_argument('-d', '--debug-ll', action='store_true', dest="debug_ll",
                      help='save the human-readable ll file')
  parser.add_argument('file', help='The file to check')
  main(parser.parse_args())
