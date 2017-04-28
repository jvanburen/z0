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
CC0_INCLUDE_PATHS = ["./z0lib", "/home/user/cc0/runtime/"]

# Derived config (shouldn't need to change)
CC0 = CC0_BIN_PREFIX + "cc0.bin"
CLANG = LLVM_BIN_PREFIX + "clang"
OPT = LLVM_BIN_PREFIX + "opt"
DIS = LLVM_BIN_PREFIX + "llvm-dis"

CC0_LIBOPTIONS = ['-L', 'include', '-L', 'lib']
CC0_OPTIONS = ['-d', '--no-log', "--save-files", "--standard=c0"]
CLANG_OPTIONS = ["-O0",'-std=c99', '-fwrapv', '-w', '-g', '-D', 'IGNORE_CC0_ASSERT']
OPT_BEFORE_PASSES = ['-mem2reg', '-jump-threading']
Z3_PASS_NAME = ["-load", "/home/user/z3-4.5.0-x64-debian-8.5/bin/libz3.so",
                "-load", "lib/z0.so", "-z0"]

def main(args):
  filename = args.files[-1]
  c_file = filename + ".c"
  h_file = filename + ".h"
  # Compile C0 to C
  CC0_OUTPUT = ['-o', args.output]
  sp.check_call([CC0] + CC0_LIBOPTIONS + CC0_OPTIONS + CC0_OUTPUT + args.files)#, stderr=sp.DEVNULL)
  # Generate llvm bitcode with clang
  include_flags = ["-I"+path for path in CC0_INCLUDE_PATHS]
  bc_file = filename + ".bc"
  opt_file = filename + ".opt.bc"

  sp.check_call([CLANG, "-S", "-emit-llvm", c_file, '-o', bc_file] + include_flags + CLANG_OPTIONS)

  # Analyze llvm code
  sp.check_call([OPT, bc_file, '-o', opt_file] + OPT_BEFORE_PASSES)
  if args.debug_ll:
    ll_file = filename + ".ll"
    print("outputting ll file", ll_file)
    sp.check_call([DIS, opt_file, '-o', ll_file])
  else:
    os.remove(c_file)

  if args.debug_pass:
      Z3_PASS_NAME.append('-debug')
  sp.check_call([OPT, opt_file, '-o', os.path.devnull] + Z3_PASS_NAME)
  os.remove(h_file)
  os.remove(bc_file)
  os.remove(opt_file)

if __name__ == '__main__':
  parser = argparse.ArgumentParser(
        description='Static Analysis for C0', prog="z0",
        formatter_class=argparse.RawDescriptionHelpFormatter,
  epilog="Jacob Van Buren (jvanbure)\n17-355 Program Analysis Final Project Spring 2017")
  parser.add_argument('-l', '--debug-ll', action='store_true', dest="debug_ll",
                      help='save the human-readable ll file')
  parser.add_argument('-d', '--debug-pass', action='store_true', dest="debug_pass",
                      help='enable debug logging')
  parser.add_argument('files', nargs='+', metavar='SOURCEFILE', help='source C0 file to check')
  parser.add_argument('-o', '--output', metavar='<file>', help='place the executable output into <file>', default='a.out', dest='output')
  try:
    main(parser.parse_args())
  except Exception as e:
    print('\033[91m'+str(e)+'\033[0m')
