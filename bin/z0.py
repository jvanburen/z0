#!/usr/bin/env python3
"""check.py
Driver program / entry point for static analysis
"""
import os
import subprocess as sp
import argparse

# Top-level Configuration (can change)
# Make sure path prefixes end in "/"
CC0_BIN_PREFIX = "/home/user/cc0/bin/"
LLVM_BIN_PREFIX = "/home/user/llvm-3.9.1.install/bin/"
Z0_PREFIX = "/home/user/project/"
CC0_INCLUDE_PATHS = [Z0_PREFIX + "include/z0", "/home/user/cc0/runtime/"]

# Derived config (shouldn't need to change)
CC0 = CC0_BIN_PREFIX + "cc0.bin"
CLANG = LLVM_BIN_PREFIX + "clang"
OPT = LLVM_BIN_PREFIX + "opt"
DIS = LLVM_BIN_PREFIX + "llvm-dis"

CC0_LIBOPTIONS = ['-L', Z0_PREFIX + 'include', '-L', Z0_PREFIX + 'lib']
CC0_OPTIONS = ['-d', '--no-log', "--save-files", "--standard=c0"]
OPT_BEFORE_PASSES = ['-mem2reg', '-jump-threading', '-loops']
CLANG_OPTIONS = ["-I" + path for path in CC0_INCLUDE_PATHS] + [
    '-S', '-emit-llvm',
    '-O0', '-std=c99', '-fwrapv', '-w', '-g',
    '-D', 'COMPILING_FOR_Z0']
Z0_PASS_LOAD = [
    "-load", "/home/user/z3-4.5.0-x64-debian-8.5/bin/libz3.so",
    "-load", Z0_PREFIX + "lib/z0.so"]
Z0_PASS_NAME = ["-z0"]
EPILOG = """Jacob Van Buren (jvanbure)
17-355 Program Analysis Final Project Spring 2017"""

def main(args):
    """Entrypoint"""
    filename = args.files[-1]
    c_file = filename + ".c"
    h_file = filename + ".h"
    bc_file = filename + ".bc"
    opt_file = filename + ".opt.bc"
    ll_file = filename + ".ll"
    if args.debug_pass:
        Z0_PASS_LOAD.append('-debug')

    # Compile C0 to C
    cc0_options = CC0_LIBOPTIONS + CC0_OPTIONS + args.files
    sp.check_call([CC0, '-o', args.output] + cc0_options)  # stderr=sp.DEVNULL)

    # Generate llvm bitcode with clang
    sp.check_call([CLANG, c_file, '-o', bc_file] + CLANG_OPTIONS)

    # Analyze llvm code
    sp.check_call([OPT, bc_file, '-o', opt_file] + OPT_BEFORE_PASSES)
    if args.debug_ll:
        print("Outputting human-readable file", ll_file)
        sp.check_call([DIS, opt_file, '-o', ll_file])
    else:
        os.remove(c_file)

    sp.check_call([OPT, opt_file, '-o', os.path.devnull] + Z0_PASS_LOAD + OPT_BEFORE_PASSES + Z0_PASS_NAME)

    os.remove(h_file)
    os.remove(bc_file)
    os.remove(opt_file)

if __name__ == '__main__':
    PARSER = argparse.ArgumentParser(
        prog="z0",
        description='Static Analysis verification for C0',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=EPILOG)
    PARSER.add_argument(
        '-l', '--debug-ll',
        dest="debug_ll",
        action='store_true',
        help='save the human-readable ll file')
    PARSER.add_argument(
        '-d', '--debug-pass',
        dest="debug_pass",
        action='store_true',
        help='enable debug logging')
    PARSER.add_argument(
        'files',
        metavar='SOURCEFILE',
        nargs='+',
        help='source C0 file to check')
    PARSER.add_argument(
        '-o', '--output',
        metavar='<file>',
        dest='output',
        default='a.out',
        help='place the executable output into <file>')
    try:
        main(PARSER.parse_args())
    except sp.CalledProcessError as ex:
        print('\033[91m' + str(ex) + '\033[0m')
