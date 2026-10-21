#!/usr/bin/env python3
"""Print simple static statistics of one function in two x86-64 .s files.

usage: asmstats.py OLD.s NEW.s FUNCTION [FUNCTION...]
"""
import re, sys

def function_lines(path, name):
    out, inside = [], False
    for line in open(path):
        if line.startswith(name + ':'):
            inside = True
        elif inside and line.startswith('\t.type'):
            break
        if inside and '.cfi' not in line:
            out.append(line.rstrip())
    return out

def stats(lines):
    ins = [l for l in lines if l.startswith('\t') and not l.startswith('\t.')]
    count = lambda rx: sum(1 for l in ins if re.search(rx, l))
    frame = next((l.split()[1].rstrip(',') for l in ins if l.split()[0] == 'subq' and '%rsp' in l), '-')
    return {
        'instrs': len(ins),
        'frame': frame,
        'zext movl r,r': sum(1 for l in ins if re.match(r'\s*movl\s+%(\w+), %\1$', l)),
        'movslq': count(r'^\s*movslq'),
        'rsp stores': count(r',\s*-?\d+\(%rsp(,|\))'),
        'rol/ror': count(r'^\s*(rol|ror)'),
        'leaq sym(%rip)': count(r'^\s*leaq\s+[A-Za-z_]\w*(\+\d+)?\(%rip\)'),
        'cmov': count(r'^\s*cmov'),
        'calls': count(r'^\s*call'),
    }

if __name__ == '__main__':
    old, new, *funcs = sys.argv[1:]
    for f in funcs:
        a, b = stats(function_lines(old, f)), stats(function_lines(new, f))
        print(f'{f}:')
        for k in a:
            if a[k] != b[k]:
                print(f'  {k:16s} {str(a[k]):>6s} -> {b[k]}')
