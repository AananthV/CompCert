#!/bin/sh
# Fetch PolyBench/C 4.2.1 (pinned) into DIR, for bench.py --suite polybench.
# PolyBench is distributed under the Ohio State University license and is
# not included in this repository.
# usage: fetch_polybench.sh DIR
set -e
DIR=${1:?usage: fetch_polybench.sh DIR}
REV=3e872547cef7e5c9909422ef1e6af03cf4e56072
git clone -q https://github.com/MatthiasJReisinger/PolyBenchC-4.2.1 "$DIR"
git -C "$DIR" checkout -q "$REV"
echo "PolyBench/C 4.2.1 ($REV) in $DIR"
