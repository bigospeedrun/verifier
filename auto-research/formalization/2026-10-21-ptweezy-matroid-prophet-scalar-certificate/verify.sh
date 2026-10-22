#!/bin/sh
# Run with: bash verify.sh   (plain file, no executable mode, per package rules)
set -e
cd "$(dirname "$0")"
python3 verify.py
