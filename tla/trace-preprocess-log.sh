#!/bin/bash

sed -i -E 's/^[^{]+//' $1
sort -t":" -k 3 $1 -o $1