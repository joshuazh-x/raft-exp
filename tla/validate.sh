#!/usr/bin/env bash

WORKING_DIR="$(mktemp -d)"
CURRENT_DIR="$(pwd -P)"
SPEC="${CURRENT_DIR}/Traceetcdraft.tla"
CONFIG="${CURRENT_DIR}/Traceetcdraft.cfg"
TRACES="${CURRENT_DIR}/*.ndjson.gz"
QUIET=false
FAILFAST=false

function preprocess_log {
    local trace=${1}
    sed -i -E 's/^[^{]+//' ${trace}
    sort -t":" -k 3 ${trace} -o ${trace}
}

function colored_text {
    color=$1
    text=$2

    case $color in
        "red")
            echo $"\033[0;31m$text\033[0m"
        ;;

        "green")
            echo "\033[0;32m$text\033[0m"
        ;;

        *)
            echo text
        ;;
    esac
}

function validate {
    local trace_gz=${1}
    local trace="${WORKING_DIR}/$(basename "$trace_gz" .gz)"

    gunzip < ${trace_gz} > ${trace}
    
    preprocess_log ${trace}

    env JSON="${trace}" java -XX:+UseParallelGC -cp tla2tools.jar:CommunityModules-deps.jar tlc2.TLC -config "${CONFIG}" "${SPEC}" -lncheck final -metadir "${WORKING_DIR}/states" > /dev/null
    result=$?

    if [ "${QUIET}" = false ]; then 
        if [ "${result}" = 0 ]; then 
            echo -e ${trace_gz} "-" $(colored_text "green" "PASS")
        else
            echo -e ${trace_gz} "-" $(colored_text "red" "FAIL")
        fi
    fi

    return $result
}

while getopts :hs:c:qf flag
do
    case "${flag}" in
        s) SPEC=${OPTARG};;
        c) CONFIG=${OPTARG};;
        q) QUIET=true;;
        f) FAILFAST=true;;
        h|*) echo "usage: validate.sh [-s <spec>] [-c <config>] [-q] [-f] <trace files>">&2; exit 1;; 
    esac
done

shift $(($OPTIND -1))
TRACES="$@"

if [ "${QUIET}" = false ]; then 
    echo "spec: ${SPEC}"
    echo "config: ${CONFIG}"
fi

total=0
passed=0
for f in $TRACES 
do 
    validate $f
    if [ "$?" = 0 ]; then
        passed=$((passed+1))
    elif [ "${FAILFAST}" = true ]; then
        break
    fi
    total=$((total+1))
done

if [ "${QUIET}" = false ]; then 
    if [ "$total" = 0 ]; then
        echo -e "All $total trace(s) pass"
    else
        echo -e "$passed of $total trace(s) passed"
    fi
fi

if [ "$passed" -lt "$total" ]; then 
    exit 1
fi


