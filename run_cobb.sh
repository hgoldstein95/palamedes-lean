#!/bin/bash

set -e

# run Cobb experiments
cd Cobb
eval $(opam env)

benchmarks=('sortedlist' 'even_list' 'list_trues' 'list_twos' 'list_twos_even_len' 'len_even_list' 'len_k_list' 'list_twos_len_k' 'uniquelist' 'duplicatelist' 'depthtree' 'complete_tree' 'nonemptytree' 'twos_tree' 'rbtree_busted' 'depth_bst' 'stlc_gen_term_size' 'equals2' 'equals2sym' 'equals2or5' 'equals2or5andTrue' 'gt5' 'between_5_10' 'between_lo_hi' 'between_lo_hi_or_zero' )

cobbrun() {
    local b="$1"
    local res="$b"
    #max sketch
	max_cmd="timeout 900 python scripts/synth.py underapproximation_type/data/validation/${b}_max_sketch"
    if $max_cmd > /dev/null 2>&1; then
        # read output file
        f="`tail -1 underapproximation_type/data/validation/${b}_max_sketch/progMax.ml.result.csv`"
		status=$(echo $f| awk -F',' '{print $1}')
		if [ "$status" != 'true' ]; then
			res+=',error,'
		else
			time=$(echo $f| awk -F',' '{print $10}')
			res+=",success,${time}"
		fi
    elif [ $? = 124 ]; then
        res+=',timeout,'
    else
        res+=',error,'
    fi
	#min sketch
	min_cmd="timeout 900 python scripts/synth.py underapproximation_type/data/validation/${b}_min_sketch"
    if $min_cmd > /dev/null 2>&1; then
        # read output file
        f="`tail -1 underapproximation_type/data/validation/${b}_min_sketch/progMin.ml.result.csv`"
		status=$(echo $f| awk -F',' '{print $1}')
		if [ "$status" != 'true' ]; then
			res+=',error,'
		else
			time=$(echo $f| awk -F',' '{print $10}')
			res+=",success,${time}"
		fi
    elif [ $? = 124 ]; then
        res+=',timeout,'
    else
        res+=',error,'
    fi
    echo $res >> cobbResults.txt
    echo $res
}

echo 'Benchmark,max sketch status,max sketch time,min sketch status,min sketch time' > cobbResults.txt
echo 'Benchmark,max sketch status,max sketch time,min sketch status,min sketch time'
for b in "${benchmarks[@]}"
do
   cobbrun $b
done