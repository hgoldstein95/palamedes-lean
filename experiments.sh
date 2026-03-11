#!/bin/bash
set -e

# run Cobb experiments
cd Cobb
eval $(opam env)


#!/bin/bash

# Arrays to track results
passed=()
failed=()

# Helper function to run a command and track result
run() {
    local label="$1"
    echo "Running $label"
    shift
    if "$@" > /dev/null 2>&1; then
        passed+=("$label")
    else
        failed+=("$label ← exit code $?")
    fi
}

run "sorted list max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/sortedlist_max_sketch 
run "even list max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/even_list_max_sketch 
run "incrementing by 1 list max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_incr_one_max_sketch            
run "list of trues max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_trues_max_sketch             
run "even length list max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/len_even_list_max_sketch          
run "twos list even lengt max sketchh" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_twos_even_len_max_sketch      
run "length k list max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/len_k_list_max_sketch          
run "list twos length k list max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_twos_len_k_max_sketch   
run "unique list max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/unique_list_max_sketch      
run "list with duplicates max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/duplicatelist_max_sketch   
run "depth n tree max sketch"  timeout 900 python scripts/synth.py underapproximation_type/data/validation/depthtree_max_sketch       
run "complete tree max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/complete_tree_max_sketch  
run "nonempty tree max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/nonemptytree_max_sketch      
run "tree of twos max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/twos_tree_max_sketch     
run "rbtree no BST max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/rbtree_busted_max_sketch    
run "bst depth k max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/depth_bst_max_sketch      
run "equals 2 max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/equals2_max_sketch         
run "equals 2 or 5 max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/equals2or5_max_sketch      
run "greater than 5 max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/gt5_max_sketch              
run "stlc term max sketch max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_max_sketch   

run "sorted list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/sortedlist_min_sketch
run "even list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/even_list_min_sketch 
run "incrementing by 1 list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_incr_one_min_sketch          
run "list of trues" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_trues_min_sketch                 
run "length k list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/len_k_list_min_sketch           
run "list twos length k list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_twos_len_k_min_sketch  
run "unique list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/unique_list_min_sketch     
run "list with duplicates" timeout 900 python scripts/synth.py underapproximation_type/data/validation/duplicatelist_min_sketch   
run "depth n tree"  timeout 900 python scripts/synth.py underapproximation_type/data/validation/depthtree_min_sketch      
run "complete tree" timeout 900 python scripts/synth.py underapproximation_type/data/validation/complete_tree_min_sketch
run "nonempty tree" timeout 900 python scripts/synth.py underapproximation_type/data/validation/nonemptytree_min_sketch     
run "tree of twos" timeout 900 python scripts/synth.py underapproximation_type/data/validation/twos_tree_min_sketch     
run "rbtree no BST" timeout 900 python scripts/synth.py underapproximation_type/data/validation/rbtree_busted_min_sketch   
run "bst depth k" timeout 900 python scripts/synth.py underapproximation_type/data/validation/depth_bst_min_sketch     
run "equals 2" timeout 900 python scripts/synth.py underapproximation_type/data/validation/equals2_min_sketch        
run "equals 2 or 5" timeout 900 python scripts/synth.py underapproximation_type/data/validation/equals2or5_min_sketch     
run "greater than 5" timeout 900 python scripts/synth.py underapproximation_type/data/validation/gt5_min_sketch           
run "stlc term max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_min_sketch

# these two time out 
run "even length list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/len_even_list_min_sketch         
run "twos list even length" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_twos_even_len_min_sketch 

# --- Summary ---
echo ""
echo "===== RESULTS ====="
echo "✅ Succesfully Synthesized (${#passed[@]}):"
for item in "${passed[@]}"; do
    echo "   • $item"
done

echo ""
echo "❌ Timed Out or Failed to Synthesize (${#failed[@]}):"
for item in "${failed[@]}"; do
    echo "   • $item"
done