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

# --- Your commands here ---
run "sorted list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/sortedlist 
run "even list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/even_list 
run "incrementing by 1 list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_incr_one/           
run "list of trues" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_trues/             
run "even length list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/len_even_list/         
run "twos list even length" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_twos_even_len/     
run "length k list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/len_k_list/           
run "list twos length k list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/list_twos_len_k/  
run "unique list" timeout 900 python scripts/synth.py underapproximation_type/data/validation/unique_list/     
run "list with duplicates" timeout 900 python scripts/synth.py underapproximation_type/data/validation/duplicate_list/   
run "depth n tree"  timeout 900 python scripts/synth.py underapproximation_type/data/validation/depthtree/      
run "complete tree" timeout 900 python scripts/synth.py underapproximation_type/data/validation/complete_tree/  
run "nonempty tree" timeout 900 python scripts/synth.py underapproximation_type/data/validation/nonemptytree/     
run "tree of twos" timeout 900 python scripts/synth.py underapproximation_type/data/validation/twos_tree/     
run "rbtree no BST" timeout 900 python scripts/synth.py underapproximation_type/data/validation/rbtree_busted/   
run "bst depth k" timeout 900 python scripts/synth.py underapproximation_type/data/validation/depth_bst/     
run "equals 2" timeout 900 python scripts/synth.py underapproximation_type/data/validation/equals2/        
run "equals 2 or 5" timeout 900 python scripts/synth.py underapproximation_type/data/validation/equals2or5/     
run "greater than 5" timeout 900 python scripts/synth.py underapproximation_type/data/validation/gt5/             
run "stlc term max sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_size_1/  
run "stlc term min sketch" timeout 900 python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_size_2/  

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