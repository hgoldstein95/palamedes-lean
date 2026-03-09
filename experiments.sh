#!/bin/bash
set -e

# run Cobb experiments
cd Cobb
eval $(opam env)
dune build
python scripts/synth.py underapproximation_type/data/validation/sortedlist
python scripts/synth.py underapproximation_type/data/validation/even_list
python scripts/synth.py underapproximation_type/data/validation/list_incr_one/         
python scripts/synth.py underapproximation_type/data/validation/list_trues/            
python scripts/synth.py underapproximation_type/data/validation/len_even_list/         
python scripts/synth.py underapproximation_type/data/validation/list_twos_even_len/    
python scripts/synth.py underapproximation_type/data/validation/len_k_list/           
python scripts/synth.py underapproximation_type/data/validation/list_twos_len_k/  
python scripts/synth.py underapproximation_type/data/validation/unique_list/     
python scripts/synth.py underapproximation_type/data/validation/duplicate_list/   
python scripts/synth.py underapproximation_type/data/validation/depthtree/      
python scripts/synth.py underapproximation_type/data/validation/complete_tree/  
python scripts/synth.py underapproximation_type/data/validation/nonemptytree/    
python scripts/synth.py underapproximation_type/data/validation/twos_tree/     
python scripts/synth.py underapproximation_type/data/validation/rbtree_busted/   
python scripts/synth.py underapproximation_type/data/validation/depth_bst/     
python scripts/synth.py underapproximation_type/data/validation/equals2/       
python scripts/synth.py underapproximation_type/data/validation/equals2or5/     
python scripts/synth.py underapproximation_type/data/validation/gt5/             
python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_size_1/  
python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_size_2/  