# Cobb Comparison 

This contains a suite of benchmarks for Cobb for comparison to Palamedes. 
The Cobb files here are obtained directly from the Cobb artifact at https://zenodo.org/records/16599071

## Getting started

1. [Install opam](https://opam.ocaml.org/doc/Install.html)
2. [`opam switch create ./ --deps-only`](https://opam.ocamXl.org/blog/opam-local-switches/#A-reminder-about-switches)
3. Inside the `Cobb` directory run `eval $(opam env)`
4. Build with `dune build` or `make`

## Running benchmarks

The Cobb benchmarks should have been automatically run as part `experiments.sh`,
but if you would like to re-run any of them, execute the following commands:

`python scripts/synth.py underapproximation_type/data/validation/sortedlist/`            (Sorted List)
`python scripts/synth.py underapproximation_type/data/validation/even_list/`             (List of even numbers)
`python scripts/synth.py underapproximation_type/data/validation/list_incr_one/`         (List increasing by 1)
`python scripts/synth.py underapproximation_type/data/validation/list_trues/`            (List of Trues)
`python scripts/synth.py underapproximation_type/data/validation/len_even_list_max_sketch/`         (List of even length)
`python scripts/synth.py underapproximation_type/data/validation/len_even_list_min_sketch/` 
`python scripts/synth.py underapproximation_type/data/validation/list_twos_even_len_max_sketch/`   (List of 2s of even length)    
`python scripts/synth.py underapproximation_type/data/validation/list_twos_even_len_min_sketch/`   
`python scripts/synth.py underapproximation_type/data/validation/len_k_list/`            (List of length k)
`python scripts/synth.py underapproximation_type/data/validation/list_twos_len_k/`   (List of 2s of length k)
`python scripts/synth.py underapproximation_type/data/validation/unique_list/`       (Unique List)
`python scripts/synth.py underapproximation_type/data/validation/duplicate_list/`    (List containing a duplicate)

`python scripts/synth.py underapproximation_type/data/validation/depthtree/`         (Tree of Depth k)
`python scripts/synth.py underapproximation_type/data/validation/complete_tree/`     (Complete Tree)
`python scripts/synth.py underapproximation_type/data/validation/nonemptytree/`      (Non-Empty Tree)
`python scripts/synth.py underapproximation_type/data/validation/twos_tree/`         (Tree of All Twos)
`python scripts/synth.py underapproximation_type/data/validation/rbtree_busted/`     (RB Tree with no BST)
`python scripts/synth.py underapproximation_type/data/validation/depth_bst/`         (BST Tree)

`python scripts/synth.py underapproximation_type/data/validation/equals2/`           (Number equal to 2)
`python scripts/synth.py underapproximation_type/data/validation/equals2or5/`        (Number equal to 2 or 5)
`python scripts/synth.py underapproximation_type/data/validation/gt5/`               (Number > 5)

`python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_size_max_sketch/`    (STLC)
`python scripts/synth.py underapproximation_type/data/validation/stlc_gen_term_size_min_sketch/`    

The results will be written to `*.ml.result.csv` files inside respective benchmark's directory.

Note that some of the benchmarks referred to in the paper 
(e.g. AVL tree, Well-scoped STLC term, `∃ a, a = 3 /\ v = a + 1`, among others)
do not have corresponding sketches. These benchmarks could not be expressed in Cobb because the 
necessary libraries and data types did not exist. These were considered failures for the purposes 
of comparison with Palamedes. Cobb benchmarks like unique list and duplicate list that 
Palamedes could not express were similarly considered Palamedes failures for this comparison. 