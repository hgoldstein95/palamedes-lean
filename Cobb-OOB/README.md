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
but if you would like to re-run any of them, execute the following command:

`python scripts/synth.py underapproximation_type/data/validation/*NAME*/`   

where *Name* is the name of the benchmark. 
The results will be written to `*.ml.result.csv` files inside the respective benchmark's directory.

Note that some of the benchmarks referred to in the paper 
(e.g. AVL tree, Well-scoped STLC term, `∃ a, a = 3 /\ v = a + 1`, among others)
do not have corresponding sketches. These benchmarks could not be expressed in Cobb because the 
necessary libraries and data types did not exist. These were considered failures for the purposes 
of comparison with Palamedes. Cobb benchmarks like unique list and duplicate list that 
Palamedes could not express were similarly considered Palamedes failures for this comparison. 