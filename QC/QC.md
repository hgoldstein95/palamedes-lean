There are two files in this directory, QC.v and LC.v.
The majority of the generators are defined in QC.v; the other file, LC.v,
contains only the generators that relate to STLC, to avoid some namespace
collisions.

To compile the files, which derives the generators for RQ2, simply do:
```
~/.opam/5.3.0/bin/coqc QC.v
```

To run a generator for testing purposes, simply uncomment the corresponding
Sample command. For example, to sample the most complex generator (for
red-black trees) at the end of QC.v, simply change the line:

```
(* Sample (genST (fun t => RBT black 2 0 17 t)). *)
```

to


```
Sample (genST (fun t => RBT black 2 0 17 t)).
```

and then re-run the coqc command above to see the sampled output in
the terminal.