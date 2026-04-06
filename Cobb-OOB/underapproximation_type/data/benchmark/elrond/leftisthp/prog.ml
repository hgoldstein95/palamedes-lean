let rec leftisthp_gen (s : int) : int leftisthp =
  if s == 0 then Lhpleaf
  else
    let (s1 : int) = s - 1 in
    let (lt : int leftisthp) = leftisthp_gen s1 in
    let (s2 : int) = int_range_inc 0 s1 in
    let (rt : int leftisthp) = leftisthp_gen s2 in
    let (n : int) = int_gen () in
    Lhpnode (s2 + 1, n, lt, rt)
