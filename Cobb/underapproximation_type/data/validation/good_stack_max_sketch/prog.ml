let rec gen_stack (d : int) : stack =
  if sizecheck d then Mty 
  else 
    let (x : int) = if bool_gen () then 0 else 1 in 
    let (l : label) = if bool_gen () then Pub else Sec in 
    let (a : atom) = Atm (x, l) in
    let (s : stack) = gen_stack (subs d) in 
    if bool_gen () then 
      StackCons (a, s) 
    else 
      RetCons (a, s)

let[@assert] gen_stack =
  let d = ((0 <= v : [%v: int]) [@over]) in
  ((good_stack d v : [%v: stack]) [@under])
