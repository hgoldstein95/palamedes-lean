let rec incr_one_list_gen (s : int) (x : int) : int list =
  if sizecheck s then []
  else
    let (y : int) = int_gen () in
    if y == x + 1 then
      let (size2 : int) = subs s in
      let (l : int list) = incr_one_list_gen size2 y in
      let (l2 : int list) = y :: l in
      l2
    else Exn

let[@assert] incr_one_list_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((len v s && incr_one v
    && (not (emp v)) #==> (fun ((u [@exists]) : int) -> hd v u && x <= u)
    : [%v: int list])
    [@under])
