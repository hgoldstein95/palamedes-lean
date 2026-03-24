let rec incr_one_list_gen (s : int) (x : int) : int list =
  if sizecheck s then Err
  else
    let (y : int) = int_gen () in
    if y == x + 1 then Err else Exn

let[@assert] incr_one_list_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((len v s && incr_one v
    && (not (emp v)) #==> (fun ((u [@exists]) : int) -> hd v u && u == x + 1)
    : [%v: int list])
    [@under])
