let rec labels t =
  match t with
  | Empty -> []
  | Leaf x -> [x]
  | Node (x, l, r) -> labels l @ [x] @ labels r