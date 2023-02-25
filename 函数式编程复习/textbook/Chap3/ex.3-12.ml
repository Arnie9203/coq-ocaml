let sortTree t =
  let sortNode t' =
    match t' with 
    | Empty -> Empty
    | Leaf a -> Leaf (sort a)
    | Node (a, l, r) -> Node (sort a, l, r)
  in
  mapTree sortNode t