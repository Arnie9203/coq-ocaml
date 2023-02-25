let rec replaceEmpty y t =
  match t with
  | Empty -> y
  | Leaf a -> Leaf a
  | Node (a, l, r) -> Node (a, replaceEmpty y l, replaceEmpty y r)