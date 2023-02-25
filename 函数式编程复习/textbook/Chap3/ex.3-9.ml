let rec replace x y t =
  match t with
  | Empty -> Empty
  | Leaf a -> if x = a then Leaf y else Leaf a
  | Node (a, l, r) -> Node ((if x = a then y else a ),
                              replace x y l, replace x y r)