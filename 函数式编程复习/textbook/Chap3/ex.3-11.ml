let rec mapTree f t =
  match t with
  | Empty -> Empty
  | Leaf a -> f (Leaf a)
  | Node (a, l, r) -> f (Node (a, mapTree f l, mapTree f r))