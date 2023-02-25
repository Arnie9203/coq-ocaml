type 'a tree =
  | Empty
  | Leaf of 'a
  | Node of 'a * 'a tree * 'a tree