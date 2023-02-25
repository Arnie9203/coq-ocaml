type 'a tree = 
  | Leaf
  | Node of 'a * 'a tree * 'a tree

let rec size = function
  | Leaf -> 1
  | Node (_, l, r) -> 1 + size l + size r

let rec total = function
  | Leaf -> 0
  | Node (v, l, r) -> v + total l + total r

let rec maxdepth = function
  | Leaf -> 1
  | Node (_, l, r) -> 1 + max (maxdepth l) (maxdepth r)

let rec list_of_tree = function
  | Leaf -> []
  | Node (v, l, r) -> v :: (list_of_tree l) @ (list_of_tree r)