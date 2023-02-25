let max a b = 
  if a > b then a else b

let rec maxlist = function
  | [] -> raise (Failure "empty list")
  | [x] -> x
  | x :: xs -> max x (maxlist xs)