let rec subset l1 l2 =
  match l1 with
  | [] -> true
  | h :: t -> let rec member l =
                match l with 
                | [] -> false
                | h' :: t' -> h = h' || member t'
  in member l2 && subset t l2