let rec nonredundancy l =
  match l with 
  | [] -> []
  | h :: t -> let rec member l' =
                match l' with
                | [] -> false
                | h' :: t' -> h = h' || member t'
  in if member t then nonredundancy t
  else h :: nonredundancy t