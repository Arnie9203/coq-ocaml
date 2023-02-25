## exam2019.v

### Q1

```haskell
(* 1. Prove the following fact about natural numbers.
Hint: You may search and use some properties about the plus function in the standard library of Coq. *)

Lemma mul_3_r : forall n : nat, n * 3 = n + n + n.
Proof. intros. induction n.
+ reflexivity.
+ simpl. 
  Search (S (_ + _)).  
  rewrite PeanoNat.Nat.add_succ_r.
  rewrite PeanoNat.Nat.add_succ_r. 
  Search (S _ + _).
  rewrite plus_Sn_m. rewrite IHn. reflexivity.
Qed.

```

**Search Usage**

The simplest way to search is to search by name. This is one of the things Search command does:

```sh
Coq < Search "len".
length: forall A : Type, list A -> nat
```

You can also search for theorems (or other objects) whose statement contains a given identifier.

```sh
Coq < Search False.
False_rect: forall P : Type, False -> P
False_ind: forall P : Prop, False -> P
(* ... *)
Coq < Search 0.
nat_rect:
  forall P : nat -> Type,
  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
nat_ind:
  forall P : nat -> Prop,
  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
(* ... *)
```

Another thing you can do is to search for patterns with holes _:

```sh
Coq < Search (S _ <= _).
le_S_n: forall n m : nat, S n <= S m -> n <= m
le_n_S: forall n m : nat, n <= m -> S n <= S m
```

When searching for a pattern, Search matches anywhere in the statement. If you only want to search for the pattern in the conclusion, use SearchPattern:

```sh
Coq < SearchPattern (S _ <= _).
le_n_S: forall n m : nat, n <= m -> S n <= S m
```

If you’re looking for a rewrite, there’s SearchRewrite. It finds conclusions of type _ = _ where one of the sides matches the given pattern.

```sh
Coq < SearchRewrite (_ + 0).
plus_n_O: forall n : nat, n = n + 0
```



### Q2

```ocaml
(* 2. Complete the following definition so that (div2021 n) returns true iff n is divisible by 2021.
Hint: You may find the leb function useful. *)
Fixpoint div2021 (n : nat ) : bool :=
  match n with
  | O => true
  | S n' => if leb n 2020 then false
            else div2021 (n' - 2020)
end.

Example div2021_test1: div2021 4042 = true.
Proof. reflexivity. Qed.

Example div2021_test2: div2021 2027 = false.
Proof. reflexivity. Qed.
```



### Q3

```ocaml
(* 3. Define a function createList such that (createList n) returns
a list of numbers in the form: [n;(n-1);...;2;1;2;...;(n-1);n], for any n > 0. *)

Fixpoint createList (n : nat) : list nat :=
  match n with 
  | O => []
  | S O => [1]
  | S n' => [n] ++ createList n' ++ [n]
end.


Example createList_test : createList 6 = [6;5;4;3;2;1;2;3;4;5;6].
Proof. reflexivity. Qed.
```

**non-exhaustive pattern matching**



### Q4

```ocaml
(* 4. Let oddn and evenn be the predicates that test whether a given number
is odd or even. Show that the sum of an odd number with an even number is odd. *)
Inductive oddn : nat -> Prop :=
 | odd1 : oddn 1
 | odd2 : forall n, oddn n -> oddn (S (S n)).

Inductive evenn : nat -> Prop :=
 | even1 : evenn 0
 | even2 : forall n, evenn n -> evenn (S (S n)).
 
Hint Constructors evenn oddn.

 (* Getting Started *)
 
 Lemma even_add_one : forall n, evenn n -> oddn (S n).
 Proof.  intros; induction H; auto. Qed.
 
 Hint Resolve even_add_one.
 
 Lemma odd_add_one : forall n, oddn n -> evenn (S n).
 Proof. intros; induction H; auto. Qed.
 
 Hint Resolve odd_add_one.
 
 Lemma parity_dec : forall n, {evenn n} + {oddn n}.
 Proof. induction n; try destruct IHn; auto. Qed.
 
 Hint Resolve parity_dec.
 
Theorem odd_add : forall n m, oddn n -> evenn m -> oddn (n + m).
Proof. intros; induction H; simpl; auto. Qed.
```





### Q5

```c
(* 5. Write a function (partition):

partition : list nat -> list (list nat )

which partitions a list into a list of 3 sublists. The first sublist
contains all even numbers in the original list. The second sublist
contains all odd numbers divisible by 5 in the original list. The last
sublist contains all other elements. The order of elements in the
three sublists should be the same as their order in the original list.

Hint: You may use the Coq function (filter).
*)

Fixpoint divide5 (n:nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => false
  | 4 => false
  | S(S(S(S(S n')))) => divide5 n'
  end.

Definition filt1(n:nat) : bool :=
  even n.

Definition filt2(n:nat) : bool :=
  (negb (even n)) && (divide5 n).

Definition filt3(n:nat) : bool :=
  negb ((even n) || ((negb (even n)) && (divide5 n))). 

Definition partition (l : list nat) : list (list nat) :=
   [ filter filt1 l ; filter filt2 l ; filter filt3 l ].

Example partition_test: partition [1;2;3;9;4;5;6;15;8] = [[2;4;6;8]; [5;15]; [1;3;9]].
Proof. reflexivity. Qed.
```



### Q6

```ocaml

(* 6. Prove the following fact about excluded middle. *)
Theorem excluded_middle : 
  (forall P Q : Prop, (P -> Q) -> (~P \/ Q)) -> (forall P, P \/ ~P).
Proof. 
unfold not. intros.
 assert((P -> False)\/P ->  P \/ (P -> False)).
   { intros. destruct H0. right. apply H0. left. apply H0. }
   apply H0.
apply H.
   intros. apply H1.
Qed.
```





### Q7

```ocaml
(* 7. Let a sequence of numbers F(n) be given as follows.
F(0) = 0
F(n) = F(n-1) + 2 * n for n > 0.

Define the function Seq such that (Seq n) returns the sequence

[0; F(1); 2; F(3); 4; F(5); \u2026 ; 2n; F(2n + 1)].
*)

Fixpoint F1(n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' => F1(n') + 2 * n
  end.

Fixpoint F2(n:nat) : nat :=
  match n with 
  | 0 => 0
  | S n' => S (S (F2 n'))
end.

Fixpoint Seq (n: nat) : list nat :=
  match n with
  | 0 => [0; 2]
  | S n' => (Seq n') ++ [(F2 n);(F1 (2 * n + 1))]
  end.

Compute Seq 5.


Example Seq_test :  Seq 5 = [0; 2; 2; 12; 4; 30; 6; 56; 8; 90; 10; 132].
Proof. reflexivity. Qed.
```



### Q8

```ocaml
(* 8. Consider the following type:

Inductive btree : Set :=
| leaf : nat -> btree
| node : nat -> btree -> btree -> btree.

Define a function taking as argument a tree t: btree and returning
the sum of all numbers occurring in the tree. *)

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Fixpoint sum (t: btree) : nat :=
  match t with 
  | leaf n => n
  | node n t1 t2 =>
                   n + sum t1 + sum t2
end.


Example bt_test : sum (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
                              (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
                  = 55.
Proof. reflexivity. Qed. 
```





### Q9

```ocaml
(* 9. Write in Coq a function that rotates a list. Namely, the call to
(rotate l) returns a new list that is the same as l except that the last element of l instead appears as the first element of the new list. *)

Fixpoint last' (l: list nat) : list nat :=
  match l with
    | [] => []
    | [a] => [a]
    | a :: l => last' l
    end.

 Fixpoint removelast (l:list nat) : list nat :=
    match l with
      | [] => []
      | [a] => []
      | a :: l => a :: removelast l
    end.

Definition rotate (l : list nat) : list nat :=
  last' l ++ (removelast l).

Example rotate_test1 : rotate [1;2;3;4;5] = [5;1;2;3;4].
Proof. reflexivity. Qed.

Example rotate_test2 : rotate [] = [].
Proof. reflexivity. Qed.

Example rotate_test3 : rotate [2] = [2].
Proof. reflexivity. Qed.
```





### Q10

```ocaml
(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)

Theorem optimize_mult1_sound: forall a,
  aeval (optimize a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) simpl. reflexivity.
  - (* APlus *) destruct a2 eqn: Eqa2.
    + destruct n eqn:En.
      * simpl. rewrite IHa1. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      * simpl. rewrite IHa1. reflexivity.
    + simpl. rewrite <- IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
  - (* AMinus *)destruct a2 eqn:Eqa2.
    + destruct n eqn:En.
      * simpl. rewrite IHa1. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
      * simpl. rewrite IHa1. reflexivity.
    + simpl. rewrite <- IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
  - (* AMult *)destruct a2 eqn:Eqa2.
    + destruct n eqn:En.
      * simpl. rewrite PeanoNat.Nat.mul_0_r. reflexivity.
      * destruct n0.
        ** simpl. rewrite IHa1. rewrite PeanoNat.Nat.mul_1_r. reflexivity. 
        ** simpl. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
Qed. 

```







## exam2020.v

### Q1

```ocaml
(* 1. Prove the following fact about natural numbers. *)

Lemma axx:forall n :nat, n+S n+2=S(n+n+2).
Proof.
intros n.
rewrite <- PeanoNat.Nat.add_succ_l. 
rewrite <- PeanoNat.Nat.add_succ_l. 
rewrite <- PeanoNat.Nat.add_assoc.
rewrite PeanoNat.Nat.add_shuffle3.
rewrite PeanoNat.Nat.add_assoc.
reflexivity.
Qed.
Lemma mul_2_r : forall  n : nat, 
  (n + 1) * 2 = n + n + 2.
Proof. 
  intros n. 
  induction n as [| n' IHn].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. rewrite axx. reflexivity.
Qed.
```



### Q2

```ocaml
(* 2. Define a function called squared so that (squared n) returns true 
iff n is a squared number, i.e. n = n' * n' for some n'. *)

Definition squared (n : nat) : bool :=
  n =?  square (sqrt n) .

Example square_test1 : squared 8 = false.
Proof. 
  reflexivity.
Qed.

Example square_test2 : squared 25 = true.
Proof. 
  reflexivity.
Qed.
```



### Q4

```ocaml

(* 4. Let oddn be the predicate that tests whether a given number
is odd or not. Show that the multiplication of two odd numbers is odd. *)

Inductive oddn : nat -> Prop :=
 | odd1 : oddn 1
 | odd2 : forall n, oddn n -> oddn (S (S n)).

Lemma axx2:forall n m :nat, n+S n+m=S(n+n+m).
Proof.
  intros n m.
rewrite <- PeanoNat.Nat.add_succ_l. 
rewrite <- PeanoNat.Nat.add_succ_l. 
rewrite <- PeanoNat.Nat.add_assoc.
rewrite PeanoNat.Nat.add_shuffle3.
rewrite PeanoNat.Nat.add_assoc.
reflexivity.
Qed.

Theorem odd_even: forall n m, oddn m -> oddn (n+n+m).
Proof.
  intros n m H.
  induction n.
  - simpl. apply H.
  - simpl. rewrite axx2. apply odd2 in IHn. apply IHn.
Qed.

Theorem odd_mul : forall n m, oddn n -> oddn m -> oddn (n * m).
Proof. 
  intros n m H1 H2.
  induction H1.
  - simpl. rewrite PeanoNat.Nat.add_0_r. apply H2.
  - simpl. rewrite PeanoNat.Nat.add_assoc. apply odd_even. apply IHoddn.
Qed.
```



### Q6

```ocaml
(* 6. We call a natural number good if the sum of all 
   its digits is divisible by 5. For example 122 is good 
   but 93 is not. Define a function count such that 
   (count n) returns the number of good numbers smaller than 
   or equal to n. Here we assume that 0 <= n < 10000. 
   Hint: You may find the "let ... in" struct useful. You may 
   directly use the div and modulo functions defined in the 
   standard library of Coq. *)
Require Import Arith.
Import Nat. 
From Equations Require Import Equations.

Section Base. 
Variable base: nat.
Hypothesis Hbase : 1 < base. 

Equations sum_aux (digits: nat) (sum: nat): nat  by wf digits lt :=
 sum_aux 0 sum := sum;
 sum_aux d sum := sum_aux (div d base)
                          (add sum (modulo d base)).
Next Obligation. 
 apply div_lt; auto with arith.
Defined. 

Definition sum_digits (digits : nat) :=
  sum_aux digits 0. 

End Base. 


Compute sum_digits 10 _ 231.

Definition sum_digits' (digits : nat) (base : nat) : nat :=
  let fix aux (sum x_value base fuel : nat) : nat :=
    match fuel with
    | 0 => sum
    | S p => 
      if leb x_value 0 then
         sum
      else
        aux (add sum (modulo x_value base)) (div x_value base) base p
    end in
   aux 0 digits base digits.
 Compute sum_digits' 231 10.

Definition isGood(n:nat) : bool := 
  if eqb ((sum_digits' n 10) mod 5) 0 then true
  else false.

Fixpoint count (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => if isGood n then 1 + count n'
            else count n'
end.

Compute count 15.

Example count_test1 : count 15 = 3.
Proof. reflexivity. Qed.

Example count_test2 : count 2005 = 401.
Proof. reflexivity. Qed.
```



### Q7

```ocaml
(* 7. Prove the following fact about excluded middle. *)

Theorem de_morgan : 
   (forall P, P \/ ~P) -> (forall P Q, ~(~P /\ ~Q) -> P \/Q).
Proof. 
 unfold not. intros.
   destruct (H Q).
   - right. apply H1.
   - destruct (H P).
     + left. apply H2.
     + destruct H0. split. ++ apply H2. ++ apply H1.
Qed.
```



### Q9

```ocaml

(* 9. Write in Coq a function that swaps the maximum and minimum
elements in a list while keeping other elements unchanged. Suppose
all the elements in the input list are distinct and they range from 1 to 100.
*)
Fixpoint max_l(l:list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => if (max_l t) <? h then h
    else max_l t
  end.

Fixpoint min_l(l:list nat) : nat :=
  match l with
  | [] => 101
  | h :: t => if h <? (min_l t) then h
    else min_l t
  end.

Fixpoint swap' (l: list nat) (ma mi : nat): list nat :=
  match l with
  | [] => []
  | h :: t => 
    if h =? ma then mi :: swap' t ma mi
    else if h =? mi then ma :: swap' t ma mi
    else h :: swap' t ma mi
  end.

Definition swap (l : list nat) : list nat :=
  swap' l (max_l l) (min_l l).

Example swap_test : swap [3;7;2;5;1;4;6] = [3;1;2;5;7;4;6].
Proof. 
  reflexivity.
Qed.
```

