(* Final Exam --- December 27, 2021  
You are allowed to search and use any property provided in the 
standard library of Coq. *)
(*
Zhou Ziwei
10195101479
Q6 Q7 not proved
Q10 are proved!
*)

Require Import Nat.
Require Import List.
Require Import Program Nat.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.

(* 1. Prove the following fact about natural numbers. *)

Lemma axx:forall n :nat, n+S n+2=S(n+n+2).
Proof.
intros n.
Search (S (_ + _)).
rewrite <- PeanoNat.Nat.add_succ_l. 
rewrite <- PeanoNat.Nat.add_succ_l.
Search (_ + _ + _). 
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

(* 3. Let two sequences of numbers F1(n) and F2(n) be given as follows.
   F1(0) = 0
   F1(n) = F1(n-1) + 2 * n   for n > 0.

   F2(0) = F2(1) = 1
   F2(n+2) = F2(n) + F2(n+1)    for n >= 0.

Define the function Seq such that (Seq n) returns the sequence

[F1(0); F2(0); F1(1); F2(1); ... ; F1(n); F2(n)].
*)
Fixpoint F1(n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' => F1(n') + 2 * n
  end.

Fixpoint F2(n:nat) : nat :=
  match n with 
  | 0 => 1
  | S n' => match n' with 
    | 0 => 1
    | S n'' => F2(n') + F2(n'')
    end
  end.

Fixpoint Seq (n: nat) : list nat :=
  match n with
  | 0 => [0;1]
  | S n' => (Seq n') ++ [(F1 n);(F2 n)]
  end.

Example Seq_test :  Seq 5 = [0; 1; 2; 1; 6; 2; 12; 3; 20; 5; 30; 8].
Proof. 
  reflexivity.
Qed.


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


(* 5. Write a function (partition):

      partition : list nat -> list (list nat )

   which partitions a list into a list of 3 sublists. The first sublist
   contains all odd numbers divisible by 3 in the original list. 
   The second sublist contains all other odd numbers in the original list. 
   The last sublist contains all the even numbers in the original list. 
   The order of elements in the three sublists should be the same as their 
   order in the original list. 

   Hint: You may use the Coq function (filter).
*)

Fixpoint divide3 (n:nat) : bool :=
  match n with
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => true
  | S(S(S n')) => divide3 n'
  end.

Definition filt1(n:nat) : bool :=
  (negb (even n)) && (divide3 n).

Definition filt2(n:nat) : bool :=
  (negb (even n)) && (negb (divide3 n)).

Definition filt3(n:nat) : bool :=
  even n.

Definition partition (l : list nat) : list (list nat) :=
  [ filter filt1 l ; filter filt2 l ; filter filt3 l ].

Example partition_test: 
  partition [1;2;3;9;4;5;6;15;8] = [[3; 9; 15]; [1; 5]; [2; 4; 6; 8]].
Proof. 
  reflexivity.
Qed.

(* 6. We call a natural number good if the sum of all 
   its digits is divisible by 5. For example 122 is good 
   but 93 is not. Define a function count such that 
   (count n) returns the number of good numbers smaller than 
   or equal to n. Here we assume that 0 <= n < 10000. 
   Hint: You may find the "let ... in" struct useful. You may 
   directly use the div and modulo functions defined in the 
   standard library of Coq. *)

Definition sum_digits (digits : nat) (base : nat) : nat :=
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

Compute (sum_digits 3412 10).

Fixpoint div5 (n : nat) : bool :=
  match n with 
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => false
  | 4 => false
  | S(S(S(S(S n')))) => div5 n'
  end.

Fixpoint count (n : nat) : nat :=
  match n with 
  | 0 => 1
  | S n' => if div5 (sum_digits n 10) then 1 + count n'
            else count n' 
  end.


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



(* 8. Consider the following type:

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.
 
Define a function to give a preorder traversal of the tree and collect
all the odd numbers in a list. 
*)

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Fixpoint preorder (t: btree) : list nat :=
  match t with
  | node n t1 t2 =>
    if even n then (preorder t1) ++ (preorder t2)
    else [n] ++ (preorder t1) ++ (preorder t2)
  | leaf n =>
    if even n then []
    else [n]
  end.

Example bt_test : preorder (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
                                   (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
                   = [5; 1; 3; 9; 7].
Proof. 
  reflexivity.
Qed.


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

(* 10. The following definitions specify the abstract syntax of
    some arithmetic expressions and an evaluation function. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e + 0],
   [e - 0] or [e * 1] into [e], and [e * 0] into [0]. *)
 
Fixpoint optimize (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus  e1 (ANum 0) => optimize e1  (* [e + 0] *)
  | APlus  e1 e2 => APlus  (optimize e1) (optimize e2)
  | AMinus e1 (ANum 0) => optimize e1  (* [e - 0] *)
  | AMinus e1 e2 => AMinus (optimize e1) (optimize e2)
  | AMult  e1 (ANum 1) => optimize e1  (* [e * 1] *)
  | AMult  e1 (ANum 0) => ANum 0  (* [e * 0] *)
  | AMult  e1 e2 => AMult  (optimize e1) (optimize e2)
  end.


(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)
Search mult.
Theorem optimize_mult1_sound: forall a,
  aeval (optimize a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) simpl. reflexivity.
  - (* APlus *) induction a2.
    + induction n.
      * simpl. rewrite IHa1. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      * simpl. rewrite IHa1. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
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





