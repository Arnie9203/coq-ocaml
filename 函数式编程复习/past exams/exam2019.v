Require Import Nat.
Require Import List.
Require Import Lia.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.

(* 1. Prove the following fact about natural numbers.
Hint: You may search and use some properties about the plus function in the standard library of Coq. *)

Lemma mul_3_r : forall n : nat, n * 3 = n + n + n.
(* Proof. intros. lia. Qed. *)
Proof. intros. induction n.
+ reflexivity.
+ simpl. 
  Search (S (_ + _)).  
  rewrite PeanoNat.Nat.add_succ_r.
  rewrite PeanoNat.Nat.add_succ_r. 
  Search (S _ + _).
  rewrite plus_Sn_m. rewrite IHn. reflexivity.
Qed.


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
 Proof.  intros. induction H. apply odd1. apply odd2. apply IHevenn. Qed.
 
 Hint Resolve even_add_one.
 
 Lemma odd_add_one : forall n, oddn n -> evenn (S n).
 Proof. intros. induction H. apply even2. apply even1.
 apply even2. apply IHoddn. Qed.
 
 Hint Resolve odd_add_one.
 
 Lemma parity_dec : forall n, {evenn n} + {oddn n}.
 Proof. induction n.
  + left. apply even1.
  + destruct IHn.  
    ++ auto.
    ++ auto.
  Qed. 
 
 Hint Resolve parity_dec.
 
Theorem odd_add : forall n m, oddn n -> evenn m -> oddn (n + m).
Proof. intros. induction H.
  + simpl. auto.
  + simpl. auto.
  Qed.
 (*intros; induction H; simpl; auto. Qed. **)
 
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




(* 9. Write in Coq a function that rotates a list. Namely, the call to
(rotate l) returns a new list that is the same as l except that the last
element of l instead appears as the first element of the new list. *)

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
   and slightly simplifies it, changing every occurrence of [e + 0]
   and [e - 0] into just [e], and [e * 1] into [e]. *)

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










