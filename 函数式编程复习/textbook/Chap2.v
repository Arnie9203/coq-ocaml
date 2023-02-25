Require Import Nat.
Require Import List.
Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
(* ex.2.1 *)
Definition orb (b1 b2 : bool) : bool :=
  match b1 with 
  | true => true
  | false => b2
end.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
end.

(* ex.2.2 *)
Fixpoint div3 (n : nat) : bool :=
  match n with 
  | 0 => true
  | 1 => false
  | 2 => false
  | S (S (S n')) => div3 n'
  end.

(* ex.2.3*)
Fixpoint div2021 (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => if leb n 2020 then false
    else div2021 (n' - 2020)
  end.


(* ex.2.4*)
Fixpoint mult (n m : nat) : nat :=
  match n with 
  | 0 => 0
  | S n' => m + mult n' m
  end.

Fixpoint exp (n m : nat) : nat :=
  match m with
  | 0 => 1
  | S m' => n * (exp n m')
  end.

Fixpoint fact (n : nat) : nat :=
  match n with 
  | 0 => 1
  | S n' => n * fact n'
  end.

(* ex.2.5*)
Fixpoint eqb (n m : nat) : bool :=
  match n, m with 
  | 0, 0 => true
  | S _, 0 => false
  | 0, S _ => false
  | S n', S m' => eqb n' m'
  end.

Fixpoint eqb' (n m : nat) : bool := 
  match n with
  | 0 => match m with 
          | 0 => true
          | S _ => false
          end
  | S n' => match m with
            | 0 => false
            | S m' => eqb' n' m'
            end
end.


Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end.


Fixpoint leb' (n m : nat) : bool :=
  match n, m with 
  | 0, _ => true
  | S n', 0 => false
  | S n', S m' => leb' n' m'
  end.

(* ex.2.6*)
(* Cnanot guess decreasing argument of fix.
Fixpoint ackermann (m n: nat) : nat :=
    match m with
    | 0 => n + 1
    | S m' =>
        match n with
        | 0 => ackermann m' 1
        | S n' => ackermann m' (ackermann m n')
        end
    end.
*)
  
Fixpoint Ackermann (m n: nat) {struct m} : nat :=
    match m with
      | O => S n
      | S m' =>  let fix Ackermann' (n : nat) {struct n} : nat :=
                  match n with
                    | O => Ackermann m' 1
                    | S n' =>  Ackermann m' (Ackermann' n')
                    end
  in Ackermann' n
end.

(* ex.2.7*)
Inductive natpair: Type :=
  |pair (n1 : nat) (n2 : bool).

Check (pair 100 true) : natpair.


(* ex.2.8*)
Fixpoint rev (l : list nat) := 
  match l with
  | [] => []
  | h :: t => rev t ++ [h]
  end.

(* ex.2.9*)
Fixpoint createList (n : nat) : list nat :=
  match n with 
  | 0 => []
  | S n' => createList n' ++ [n]
  end.

(* ex.2.10*)
Fixpoint createList' (n : nat) : list nat :=
  match n with 
  | O => []
  | S O => [1]
  | S n' => [n] ++ createList' n' ++ [n]
end.

(* ex.2.11*)
Fixpoint fib_direct (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib_direct n' + fib_direct n''
              end
  end.
Fixpoint fib_accumulator (n : nat) (a : nat) (b : nat) : nat :=
  match n with
    | 0     => b
    | (S n') => fib_accumulator n' (a+b) a
  end.

Fixpoint fib (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | 1 => [0;1]
  | S n' => fib n' ++ [fib_direct n]
  end.

Compute (fib 8).

(* ex.2.12*)
Definition swap (l : list nat) : list nat := 
  match l with
  | [] => []
  | h :: t => match rev t with 
              | [] => [h]
              | h' :: t' => h' :: rev t'++ [h]
              end
  end.

Example test_swap : swap [1;2;3;4;5] = [5;2;3;4;1].
Proof. reflexivity. Qed.

(* ex.2.13*)
Fixpoint sort (L : list nat) : list nat :=
  match L with
  | [] => []
  | h :: tl =>
         let fix insert (x : nat)(l : list nat) : list nat :=
           match l with
           | [] => [x]
           | a :: l' => if (leb x a) then x :: l
                        else a :: insert x l'
           end
         in insert h (sort tl)
end.
Example test_sort : sort [2;4;1;6;9;6;4;1;3;5;10] =
                         [1;1;2;3;4;4;5;6;6;9;10].
Proof. reflexivity. Qed.

(* ex.2.14*)
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

Fixpoint occur (n : nat) (t : btree) : bool :=
  match t with
  | leaf v => eqb n v
  | node v t1 t2 => (eqb n v) || (occur n t1) || (occur n t2)
  end.

Example occur_text1 : occur 6 (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
  (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
= true.
Proof. reflexivity. Qed.


Example occur_text2 : occur 100 (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
  (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
= false.
Proof. reflexivity. Qed.


Fixpoint countEven (t : btree) : nat :=
  match t with
  | leaf v => match (even v) with 
              | true => 1
              | false => 0
              end
  | node v t1 t2 => match (even v) with
                    | true => 1 + (countEven t1) + (countEven t2)
                    | false => (countEven t1) + (countEven t2)
                    end 
  end.

Example countEven_test : countEven (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
  (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
= 6.
Proof. reflexivity. Qed.


(* ex.2.15*)
Require Import Unicode.Utf8.
Require Import Utf8_core.
Require Import List.
Require Import Program.Equality.

Inductive type : Set :=
  | tau : type
  | arr : type → type → type.

Inductive term : Set :=
  | var : nat → term
  | abs : type → term → term
  | app : term → term → term.

Definition dec (Γ : list type) x τ : Prop :=
  nth_error Γ x = Some τ.

Inductive J (Γ : list type) : term → type → Set :=
  | tvar : ∀ x τ, dec Γ x τ → J Γ (var x) τ
  | tabs : ∀ τ₁ τ₂ e, J (τ₁ :: Γ) e τ₂ → J Γ (abs τ₁ e) (arr τ₁ τ₂)
  | tapp : ∀ τ₁ τ₂ e₁ e₂, J Γ e₁ (arr τ₁ τ₂) → J Γ e₂ τ₁ → J Γ (app e₁ e₂) τ₂.

Lemma unique_variable_type :
  forall G x t1 t2, dec G x t1 -> dec G x t2 -> t1 = t2.
Proof.
  unfold dec; intros.
  assert (value t1 = value t2). congruence.
  inversion H1. reflexivity.
Qed.

Axiom unique_variable_type_derivation :
  forall G x t (d1 d2 : dec G x t), d1 = d2.

Lemma unique_type : forall G e t1 t2 (d1 : J G e t1) (d2 : J G e t2), t1 = t2.
Proof.
  intros G e; generalize dependent G.
  induction e; intros.

  dependent destruction d1. dependent destruction d2.
  apply (unique_variable_type G n); assumption.

  dependent destruction d1. dependent destruction d2.
  firstorder congruence.

  dependent destruction d1. dependent destruction d2.
  assert (arr τ₁ τ₂ = arr τ₁0 τ₂0).
  firstorder congruence.
  congruence.
Qed.

Lemma unique_derivation : forall G e t (d1 d2 : J G e t), d1 = d2.
Proof.
  intros G e; generalize dependent G.
  induction e; intros.

  dependent destruction d1. dependent destruction d2.
  f_equal. solve [apply (unique_variable_type_derivation G n)].

  dependent destruction d1. dependent destruction d2.
  f_equal. solve [apply IHe].

  dependent destruction d1. dependent destruction d2.
  assert (τ₁ = τ₁0). 2: subst τ₁.
  solve [eapply unique_type; eauto].
  f_equal; solve [firstorder].
Qed.

(* ex.2.16*)
Inductive btree' : Set :=
 | leaf' : btree'
 | node' : nat -> btree' -> btree' -> btree'.

Check (node' 5 (node' 1 (leaf') (node' 3 (leaf') (leaf'))) 
(node' 9 (node' 7 (leaf') (leaf')) (leaf'))).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list.
(* list : Type -> Type *)
Check (nil nat).
(* nil nat : list nat *)
Check (cons bool true (nil bool)).
(* cons bool true (nil bool) : list bool *)

Check nil.
(* nil : forall X : Type, list X *)
Check cons.
(* cons : forall X : Type, X -> list X -> list X *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
end.

Compute repeat bool true 1.
(* = cons bool true (nil bool) : list bool *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.
Arguments app {X}.
Check cons 1 (cons 3 nil).
(* cons 1 (cons 3 nil) : list nat *)
Compute repeat true 2.
(* = cons true (cons true nil) : list bool *)

Fixpoint repeat' {X : Type} (x : X) (count : nat) : list X :=
match count with
| 0 => nil
| S count' => cons x (repeat' x count')
end.
Compute repeat' 1 3.
(* = cons 1 (cons 1 (cons 1 nil)) : list nat *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* ex.2.17*)

(* ex.2.18*)
Fixpoint last' (X : Type) (l: list X) : list X :=
  match l with
    | [] => []
    | [a] => [a]
    | a :: l => last' X l
    end.

 Fixpoint removelast (X : Type) (l: list X) : list X:=
    match l with
      | [] => []
      | [a] => []
      | a :: l => a :: removelast X l
    end.

Fixpoint app' (X : Type) (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | h :: l1' => h :: app' X l1' l2
  end.

Definition rotate (X : Type) (l: list X) : list X :=
  app' X (last' X l) (removelast X l).

Example rotate_test1 : rotate nat [1;2;3;4;5] = [5;1;2;3;4].
Proof. reflexivity. Qed.

Example rotate_test2 : rotate bool [true; false] = [false; true].
Proof. reflexivity. Qed.

Example rotate_test3 : rotate nat [2] = [2].
Proof. reflexivity. Qed.


(* ex.2.19*)
Inductive pair_poly (X:Type) : Type :=
  | pair' (x1 : X) (x2 : X).


Fixpoint list_pair (X : Type) (l : list X) (v : X) : list (pair_poly X)  :=
  match l with
  | [] => []
  | h :: l' => (pair' X h v) :: (list_pair X l' v)
  end.


Fixpoint product (X : Type) (l1 l2 : list X) : list (pair_poly X):=
  match l2 with 
  | nil => nil
  | h :: t => app' (pair_poly X) (list_pair X l1 h) (product X l1 t)
  end.



(* ex.2.20*)

Fixpoint insert_list (x : nat) (l : list (list nat))
                                  : list (list nat) :=
  match l with
  | [] => []
  | h :: tl => (x :: h) :: insert_list x tl
  end.

  Fixpoint powerset (L : list nat) : list (list nat) :=
    match L with
    | [] => [[]]
    | h :: tl => let pl := powerset tl in
                 app' (list nat) pl (insert_list h pl)
    end.

Example test_powerset1: powerset [1;2;3] = [[ ]; [3]; [2]; [2; 3];
    [1]; [1; 3]; [1; 2]; [1; 2; 3]].
Proof. reflexivity. Qed.
Example test_powerset2: powerset [1;2;3;4] = [[ ]; [4]; [3]; [3; 4];
    [2]; [2; 4]; [2; 3]; [2; 3; 4];
    [1]; [1; 4]; [1; 3]; [1; 3; 4];
    [1; 2]; [1; 2; 4]; [1; 2; 3];
    [1; 2; 3; 4]].
Proof. reflexivity. Qed.

Definition twice {X : Type} (f : X -> X) (n : X) : X := f (f n).

Check @twice.
Compute twice S 2.
(* = 4 : nat *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
end.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
end.
Compute map (fun n => n + 5) [1;3;5].
(* = [6;8;10] : list nat *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
Compute fold plus [1;3;5] 0.
(* = 9 : nat *)

(* ex.2.21*)
Fixpoint divide3 (n:nat) : bool :=
  match n with
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => true
  | S(S(S n')) => divide3 n'
  end.

Definition filt1(n:nat) : bool :=
  (divide3 n).

Definition filt2(n:nat) : bool :=
  negb(divide3 n).


Definition partition (l : list nat) : list (list nat) :=
  [ filter filt1 l ; filter filt2 l].


(* ex.2.22*)
Inductive gt : nat -> nat -> Prop :=
  | gtn (n : nat) : gt (S n) n
  | gtS (n m : nat) (H : gt n m) : gt (S n) m.

Theorem gt5 : gt 5 3.
Proof. apply gtS. apply gtn. Qed.

(* ex.2.23*)
Inductive subseq : list nat -> list nat -> Prop :=
  | sub1 l : subseq nil l
  | sub2 l1 l2 a (H : subseq l1 l2) : subseq l1 (a :: l2)
  | sub3 l1 l2 a (H : subseq l1 l2) : subseq (a :: l1) (a :: l2).


Theorem subseq1 : subseq [1;2;3] [1;1;4;6;2;7;2;3;9].
Proof. apply sub3. apply sub2. apply sub2. apply sub2. apply sub3.
apply sub2. apply sub2. apply sub3. apply sub1. Qed.

(* ex.2.24*)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. intros. induction n.
+ simpl. reflexivity.
+ Search (S _ + _). rewrite PeanoNat.Nat.add_succ_comm.
  rewrite PeanoNat.Nat.add_succ_l. reflexivity.
  Qed.

