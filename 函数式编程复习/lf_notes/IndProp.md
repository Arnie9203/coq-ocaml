```ocaml
Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.
  
Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then 0
  else 1 + reaches_1_in (f n).

(** This definition is rejected by Coq's termination checker, since the argument to the recursive call, [f n], is not "obviously smaller" than [n]. **)

Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

(** The details of such definitions are written will be explained
    below; for the moment, the way to read this one is: "The number
    [1] reaches [1], and any number [n] reaches [1] if [f n] does." *)

```





```ocaml
Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

(** **** Exercise: 1 star, standard, optional (close_refl_trans)

    How would you modify this definition so that it defines _reflexive
    and_ transitive closure?  How about reflexive, symmetric, and
    transitive closure? *)
```







```ocaml
(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of [n] holds for all even numbers (i.e.,
    those for which [ev n] holds), we can use induction on [ev
    n]. This requires us to prove two things, corresponding to the two
    ways in which [ev n] could have been constructed. If it was
    constructed by [ev_0], then [n=0] and the property must hold of
    [0]. If it was constructed by [ev_SS], then the evidence of [ev n]
    is of the form [ev_SS n' E'], where [n = S (S n')] and [E'] is
    evidence for [ev n']. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for [n']. *)

(** Let's try proving that lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even E' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.
```





```ocaml
Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the [Logic]
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split.
  - (* -> *) intro EN.
    induction EN.
    + (* ev 0 *) apply ev_0.
    + (* ev 2 *) apply ev_SS. apply ev_0.
    + (* ev (n + m) *) apply ev_sum.
      * (* ev n *) apply IHEN1.
      * (* ev m *) apply IHEN2.
  - (* -> *) intro EN.
    induction EN as [|n' EN' IHen].
    + (* ev' 0 *) apply ev'_0.
    + (* ev' (S (S n')) *) assert (H : (S (S n') = 2 + n')).
      { reflexivity. }
      rewrite -> H. apply ev'_sum.
      * (* ev' 2 *)apply ev'_2.
      * (* ev' n *) apply IHen.
Qed.


(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint: Is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  assert (HH : (ev (n + m) -> ev ((n + p) + (m + p)))).
{ 
  intro H. Search (_ + (_ + _) = (_ + _) + _).
(*
plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p
*)
(*
plus_comm : forall n m : nat, n + m = m + n
*)
(* TARGET: n + m + (p + p) || (p + p) + (n + m) *)
(* n + p + (m + p) == (n + p) + (m + p) *)
(* assoc: n + (p + (m + p)) *)
  rewrite <- (add_assoc n p (m + p)).
(* assoc: n + ((p + m) + p) *)
  rewrite (add_assoc p m p).
(* comm: n + ((p + m) + p) *)
  rewrite (add_comm p m).
(* assoc: (n + (m + p) + p *)
  rewrite add_assoc.
(* assoc: ((n + m) + p) + p *)
  rewrite add_assoc.
(* assoc: (n + m) + (p + p) *)
  rewrite <- (add_assoc (n + m) p).
  apply (ev_sum (n + m) (p + p)).
  - apply H.
  - rewrite <- double_plus. apply ev_double.
}
  apply HH in Hnm. apply (ev_ev__ev (n + p)).
  - apply Hnm.
  - apply Hnp.
Qed.
```

