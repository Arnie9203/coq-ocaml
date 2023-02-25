(*[Proof of de Morgan laws with coq]*)
(*{NOTE: coq tactics for Propositional Logic]
  |- A -> B       =intro A1=> A1: A |- B
  |- A -> B -> C  =intros A1 B1=> A1: A, B1: B |- C
  |- A\/B         =left=> |- A
  |- A\/B         =right=> |- B
  |- A/\B         =split=> |- A ; |- B
  |- False        =absurd (A)=> |- ~A ; |- A

  AB: A->B |- B   =apply AB=> AB: A->B |- A
  AB: A/\B |- C   =destruct AB as [A1 B1]=> A1: A, B1: B |- C
  AB: A\/B |- C   =destruct AB as [A1 | B1]=> A1: A |- C ; B1: B |- C
  NA: ~A |- False =apply NA=> |- A
*)

Theorem deMorgan1 (A B: Prop): ~(A\/B) -> ~A/\~B.
Proof.
  intro NAB.
  split.

  (* NAB: ~(A\/B) |- ~A *)
  - intro A1.
    apply NAB.
    left.
    exact A1.

  (* NAB ~(A\/B) |- ~B *)
  - intro B1.
    apply NAB.
    right.
    exact B1.
Qed.

Print deMorgan1.

(* embed body code for the type with `refine` tactic*)
Theorem deMorgan1b (A B: Prop): ~(A\/B) -> ~A/\~B.
Proof.
  intro NAB.
  refine (conj (fun A1: A => NAB (or_introl A1))
               (fun B1: B => NAB (or_intror B1))).
Qed.

Print deMorgan1b.


Theorem deMorgan2 (A B: Prop): ~A/\~B -> ~(A\/B).
Proof.
  intros NANB AB.
  destruct NANB as [NA NB].
  destruct AB as [A1 | B1].

  (* NA:~A, NB:~B A1:A |- False *)
  - apply NA.
    exact A1.

  (* NA:~A, NB:~B B1:B |- False *)
  - apply NB.
    exact B1.
Qed.

Print deMorgan2.


(* with `case` tactic instread of both `destruct`*)
Theorem deMorgan2b (A B: Prop): ~A/\~B -> ~(A\/B).
Proof.
  intros NANB AB.
  case AB.

  (* NANB:~A/\~B |- A->False *)
  - intro A1.
    case NANB.
    (* A1: A |- ~A->~B->False *)
    intros NA NB.
    apply NA.
    exact A1.

  (* NANB:~A/\~B |- B->False *)
  - intro B1.
    case NANB.
    (* B1: B |- ~A->~B->False *)
    intros NA NB.
    apply NB.
    exact B1.
Qed.

Print deMorgan2b.


Theorem deMorgan3 (A B: Prop): ~A\/~B -> ~(A/\B).
Proof.
  intros NANB AB.
  destruct AB as [A1 B1].
  destruct NANB as [NA | NB].

  (* A1: A, B1: B, NA:~A |- False *)
  - apply NA.
    exact A1.

  (* A1: A, B1: B, NB:~B |- False *)
  - apply NB.
    exact B1.
Qed.

Print deMorgan3.


(*
   This case of demorgan requires the axiom NNPP: ~~A -> A
   - same as: (~A->False)->A , or as: ((A->False)->False)->A
   |- A =apply NNPP=> |- ~A->False
*)
Require Import Classical.
Theorem deMorgan4 (A B: Prop): ~(A/\B) -> ~A\/~B.
Proof.
  intro NAB.
  apply NNPP.
  intro NNANB.
  apply NAB.
  split.

  (* NNANB: ~(~A\/~B) |- A *)
  - apply NNPP.
    intro NA.
    apply NNANB.
    left.
    exact NA.

  (* NNANB: ~(~A\/~B) |- B *)
  - apply NNPP.
    intro NB.
    apply NNANB.
    right.
    exact NB.
Qed.

Print deMorgan4.


(*[NOTE: Prop types on coq]
  Type hierarchy
  - Type: Type
  - Set Prop: Type
  - nat bool: Set    (builtin value types)
  - True False: Prop
  - A B C ... : Prop (user defined propositions)

  I: True
   : False (no functions of False type existed)
  
  and A B := conj: A->B->A/\B
  or A B := or_introl A->A\/B
          | or_introl B->A\/B

  ~A == A -> False  
*)

(*[Appendix: traditional proof tree rules of /\-elim \/-elim with coq]
  and_ind: (A->B->P) -> (A/\B) -> P
  or_ind: (A->P) -> (B->P) -> (A\/B) -> P

  |- P =apply and_ind with A B=> |- A->B->P ; |- A/\B->P
  |- P =apply or_ind with A B=> |- A->P ; |- B->P ; |- A\/B->P

  
  |- A ==> |- A/\B                 (and-l-elim)
  |- B ==> |- A/\B                 (and-r-elim)
  |- C ==> |- A\/B ; A |- C; B |- C  (or-elim)
 *)
(* make custom tactic for and-l-elim / and-r-elim *)
Theorem and_elim_l (A B: Prop): A/\B->A.
Proof.
  intro AB.
  apply and_ind with A B.
  (* AB: A/\B |- A->B->A *)
  - intros A1 B1.
    exact A1.
  (* AB: A/\B |- A/\B *)
  - exact AB.
Qed.
Theorem and_elim_r (A B: Prop): A/\B->B.
Proof.
  intro AB.
  apply and_ind with A B.
  (* AB: A/\B |- A->B->B *)
  - intros A1 B1.
    exact B1.
  (* AB: A/\B |- A/\B *)
  - exact AB.
Qed.
Ltac and_l_elim B := apply and_elim_l with B.
Ltac and_r_elim A := apply and_elim_r with A.

(* with traditional axiom style: and_elim_l and_elim_r *)
Theorem and_refl0 (A B: Prop): A/\B -> B/\A.
Proof.
  intro AB.
  split.
  
  (* AB: A/\B |- B *)
  - and_r_elim A.
    (* AB: A/\B |- A/\B *)
    exact AB.
      
  (* AB: A/\B |- A *)
  - and_l_elim B.
    (* AB: A/\B |- A/\B *)
    exact AB.
Qed.

(* with applying and_ind directly *)
Theorem and_refl (A B: Prop): A/\B -> B/\A.
Proof.
  intro AB.
  split.
  
  (* AB: A/\B |- B *)
  - apply and_ind with A B.
    (* AB: A/\B |- A->B->B *)
    + intros A1 B1.
      exact B1.
    (* AB: A/\B |- A/\B *)
    + exact AB.
      
  (* AB: A/\B |- A *)
  - apply and_ind with A B.
    (* AB: A/\B |- A->B->A *)
    + intros A1 B1.
      exact A1.
    (* AB: A/\B |- A/\B *)
    + exact AB.
Qed.

(* or_ind is same as traditional axiom:  or_elim *)
Theorem or_refl (A B: Prop): A\/B -> B\/A.
Proof.
  intro AB.
  apply or_ind with A B.

  (* AB: A\/B |- A->B\/A *)
  - intro A1.
    right.
    exact A1.
    
  (* AB: A\/B |- B->B\/A *)
  - intro B1.
    left.
    exact B1.
    
  (* AB: A/\B |- A/\B *)
  - exact AB.
Qed.

(*
  [How to use this on coqtop]
  $ coqc demorgan.v
  $ ledit coqtop
  Coq < Require Import demorgan.
  Coq < Print deMorgan0.
  deMorgan0 =
  fun (A B : Prop) (NAB : ~ (A \/ B)) =>
  conj (fun A1 : A => NAB (or_introl A1)) (fun B1 : B => NAB (or_intror B1))
       : forall A B : Prop, ~ (A \/ B) -> ~ A /\ ~ B
  
  Argument scopes are [type_scope type_scope _]
  
  Coq <
*)
