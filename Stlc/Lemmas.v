Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Program.
Require Import Coq.Classes.EquivDec.
Require Import Arith.
Close Scope program_scope.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Import Coq.Classes.RelationClasses.
Require Import Lia.

Require Import Stlc.DefinitionsSyntax.
Require Import Coq.Logic.StrictProp.
From mathcomp Require Import ssrnat ssrbool ssreflect.
From Hammer Require Import Tactics.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* This file was originally produced by the LNgen tool. It has been modified to 
   use the well-scoped expressions.
*)

(* *********************************************************************** *)
(** * Tactic support *)


(* Simplify the equations versions of the functions. *)

(* like an inversion tactic for equalities *)

(** Additional hint declarations. *)

(* Can't do this automatically b/c we need to have the 
   equality around. But then the option in the equality
   will also be eliminated if this tactic is repeated. *)
Ltac destruct_option :=
  let rec main x :=
    let h := fresh "EQ" in
    match type of x with
      | option _ => destruct x eqn:h
    end
  in
  match goal with
    | |- context [?x] => main x
    | H : _ |- _ => main H
    | _ : context [?x] |- _ => main x
  end.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].

(* *********************************************************************** *)
(** * Theorems about [weaken] *)

Ltac default_auto ::= auto with arith lngen; tauto.


Lemma size_exp_weaken_exp :
(forall n1 (e1 : exp n1),
  size_exp (weaken_exp e1) = size_exp e1).
Proof.
  move => n e.
  elim : n / e; hauto lq:on rew:off.
Qed.

#[global] Hint Resolve size_exp_weaken_exp : lngen.
#[export] Hint Rewrite size_exp_weaken_exp using solve [auto] : lngen.  
#[export] Hint Rewrite size_exp_weaken_exp : weaken_exp.

Lemma fv_exp_weaken_exp : 
(forall n1 (e1 : exp n1),
  fv_exp (weaken_exp e1) = fv_exp e1).
Proof. 
  intros n1 e1.
  dependent induction e1; hauto lq:on.
Qed.

#[global] Hint Resolve fv_exp_weaken_exp : lngen.
#[export] Hint Rewrite fv_exp_weaken_exp using solve [auto] : lngen.  
#[export] Hint Rewrite fv_exp_weaken_exp : weaken_exp.  

(* *********************************************************************** *)
(** * Theorems about [size] *)

Lemma size_exp_min :
(forall n (e1 : exp n), (1 <= size_exp e1)%nat).
Proof.
  intros n e1.  dependent induction e1; default_simp.
Qed.

#[global] Hint Resolve size_exp_min : lngen.

Lemma size_exp_close_exp_wrt_exp :
(forall n1 (e1 : exp n1) x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1).
Proof.
  intros n1 e1 x1.
  elim : n1 / e1;
    first (simpl;
           move => n m h;
           case : ltnP;
           sfirstorder).
  all : hauto lq:on.
Qed.

#[global] Hint Resolve size_exp_close_exp_wrt_exp : lngen.

Lemma size_exp_open_exp_wrt_exp :
(forall k (e1 : exp (S k)) (e2 : exp k),
  ((size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2))%nat)).
Proof.
  move => k h.
  dependent induction h.
  - simpl.
    move => e2.

  - simpl. lia.
  - sfirstorder inv:exp,le ctrs:le solve:lia.
  - hfcrush solve:lia.
Qed.

Lemma size_exp_open_exp_wrt_exp_var :
(forall k (e : exp (S k)) x,
  size_exp (open_exp_wrt_exp e (var_f x)) = size_exp e).
Proof.
intros k e x.
dependent induction e.
- simpl.
  
hauto q:on.
Qed.

#[global] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.


Lemma close_exp_wrt_exp_inj :
(forall k (e1 : exp k) e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2).
Proof.
  move => k e1 e2 x1.
  move : e2.
  elim : k / e1.
  - dependent inversion e2.
    + simpl.
      case ltnP => h0.
      * case ltnP => h1.
        hauto lq:on.
        case => ?; subst.
        apply sEmpty_ind.
        inversion s; inversion s0.
        exfalso; lia.
      * case ltnP => h1; last hauto lq:on.
        case => ?; subst.
        apply sEmpty_ind.
        inversion s; inversion s0.
        exfalso; lia.
    + simpl.
      case ltnP => h0.
      * case : eq_dec => ?; subst; last sfirstorder.
        simpl.
        case => ?; subst.
        lia.
      * case : eq_dec => ?; subst; last sfirstorder.
        simpl.
        case => ?; subst.
        lia.
    + move => /=.
      case : ltnP; sfirstorder.
    + move => /=.
      case : ltnP; sfirstorder.
  - dependent inversion e2.
    + simpl.
      case : ltnP; case : eq_dec => ? /=; subst.
      move => ? [?]; subst; lia.
      sfirstorder.
      move => ? [?]; subst; lia.
      sfirstorder.
    + simpl.
      case : eq_dec => ?; subst;
      case : eq_dec => ?; subst; scongruence.
    + simpl.
      case : eq_dec => ?; subst; scongruence.
    + simpl.
      case : eq_dec => ?; subst; scongruence.
  - dependent inversion e2.
    + simpl.
      case : ltnP; subst; sfirstorder.
    + simpl.
      case : eq_dec; subst; sfirstorder.
    + hauto lq:on rew:off.
    + scongruence.
  - dependent inversion e0.
    simpl.
    + case : ltnP; subst; sfirstorder.
    + simpl.
      case : eq_dec; subst; sfirstorder.
    + hauto lq:on rew:off.
    + hauto lq:on rew:off.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
(forall n1 (e1 : exp (S n1)) x1 ,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (var_f x1)) = e1).
Proof.
intros. 
dependent induction e1; simpl; default_simp.
- case : m s H.
  simpl.
  case : eq_dec => /=.

all: simp_stlc.
all: default_simp.
destruct decrease_fin eqn:EQ; default_simp. 
Qed.

#[global] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen. 


Lemma open_exp_wrt_exp_close_exp_wrt_exp :
(forall n1 (e1 : exp n1) x1,
  open_exp_wrt_exp (var_f x1) (close_exp_wrt_exp x1 e1) = e1).
Proof.
  intros n1 e1. dependent induction e1; default_simp.
Qed.

#[global] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.


Lemma open_exp_wrt_exp_inj :
(forall n1 (e2 e1:exp (S n1)) x1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp (var_f x1) e2 = open_exp_wrt_exp (var_f x1) e1 ->
  e2 = e1).
Proof.
 intros k e2 e1 x FV1 FV2.  
 dependent induction e1; dependent induction e2.
 all: simp open_exp_wrt_exp in *. 
 all: try destruct (decrease_fin k f0) eqn:E1. 
 all: try destruct (decrease_fin k f) eqn:E2. 
 all: simp open_exp_wrt_exp in *; simpl in *.
 all: intros h.
 all: noconf h.
 all: default_simp.
 all: try (rewrite <- E1 in E2; apply decrease_fin_inj in E2).
 all: eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_inj : lngen.

(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= simp_stlc.

Lemma close_exp_wrt_exp_weaken_exp :
(forall n1 (e1 : exp n1) x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 e1 = weaken_exp e1).
Proof.
intros.
dependent induction e1; default_simp.
Qed.

#[global] Hint Resolve close_exp_wrt_exp_weaken_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_weaken_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_weaken_exp :
forall n1 (e2 : exp n1) e1,
  open_exp_wrt_exp e1 (weaken_exp e2) = e2.
Proof.
intros n1 e2.
dependent induction e2; default_simp.
Qed.
#[global] Hint Resolve open_exp_wrt_exp_weaken_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_weaken_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen; simp_stlc.

Lemma fv_exp_close_exp_wrt_exp :
(forall n1 (e1 : exp n1) x1,
  fv_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_exp e1)).
Proof.
dependent induction e1; default_simp; fsetdec. 
Qed.

#[global] Hint Resolve fv_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite fv_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fv_exp_open_exp_wrt_exp_lower :
(forall n1 (e1 : exp (S n1)) (e2 : exp n1),
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp e2 e1)).
Proof.
  intros n1 e1 e2.
  funelim  (open_exp_wrt_exp e2 e1); 
    simp_stlc;
    try destruct (decrease_fin k f); 
    default_simp; fsetdec.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_lower : lngen.

Lemma fv_exp_open_exp_wrt_exp_upper :
(forall n1 (e1 : exp (S n1)) (e2 : exp n1),
  fv_exp (open_exp_wrt_exp e2 e1) [<=] fv_exp e2 `union` fv_exp e1).
Proof.
  intros n1 e1 e2.
  funelim (open_exp_wrt_exp e2 e1); simp_stlc. 
  all: try destruct decrease_fin; default_simp. 
  simp lngen in H.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_upper : lngen.

Lemma fv_exp_subst_exp_wrt_exp_fresh :
(forall n1 (e1 : exp n1) e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (subst_exp_wrt_exp e2 x1 e1) [=] fv_exp e1).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_fresh : lngen.
#[export] Hint Rewrite fv_exp_subst_exp_wrt_exp_fresh using solve [auto] : lngen.

Lemma fv_exp_subst_exp_wrt_exp_lower :
(forall n1 (e1 : exp n1) e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (subst_exp_wrt_exp e2 x1 e1)).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
fsetdec.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_lower : lngen.

Lemma fv_exp_subst_exp_wrt_exp_notin :
(forall n1 (e1 : exp n1) e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (subst_exp_wrt_exp e2 x1 e1)).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
eapply IHe1; default_simp. 
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_notin : lngen.

Lemma fv_exp_subst_exp_wrt_exp_upper :
(forall n1 (e1 : exp n1) e2 x1,
  fv_exp (subst_exp_wrt_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1)).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
fsetdec.
specialize (IHe1 (weaken_exp e2)).
simp weaken_exp in IHe1.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= simp_stlc; autorewrite with lngen.

Lemma subst_exp_close_exp_wrt_exp :
forall n1 (e2 : exp n1) (e1 : exp n1) x1 x2,
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp_wrt_exp (weaken_exp e1) x1 (close_exp_wrt_exp x2 e2) =
        close_exp_wrt_exp x2 (subst_exp_wrt_exp e1 x1 e2).
Proof.
intros n1 e2.
dependent induction e2. 
all: default_simp.
specialize (IHe2 (weaken_exp e1)).
eapply IHe2; default_simp. 
Qed.


#[global] Hint Resolve subst_exp_close_exp_wrt_exp : lngen.


Lemma subst_exp_wrt_exp_fresh_eq :
forall n1 (e2 : exp n1) e1 x1,
  x1 `notin` fv_exp e2 ->
  subst_exp_wrt_exp e1 x1 e2 = e2.
Proof.
  intros. 
  dependent induction e2; default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_wrt_exp_fresh_eq using solve [auto] : lngen.

Lemma subst_exp_wrt_exp_fresh_same :
(forall n1 (e2 : exp n1) e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp_wrt_exp e1 x1 e2)).
Proof.
intros n1 e2.
dependent induction e2; default_simp.
eapply IHe2; default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_fresh_same : lngen.

Lemma subst_exp_wrt_exp_fresh :
(forall n1 (e2:exp n1) e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp_wrt_exp e1 x2 e2)).
Proof.
intros n1 e2.
dependent induction e2; default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_fresh : lngen.

Lemma subst_exp_wrt_exp_weaken_exp : 
  forall n (e1 : exp n) x1 u,
    weaken_exp (subst_exp_wrt_exp e1 x1 u) = 
    subst_exp_wrt_exp (weaken_exp e1) x1 (weaken_exp u).
Proof.
  intros n e1 x1 u.
  dependent induction u; default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_weaken_exp : lngen.
#[export] Hint Rewrite subst_exp_wrt_exp_weaken_exp : lngen.

(* SCW: this one might be simpler if we only substitute 
   locally closed terms *)
Lemma subst_exp_open_exp_wrt_exp :
(forall n1 (e1 : exp n1) e2 (e3 : exp (S n1)) x1,
  subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp e2 e3) =
    open_exp_wrt_exp (subst_exp_wrt_exp e1 x1 e2) 
                         (subst_exp_wrt_exp (weaken_exp e1) x1 e3)).
Proof.
intros n1 e1 e2 e3 x1.
funelim (open_exp_wrt_exp e2 e3).
all: default_simp.
all: destruct (decrease_fin k m) eqn:E1; default_simp.
Qed.

#[global] Hint Resolve subst_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_open_exp_wrt_exp_var :
forall n1 (e2 : exp (S n1)) e1 x1 x2,
  x1 <> x2 ->
  open_exp_wrt_exp (var_f x2) (subst_exp_wrt_exp (weaken_exp e1) x1 e2) = 
    subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp (var_f x2) e2).
Proof.
intros; default_simp.
rewrite subst_exp_open_exp_wrt_exp.
default_simp.
Qed.

#[global] Hint Resolve subst_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_wrt_exp_spec :
(forall n (e1 e2 : exp n) x1,
  subst_exp_wrt_exp e2 x1 e1 = open_exp_wrt_exp e2 (close_exp_wrt_exp  x1 e1)).
Proof.
intros n e1 e2 x1.
dependent induction e1.
all: default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_spec : lngen.

Lemma subst_exp_wrt_exp_subst_exp_wrt_exp :
(forall n (e1 e2 e3 : exp n) x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  subst_exp_wrt_exp e2 x1 (subst_exp_wrt_exp e3 x2 e1) = 
    subst_exp_wrt_exp (subst_exp_wrt_exp e2 x1 e3) x2 (subst_exp_wrt_exp e2 x1 e1)).
Proof.
intros n e1.
dependent induction e1; intros.
all: default_simp.
rewrite IHe1; 
default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_subst_exp_wrt_exp : lngen.

Lemma subst_exp_wrt_exp_close_exp_wrt_exp_open_exp_wrt_exp :
(forall n1 (e2 : exp (S n1)) e1 x1 x2,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  subst_exp_wrt_exp (weaken_exp e1) x1 e2 = 
    close_exp_wrt_exp x2 
       (subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp (var_f x2) e2))).
Proof.
intros n e2.
dependent induction e2; intros.
all: default_simp.
all: try destruct (decrease_fin n f) eqn:E.
all: default_simp.
symmetry. eauto using decrease_increase_fin.
symmetry. eauto using decrease_to_fin.
specialize (IHe2 _ e2 ltac:(auto) ltac:(auto)).
specialize (IHe2 (weaken_exp e1)).
eapply IHe2; eauto.
all: default_simp. 
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

(*
Lemma subst_exp_wrt_exp_abs :
forall x2 (e2 : exp 1) (e1 : exp 0) x1,
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  subst_exp_wrt_exp e1 x1 (abs e2) = 
    abs (close_exp_wrt_exp x2 (subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp (var_f x2) e2))).
Proof.
default_simp. 
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_abs : lngen.
*)

Lemma subst_exp_wrt_exp_intro :
forall n1 (e1 : exp (S n1)) x1 e2,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e2 e1 = subst_exp_wrt_exp e2 x1 (open_exp_wrt_exp (var_f x1) e1).
Proof.
dependent induction e1; default_simp.
all: try destruct decrease_fin eqn:E.
all: default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_intro : lngen.
#[export] Hint Rewrite subst_exp_wrt_exp_intro using solve [auto] : lngen.

(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
