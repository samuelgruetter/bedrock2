Require Import Program.Tactics.
Require Import lib.LibTacticsMin.
Require Import Coq.Logic.ClassicalFacts.
Require Import compiler.util.Common.
Require Import lib.fiat_crypto_tactics.Not.
Require Import lib.fiat_crypto_tactics.UniquePose.

Section StateCalculus.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.
  Context {stateMap: MapFunctions var val}.
  Notation state := (map var val).
  Context {eq_var_dec: DecidableEq var}.
  Context {varset: SetFunctions var}.
  Notation vars := (set var).

  Definition extends(s1 s2: state) := forall x w, get s2 x = Some w -> get s1 x = Some w.

  Definition only_differ(s1: state)(vs: vars)(s2: state) :=
    forall x, x \in vs \/ get s1 x = get s2 x.

  Definition agree_on(s1: state)(vs: vars)(s2: state) :=
    forall x, x \in vs -> get s1 x = get s2 x.

  Definition undef(s: state)(vs: vars) := forall x, x \in vs -> get s x = None.

  Lemma get_put: forall (s: state) (x y: var) (v: val),
    get (put s x v) y = if dec (x = y) then Some v else get s y.
  Proof.
    intros. destruct (dec (x = y)).
    - subst. rewrite get_put_same. reflexivity.
    - rewrite get_put_diff by assumption. reflexivity.
  Qed.
  
  Lemma only_differ_putmany : forall (bs : list var) (vs : list val) st st' 
                                     (H : putmany bs vs st = Some st'),
      only_differ st (fold_right union empty_set (List.map singleton_set bs)) st'.
    induction bs, vs; cbn; try discriminate.
    { inversion 1; subst. cbv; eauto. }
    { intros ? ? H; destruct (putmany bs vs st) eqn:Heqo; [|discriminate].
      inversion H; subst.
      specialize (IHbs _ _ _ Heqo).
      intros x; destruct (IHbs x);
        autorewrite with rew_set_op_specs in *; rewrite ?get_put;
          destruct (dec (a=x)); eauto. }
  Qed.
End StateCalculus.

Hint Unfold extends only_differ agree_on undef : unf_state_calculus.

Ltac rewrite_get_put :=
  rewrite? get_put in *;
  (* the above line is sometimes not enough, so be more explicit: *)
  repeat match goal with
  | H: _ |- _ => rewrite? get_put in H
  end.

Ltac state_calc_generic varT valT :=
  repeat autounfold with unf_state_calculus in *;
  intros;
  repeat autounfold with unf_set_defs in *;
  destruct_products;
  intros;
  rewrite_get_put;
  repeat (specialize_with varT || specialize_with valT);
  autorewrite with rew_set_op_specs in *;
  repeat (intuition (subst *; auto || congruence) || destruct_one_dec_eq).
