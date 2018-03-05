Set Warnings "-notation-overridden".

Require Import Coq.FSets.FMapPositive.

Module Import MP := FMapPositive.
Module M := MP.PositiveMap.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.

Generalizable All Variables.

Section ExprDenote.

Context `{Env}.

Import EqNotations.

Fixpoint termD_work dom (e : Term) : option (∃ cod, objs dom ~> objs cod) :=
  match e with
  | Identity => Some (dom; @id _ (objs dom))
  | Morph a =>
    match arrs a with
    | Some (x; (y; f)) =>
      match Eq_eq_dec x dom with
      | left edom =>
        Some (y; rew [fun x => objs x ~> objs y] edom in f)
      | _ => None
      end
    | _ => None
    end
  | Compose f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition termD dom cod (e : Term) : option (objs dom ~> objs cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | left ecod => Some (rew [fun y => objs dom ~> objs y] ecod in f)
    | right _ => None
    end
  | _ => None
  end.

Lemma termD_Identity {x f} : f = (@id _ (objs x)) ↔ termD x x Identity = Some f.
Proof.
  unfold termD; simpl; split; intros.
    now rewrite Pos_eq_dec_refl, H0.
  rewrite Pos_eq_dec_refl in H0.
  now inversion H0; subst.
Defined.

Lemma termD_Morph {f dom cod f'} :
  arrs f = Some (dom; (cod; f')) ↔ termD dom cod (Morph f) = Some f'.
Proof.
  unfold termD; simpl; split; intros.
    rewrite H0.
    now rewrite !Pos_eq_dec_refl.
  destruct (arrs f) eqn:?; [|discriminate].
  destruct s, s.
  destruct (BinPos.Pos.eq_dec x dom); subst; [|discriminate].
  destruct (BinPos.Pos.eq_dec x0 cod); subst; [|discriminate].
  inversion H0; subst; clear H0.
  reflexivity.
Defined.

Lemma termD_Compose {f g dom mid cod f' g'} :
  termD mid cod f = Some f'
    -> termD dom mid g = Some g'
    -> termD dom cod (Compose f g) = Some (f' ∘ g').
Proof.
  unfold termD; simpl; intros.
  destruct (termD_work mid f) eqn:?; [|discriminate].
  destruct s.
  destruct (BinPos.Pos.eq_dec x cod); [|discriminate].
  subst.
  destruct (termD_work dom g) eqn:?; [|discriminate].
  destruct s.
  destruct (BinPos.Pos.eq_dec x mid); [|discriminate].
  subst.
  simpl_eq.
  rewrite Heqo.
  rewrite !Pos_eq_dec_refl.
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  reflexivity.
Defined.

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => termD x y f ≈ termD x y g
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

End ExprDenote.
