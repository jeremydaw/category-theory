Set Warnings "-notation-overridden".

Require Export Solver.Sound.
Require Import Solver.Partial.

Module Import MP := FMapPositive.
Module M := MP.PositiveMap.

Generalizable All Variables.

Section Logic.

Context `{Env}.

Remove Hints Coq.Coq : typeclass_instances.

Open Scope partial_scope.

Program Fixpoint expr_forward (t : Expr arr_idx) (hyp : Expr arr_idx)
        (cont : [exprD t (* (subst_all_expr t defs') *)]) :
  [exprD hyp -> exprD t] :=
  match hyp with
  | Top           => Reduce cont
  | Bottom        => Yes
  | Equiv x y f g => Reduce cont (* jww (2017-08-02): TODO *)
  | And p q       => Reduce cont (* jww (2017-08-02): TODO *)
  | Or p q        => if expr_forward t p cont
                     then Reduce (expr_forward t q cont)
                     else No
  | Impl _ _      => Reduce cont
  end.
Next Obligation. contradiction. Defined.
Next Obligation. intuition. Defined.

Program Fixpoint expr_backward (t : Expr arr_idx) {measure (expr_size t)} :
  [exprD t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Equiv x y f g => _
  | And p q       =>
    match expr_backward p with
    | Proved _ _  => Reduce (expr_backward q)
    | Uncertain _ => No
    end
  | Or p q        =>
    match expr_backward p with
    | Proved _ _  => Yes
    | Uncertain _ => Reduce (expr_backward q)
    end
  | Impl p q      =>
    expr_forward q p (expr_backward q (* (subst_all_expr q defs') *))
  end.
Next Obligation.
  destruct (termD x y f) eqn:?; [|apply Uncertain].
  destruct (termD x y g) eqn:?; [|apply Uncertain].
  destruct (list_beq Eq_eqb (arrows f) (arrows g)) eqn:?; [|apply Uncertain].
  apply Proved.
  eapply arrows_decide; eauto.
Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. omega. Defined.

Definition expr_tauto : forall t, [exprD t].
Proof.
  intros; refine (Reduce (expr_backward t)); auto.
Defined.

Lemma expr_sound t :
  (if expr_tauto t then True else False) -> exprD t.
Proof.
  unfold expr_tauto; destruct t, (expr_backward _); tauto.
Qed.

End Logic.
