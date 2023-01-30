
(* need to use
coqtop -color no -R /home/jeremy/coq/category-theory Category
Load jed_JD.
coqc -R /home/jeremy/coq/category-theory Category jed_JD.v
*)

Require Import Category.Lib. (* needed for notation *)
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import jed_adjfuns jed_monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* 
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Coercions.
Unset Printing Implicit.
*)

Section CMN. (* category C and monads M and N *)

Context {C : Category}.
Context {M : obj[C] -> obj[C]}.
Context {N : obj[C] -> obj[C]}.
Context {M3 : @Monad3 C M}.
Context {N3 : @Monad3 C N}.

Print Implicit join3.
Print Implicit map3.
Print Implicit ret3.
Print Implicit ext.

(* uses given definition for join of MN, expressed using ext *)
Record JD_P : Type := 
  { prod : ∀ x : obj[C], N (M (N x)) ~{ C }~> M (N x) ;
    P1 : ∀ x y (f : x ~{ C }~> y), 
      prod y ∘ map3 N3 (map3 M3 (map3 N3 f)) ≈ map3 M3 (map3 N3 f) ∘ prod x ;
    P2 : ∀ x, prod x ∘ ret3 N3 ≈ id ;
    P3 : ∀ x, prod x ∘ map3 N3 (ret3 M3 ∘ ret3 N3) ≈ ret3 M3 ;
    P4 : ∀ x, prod x ∘ map3 N3 (ext M3 (prod x)) ≈ ext M3 (prod x) ∘ prod _ }.

Print Implicit JD_P.
Print Implicit P4.
Print Implicit prod.
Print Implicit m_assoc.
Print Implicit m_id_l.
Print Implicit m_id_r.

Check jed_monad.Monad_from_3_obligation_1.
Check jed_monad.Monad_from_3_obligation_2.
Check jed_monad.Monad_from_3_obligation_3.

Check jed_monad.Functor_from_3_obligation_3.

(* P1 to P4 give monad in Kleisli category of M *)
Program Definition JD_P_NK (P : JD_P) : @Monad3 (@Kleisli_from_3 C M M3) N :=
  {| ret3 := fun x : obj[C] => ret3 M3 ∘ @ret3 _ _ N3 x ;
    ext := fun (x y : obj[C]) (f : x ~> M (N y)) => prod P y ∘ map3 N3 f |}.

Next Obligation. proper. pose (map3_respects N3).  rewrite X. reflexivity. Qed.

Next Obligation. rewrite comp_assoc.  rewrite m_id_r.  rewrite <- comp_assoc.
rewrite <- (jed_monad.Monad_from_3_obligation_1 N3).
rewrite comp_assoc.  rewrite P2.  apply id_left. Qed.

Next Obligation. apply P3. Qed.
Next Obligation.  pose (map3_respects N3).  rewrite !ext_o.
rewrite !jed_monad.Functor_from_3_obligation_3.
rewrite !comp_assoc.  rewrite P4.  apply comp_o_r.
rewrite <- !comp_assoc.  apply comp_o_l.  symmetry.  apply P1. Qed.

Print Implicit fmap.
Print Implicit ret3.
Print Implicit compose.
Print Implicit id.
Print Implicit join3.
Print Implicit map3.

End CMN. (* more to be done, but this lets the file compile *)
