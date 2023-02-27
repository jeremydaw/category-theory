
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
Set Printing Notations.
Unset Printing Coercions.
Unset Printing Implicit.
Unset Printing Notations.
*)

Section CMN. (* category C and monads M and N *)

Context {C : Category}.
Context {M : obj[C] -> obj[C]}.
Context {N : obj[C] -> obj[C]}.
Context (M3 : @Monad3 C M).
Context (N3 : @Monad3 C N).

Print Implicit join3.
Print Implicit map3.
Print Implicit ret3.
Print Implicit ext.

(* this is the prod construction conditions of Jones & Duponcheel,
  expressed using their definitions of unitMN and mapMN and joinMN ;
  for joinMN we write it using ext *)

Definition retc x := @ret3 C M M3 _ ∘ @ret3 C N N3 x.
Definition mapc {x y} f := map3 M3 (@map3 C N N3 x y f).

Record JD_P : Type := 
  { prod : ∀ x : obj[C], N (M (N x)) ~{ C }~> M (N x) ;
    P1 : ∀ x y (f : x ~{ C }~> y), 
      prod y ∘ map3 N3 (mapc f) ≈ mapc f ∘ prod x ;
    P2 : ∀ x, prod x ∘ ret3 N3 ≈ id ;
    P3 : ∀ x, prod x ∘ map3 N3 (retc x) ≈ ret3 M3 ;
    P4 : ∀ x, prod x ∘ map3 N3 (ext M3 (prod x)) ≈ ext M3 (prod x) ∘ prod _ }.

Definition join_P (P : JD_P) x := ext M3 (prod P x).
Definition pext_P (P : JD_P) {x y} (f : x ~> M (N y)) := prod P y ∘ map3 N3 f.

Lemma pext_P_respects (P : JD_P) (x y : obj[C]) :
  Proper (equiv ==> equiv) (@pext_P P x y).
Proof. proper. unfold pext_P.  apply comp_o_l.
apply map3_respects. apply X. Qed.

Print Implicit JD_P.
Print Implicit P4.
Print Implicit prod.
Print Implicit m_assoc.
Print Implicit m_id_l.
Print Implicit m_id_r.

Record JD_Pext : Type := 
  { pext : ∀ {x y : obj[C]} (f : x ~{ C }~> M (N y)), N x ~{ C }~> M (N y) ;
    pext_respects : ∀ x y : obj[C], Proper (equiv ==> equiv) (@pext x y) ;
    pext_o : ∀ x y z (f : x ~{ C }~> y) (g : y ~> M (N z)), 
      pext (g ∘ f) ≈ pext g ∘ map3 N3 f ;
    Pext1 : ∀ x y (f : x ~{ C }~> y), pext (mapc f) ≈ mapc f ∘ pext id ;
    Pext2 : ∀ x y (f : x ~{ C }~> M (N y)), pext f ∘ ret3 N3 ≈ f ;
    Pext3 : ∀ x, pext (retc x) ≈ ret3 M3 ;
    Pext4 : ∀ x y f, pext (ext M3 (@pext x y f)) ≈ ext M3 (pext f) ∘ pext id }.

Program Definition JD_P_Pext (P : JD_P) : JD_Pext :=
  {| pext := fun x y f => prod P y ∘ map3 N3 f |}.
Next Obligation. proper. unfold pext_P.  apply comp_o_l.
apply map3_respects. apply X. Qed.
Next Obligation. rewrite map3_comp. apply comp_assoc. Qed.
Next Obligation. rewrite map3_id, id_right. apply P1. Qed.
Next Obligation. rewrite <- comp_assoc. unfold map3.
rewrite m_id_r. rewrite comp_assoc. rewrite P2. apply id_left. Qed.
Next Obligation. apply P3. Qed.
Next Obligation. pose (map3_respects N3). rewrite ext_o.
rewrite map3_comp. rewrite comp_assoc. rewrite P4.
rewrite map3_id, id_right. rewrite <- !comp_assoc.
apply comp_o_l. apply P1. Qed.

Check jed_monad.Monad_from_3_obligation_1.
Check jed_monad.Monad_from_3_obligation_2.
Check jed_monad.Monad_from_3_obligation_3.

Check jed_monad.Functor_from_3_obligation_3.
Check JD_P_Pext_obligation_6.

(* P1 to P4 give monad in Kleisli category of M *)
Program Definition JD_P_NK (P : JD_P) : @Monad3 (@Kleisli_from_3 C M M3) N :=
  {| ret3 := fun x : obj[C] => ret3 M3 ∘ @ret3 _ _ N3 x ;
    ext := fun (x y : obj[C]) (f : x ~> M (N y)) => pext_P P f |}.
Next Obligation. proper. apply pext_P_respects.  rewrite X. reflexivity. Qed.
Next Obligation. rewrite comp_assoc.  rewrite m_id_r.
unfold pext_P. rewrite <- comp_assoc.
rewrite <- (jed_monad.Monad_from_3_obligation_1 N3).
rewrite comp_assoc.  rewrite P2.  apply id_left. Qed.
Next Obligation. apply P3. Qed.
Next Obligation.  pose (map3_respects N3).  unfold pext_P. rewrite !ext_o.
rewrite !map3_comp.  rewrite !comp_assoc.  rewrite P4.  apply comp_o_r.
rewrite <- !comp_assoc.  apply comp_o_l.  symmetry.  apply P1. Qed.

Check JD_P_NK_obligation_1.
Check JD_P_NK_obligation_2.
Check JD_P_NK_obligation_3.
Check JD_P_NK_obligation_4.

Program Definition JD_Pext_NK (P : JD_Pext) :
  @Monad3 (@Kleisli_from_3 C M M3) N := {| ret3 := retc ;
    ext := fun (x y : obj[C]) (f : x ~> M (N y)) => pext P f |}.
Next Obligation. apply pext_respects. Qed.
Next Obligation. unfold retc. rewrite comp_assoc, m_id_r. apply Pext2. Qed.
Next Obligation. apply Pext3. Qed.
Next Obligation. rewrite pext_o. rewrite Pext4.
rewrite <- comp_assoc. rewrite <- pext_o. 
pose pext_respects.  rewrite id_left. reflexivity. Qed.

Check JD_Pext_NK_obligation_1.
Check JD_Pext_NK_obligation_2.
Check JD_Pext_NK_obligation_3.
Check JD_Pext_NK_obligation_4.

Print Implicit fmap.
Print Implicit ret3.
Print Implicit compose.
Print Implicit id.
Print Implicit join3.
Print Implicit map3.

End CMN. (* more to be done, but this lets the file compile *)

(* compound monad, monad in Kleisli category of another monad *)
(* this is the basis of the prod construction of Jones & Duponcheel *)

Program Definition MinK_comp {C M} (H : @Monad3 C M) {N} 
  (J : @Monad3 (@Kleisli_from_3 C M H) N) : @Monad3 C (Basics.compose M N) :=
  {| ret3 := @ret3 _ _ J ; ext := fun x y f => ext H (ext J f) |}.

Next Obligation.  proper. apply ext_respects.
apply (ext_respects J). apply X. Qed.

Next Obligation.  (* rewrite (m_id_r J). or rewrite m_id_r. fail here *)
exact (m_id_r J _ _ f). Qed.

Next Obligation. pose (ext_respects H). (* needed, including the H *)
rewrite m_id_l. apply m_id_l. Qed.

Next Obligation. rewrite m_assoc. apply ext_respects.
(* apply setoid_trans. fails, why?? and rewrite (m_assoc J). fails *)
apply (m_assoc J _ _ _ g f). Qed.

Check MinK_comp.

Print Implicit join3.

(* when we have a compound monad defined in this way, it satisfies J(1) *)
Lemma MinK_J1 {C M} (H : @Monad3 C M) {N} 
  (J : @Monad3 (@Kleisli_from_3 C M H) N) x : 
  ext H (join3 (MinK_comp H J)) ≈ @join3 _ _ (MinK_comp H J) x ∘ join3 H.
Proof. simpl. apply ext_ext. Qed.

(* monad in Kleisli category of another monad, implies Pext rules *)
(* or does it?? maybe it requires the J1 condition
Program Definition MinK_Pext {C M} (M3 : @Monad3 C M) {N} (N3 : @Monad3 C N)
  (J : @Monad3 (@Kleisli_from_3 C M M3) N) : JD_Pext M3 N3 :=
  {| pext := fun x y (f : x ~> M (N y)) => ext J f |}.
Next Obligation.  proper.  apply (ext_respects J). apply X. Qed.
Next Obligation.  rewrite !m_id_r. what to do now

Program Definition MinK_P {C M} (M3 : @Monad3 C M) {N} (N3 : @Monad3 C N)
  (J : @Monad3 (@Kleisli_from_3 C M M3) N) : JD_P M3 N3 :=
  {| prod := fun x => ext J (@id C (M (N x))) |}.
*)

Print Implicit ext_respects.
Print Implicit Kleisli_from_3.
Print Implicit Monad3.
Print Implicit m_assoc.
Print Implicit k_adj.
Print Implicit Adjunction_IffEq_comp.
Print Monad3.
Print Implicit AIE_to_Monad3.
Check AIE_to_Monad3.

(* we can prove MinK_comp using Adjunction_IffEq_comp, as
  both monads give rise to adjunctions (using Kleisli categories),
  compose these adjunctions, get compound monad from that,
  however this obscures us seeing the construction *)
Lemma MinK_comp_adj {C M} (H : @Monad3 C M) {N} 
  (J : @Monad3 (@Kleisli_from_3 C M H) N) : @Monad3 C (Basics.compose M N).
Proof.  pose (Adjunction_IffEq_comp (k_adj J) (k_adj H)).
exact (AIE_to_Monad3 a). Defined.
Check MinK_comp_adj.

(* this shows the type of ext, not how it is defined *)
Check (fun H J => ext (MinK_comp_adj H J)). 
Check (fun H J => ext (MinK_comp H J)). 

