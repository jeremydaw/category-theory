
(* need to use
coqtop -color no -R /home/jeremy/coq/category-theory Category
Load rel_monad.
coqc -R /home/jeremy/coq/category-theory Category rel_monad.v
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

Locate "∘". (* this is altered by Category.Theory.Category. *)
Print Monad.
(* Monad: including 2 properties of function, 7 conditions,
  note that the first two of the 5 given say that ret and join
  are natural transformations *)
Print Adjunction.

(* Relative Monads *)
Section RM. (* category C and object maps J and T *)

Context {C : Category}.
Context {J : obj[C] -> obj[C]}.
Context {T : obj[C] -> obj[C]}.

Record Rmonad : Type := Build_Rmonad
  { retr : forall {x : obj[C]}, J x ~{ C }~> T x ;
    extr : forall {x y} (f : J x ~{ C }~> T y), T x ~{ C }~> T y ;
    extr_respects : ∀ x y : obj[C], Proper (equiv ==> equiv) (@extr x y) ;
    rm_id_r : forall x y (f : J x ~{ C }~> T y), extr f ∘ retr ≈ f ;
    rm_id_l : forall x, extr retr ≈ id[T x] ;
    rm_assoc : forall x y z (g : J y ~{ C }~> T z) (f : J x ~{ C }~> T y),
      extr g ∘ extr f ≈ extr (extr g ∘ f) }.

(* simpler not to do this
Context `{@Rmonad}. Check H : Rmonad.
*)

Print Implicit fmap.
Print Implicit retr.
Print Implicit extr.
Print Implicit compose.
Print Implicit id.
(*
Print Implicit join3.
Print Implicit map3.
*)

Print Implicit Functor.
Print Implicit Monad.
Print Implicit fmap.
Print Implicit ext.
Print Monad3.
Print Rmonad.

Print Implicit map3_comp.
Print Implicit map3_id.

Definition mapr (Tr : Rmonad) {x y} (f : J x ~{ C }~> J y) := 
  extr Tr (retr Tr ∘ f).

(* this one is the functor
Definition maprj (J3 : @Monad3 C J) (Tr : Rmonad) {x y} (f : x ~{ C }~> y) := 
  extr Tr (retr Tr ∘ map3 J3 f).
  *)
(*
Definition join3 (H : Monad3) {x} := ext H (@id _ (M x)).
*)

Lemma mapr_respects (Tr : Rmonad) (x y : obj[C]) :
  Proper (equiv ==> equiv) (@mapr Tr x y).
Proof. proper. apply extr_respects. apply comp_o_l. exact X. Qed.

(*
Lemma maprj_respects (J3 : @Monad3 C J) (Tr : Rmonad) (x y : obj[C]) :
  Proper (equiv ==> equiv) (@maprj J3 Tr x y).
Proof. proper. apply extr_respects. apply comp_o_l.
apply map3_respects.  apply X. Qed.
*)

Print Implicit extr.
Print Implicit mapr.
Print Implicit map3.
Print Implicit retr.

(* prove that mapr (map3 .. ) is a functor, 
  for this, map3 J3 must be a functor, don't need J3 is a monad *)
Program Definition Functor_from_RM (J3 : @Monad3 C J) (Tr : Rmonad) : Functor :=
  {| fobj := T ; fmap := fun x y f => mapr Tr (map3 J3 f) |}.
Next Obligation.  proper. apply mapr_respects. apply map3_respects.
  exact X. Qed.
Next Obligation.  unfold mapr. pose extr_respects.
rewrite map3_id.  rewrite id_right. (* fail without using extr_respects *)
apply rm_id_l. Qed.
Next Obligation.  unfold mapr. rewrite rm_assoc.
apply extr_respects.  rewrite !comp_assoc. (* fails w/o ext_respects *)
rewrite rm_id_r. rewrite <- comp_assoc.
apply comp_o_l.  apply map3_comp. Qed.

Print Implicit Functor_from_RM.
Check Functor_from_RM_obligation_1.
Check Functor_from_RM_obligation_2.
Check Functor_from_RM_obligation_3.

Definition mapr3_id := Functor_from_RM_obligation_2.
Definition mapr3_comp := Functor_from_RM_obligation_3.
Check mapr3_id.  Check mapr3_comp.

(* 
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Coercions.
Unset Printing Implicit.
*)

Print Implicit extr_respects.
Print Implicit rm_assoc.

(* don't have these lemmas, types not possible 
Lemma ext_jm (H : Monad3) x y (f : x ~{ C }~> M y) :
  ext H f ≈ join3 H ∘ map3 H f.

Lemma ext_ext (H : Monad3) x y (f : x ~{ C }~> (M y)) :
  ext H (ext H f) ≈ ext H f ∘ join3 H.
*)

Lemma extr_o (Tr : Rmonad) x y z (f : J x ~{ C }~> J y) (g : J y ~{ C }~> T z) :
  extr Tr (g ∘ f) ≈ extr Tr g ∘ mapr Tr f.
Proof. unfold mapr. rewrite rm_assoc.  apply extr_respects.
rewrite comp_assoc.  apply comp_o_r.  symmetry.  apply rm_id_r.  Qed.

(* could do this but just confuses things even more
Section Monad.
Context `{Monad}. Check H : Monad. (* declares C M H *)
*)

End RM.

Print Implicit fobj.
Print Implicit fmap.
Print Implicit retr.
Print Implicit extr.
Print Implicit extr_o.
Print Implicit Monad.
Print Implicit Monad3.
Print Implicit Build_Monad3.
Print Implicit equiv.
Print Implicit join_fmap_join.
Print Implicit compose_respects.
Print Monad.

(* 
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Coercions.
Unset Printing Implicit.
*)
Print Implicit m_id_l.
Print Implicit Functor.
Print Functor.
Print Implicit compose_respects.
Print Category.

(* NB in the following, if we leave the homset as an obligation to be solved,
  see note at proof of Kleisli_from_3 *)
Program Definition Kleisli_from_RM {C J T} (Tr : @Rmonad C J T) : Category := 
  {| obj := @obj C ; hom := fun x y => @hom C (J x) (T y) ;
    homset := fun x y => @homset C (J x) (T y) ;
    id := fun x => retr Tr ;
    compose := fun x y z (g : J y ~{ C }~> T z) (f : J x ~{ C }~> T y) =>
      extr Tr g ∘ f |}.
Next Obligation. proper.  apply compose_respects.
- apply extr_respects. exact X. - exact X0. Qed.
Next Obligation.  rewrite rm_id_l. apply id_left. Qed.
Next Obligation. apply rm_id_r. Qed.
Next Obligation. rewrite comp_assoc.  apply comp_o_r.  apply rm_assoc. Qed.
Next Obligation. rewrite comp_assoc.  apply comp_o_r.
symmetry.  apply rm_assoc. Qed.

Check Kleisli_from_RM_obligation_1.
Check Kleisli_from_RM_obligation_2.
Check Kleisli_from_RM_obligation_3.
Check Kleisli_from_RM_obligation_4.

Check Kleisli_from_RM.
Print Implicit Kleisli_from_RM.

(* functors from and to Kleisli category of relative monad *)
Program Definition extr_functor {C J T} (Tr : @Rmonad C J T) :
  @Functor (Kleisli_from_RM Tr) C  :=
  {| fobj := T ; fmap := fun x y (f : J x ~{ C }~> T y) => extr Tr f |}.
Next Obligation. proper. apply extr_respects. apply X. Qed.
Next Obligation. apply rm_id_l. Qed.
Next Obligation. symmetry. apply rm_assoc. Qed.

Program Definition retr_o_functor {C J T} (J3 : @Monad3 C J)
  (Tr : @Rmonad C J T) : @Functor C (Kleisli_from_RM Tr)  :=
  {| fobj := fun x => x ;
    fmap := fun x y (f : x ~{ C }~> y) => retr Tr ∘ map3 J3 f |}.
Next Obligation. proper. apply comp_o_l. apply map3_respects. exact X. Qed.
Next Obligation.  rewrite map3_id. apply id_right. Qed.
Next Obligation. rewrite map3_comp. rewrite !comp_assoc.
  apply comp_o_r. symmetry. apply rm_id_r. Qed.

Check retr_o_functor.
Check retr_o_functor_obligation_1.
Check retr_o_functor_obligation_2.
Check retr_o_functor_obligation_3.

Print Implicit id.
Print Implicit retr.
Print Implicit obj.
Print Implicit extr.
Print Implicit hom.
Print Implicit homset.
Print Implicit compose.
Print Implicit ext_respects.
Print Implicit Adjunction_IffEq.
Print Adjunction_IffEq.

Definition KRM {C J T} Tr := @Kleisli_from_RM C J T Tr.
(* partial monads *)

Record Pmonad {C J T} (Tr : @Rmonad C J T) : Type := Build_Pmonad
  { retp : forall {x : obj[C]}, x ~{ C }~> T x ;
    extp : forall {x y} (f : x ~{ C }~> T y), J x ~{ C }~> T y ;
    extp_respects : ∀ x y : obj[C], Proper (equiv ==> equiv) (@extp x y) ;
    (* extr Tr (extp f) ∘ retp and extr Tr (extp g) ∘ f
      would be composition in the Kleisli category
      if retp and f were of the right type, note pm_assoc' *)
    pm_id_r : forall x y (f : x ~{ C }~> T y), extr Tr (extp f) ∘ retp ≈ f ;
    pm_id_l : forall x, extp retp ≈ @id (KRM Tr) x ;
    (*
    pm_assoc' : forall x y z (g : y ~{ C }~> T z) (f : x ~{ C }~> T y),
      @compose (KRM Tr) _ _ _ (extp g) (extp f) ≈ extp (extr Tr (extp g) ∘ f) ;
      *)
    pm_assoc : forall x y z (g : y ~{ C }~> T z) (f : x ~{ C }~> T y),
      extr Tr (extp g) ∘ extp f ≈ extp (extr Tr (extp g) ∘ f) }.

(*
TO CONTINUE FROM HERE
(* adjoint functors to and from Kleisli category of monad *)
Program Definition k_adj {C M} (H : @Monad3 C M) :
  @Adjunction_IffEq (Kleisli_from_3 H) C (ret_o_functor H) (ext_functor H) := 
  {| unit' := fun x => ret3 H ;
    counit' := fun y => @id C (M y) |}.
Next Obligation. rewrite !comp_assoc.
rewrite !m_id_r. rewrite id_left.
split ; symmetry. Qed.

Check k_adj.  Check k_adj_obligation_1.

(* functor to/from Kleisli cat of adjunction, see Barr & Wells 
Toposes, Triples and Theories ch 3, s2.3 
"In fact, [the Kleisli category] is initial and [The Eilenberg-Moore category]
is ﬁnal among all ways of factoring [a monad] as an adjoint pair." *)

Program Definition AIE_to_rel_fun {C D F U} 
  (H : @Adjunction_IffEq C D F U) :
  @Functor (Kleisli_from_3 (AIE_to_Monad3 H)) C :=
  {| fobj := fobj[F] ;
    fmap := fun x z (g : x ~{ D }~> U (F z)) => counit' H _ ∘ fmap[F] g |}.
Next Obligation. proper. rewrite X. reflexivity. Qed.
Next Obligation. apply iffeq. rewrite fmap_id. apply id_left. Qed.
Next Obligation. apply iffeq. rewrite fmap_comp. rewrite <- comp_assoc.
  apply comp_o_l. apply iffeq. reflexivity. Qed.

Lemma AIE_rf_comp_F {C D F U} (H : @Adjunction_IffEq C D F U) :
  Compose (AIE_to_rel_fun H)  
  (ret_o_functor (AIE_to_Monad3 H)) ≈ F.
Proof. simpl.  exists (fun x => (@iso_id _ (F x))). simpl.
intros. apply iffeq.  rewrite id_left.  rewrite id_right.
apply (@naturality _ _ _ _ (iff_unit H)). Qed.

Lemma AIE_rf_comp_U {C D F U} (H : @Adjunction_IffEq C D F U) :
  Compose U (AIE_to_rel_fun H) ≈ 
    (ext_functor (AIE_to_Monad3 H)).
Proof. simpl.  exists (fun x => (@iso_id _ (U (F x)))). simpl.
intros.  rewrite id_left.  rewrite id_right. reflexivity. Qed.

Print Implicit naturality.
Print Implicit Kleisli_from_3.
Print Implicit ret_o_functor.
Print Implicit counit'.
Print Implicit iffeq.
Print Implicit fobj.
Print Implicit iso_id.
Print Functor.
Print Implicit Functor.
Print Adjunction_IffEq.
Print Implicit Kleisli_from_3.  
Print Implicit AIE_to_Monad3.  

(* compound monad, monad in Kleisli category of another monad *)
(* this is the basis of the prod construction of Jones & Duponcheel *)

Program Definition JD_Pext {C M} (H : @Monad3 C M) {N} 
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

Check JD_Pext.

Print Implicit ext_respects.
Print Implicit Kleisli_from_3.
Print Implicit Monad3.
Print Implicit ret3.
Print Implicit m_assoc.
Print Implicit k_adj.
Print Implicit Adjunction_IffEq_comp.
Print Monad3.
Print Implicit AIE_to_Monad3.
Check AIE_to_Monad3.

(* we can prove JD_Pext using Adjunction_IffEq_comp, as
  both monads give rise to adjunctions (using Kleisli categories),
  compose these adjunctions, get compound monad from that,
  however this obscures us seeing the construction *)
Lemma JD_Pext_adj {C M} (H : @Monad3 C M) {N} 
  (J : @Monad3 (@Kleisli_from_3 C M H) N) : @Monad3 C (Basics.compose M N).
Proof.  pose (Adjunction_IffEq_comp (k_adj J) (k_adj H)).
exact (AIE_to_Monad3 a). Defined.
Check JD_Pext_adj.

(* this shows the type of ext, not how it is defined *)
Check (fun H J => ext (JD_Pext_adj H J)). 
Check (fun H J => ext (JD_Pext H J)). 

(* try to look at ext construction used in JD_Pext
Lemma lx {C M} (H : @Monad3 C M) {N}
  (J : @Monad3 (@Kleisli_from_3 C M H) N) : False.
Proof. pose (fun x y => @ext C _ (JD_Pext_adj H J) x y). simpl.
*)

(* 
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Coercions.
Unset Printing Implicit.
*)
*)
