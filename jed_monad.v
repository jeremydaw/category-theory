
(* need to use
coqtop -color no -R /home/jeremy/coq/category-theory Category
Load jed_monad.
coqc -R /home/jeremy/coq/category-theory Category jed_monad.v
*)

Require Import Category.Lib. (* needed for notation *)
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import JED.

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

Section CMo. (* category C and object map M *)

Context {C : Category}.
Context {M : obj[C] -> obj[C]}.

Record Monad3 : Type := Build_Monad3
  { ret3 : forall {x : obj[C]}, x ~{ C }~> M x ;
    ext : forall {x y} (f : x ~{ C }~> M y), M x ~{ C }~> M y ;
    ext_respects : ∀ x y : obj[C], Proper (equiv ==> equiv) (@ext x y) ;
    m_id_r : forall x y (f : x ~{ C }~> M y), ext f ∘ ret3 ≈ f ;
    m_id_l : forall x, ext ret3 ≈ id[M x] ;
    m_assoc : forall x y z (g : y ~{ C }~> M z) (f : x ~{ C }~> M y),
      ext g ∘ ext f ≈ ext (ext g ∘ f) }.

(* simpler not to do this
Context `{@Monad3}. Check H : Monad3.
*)

Print Implicit fmap.
Print Implicit ret3.
Print Implicit compose.
Print Implicit id.
(*
Print Implicit join3.
Print Implicit map3.
*)

Check join. 
Check morphism join. 
Check morphism. 
Check proper_morphism. 

Print Implicit Functor.
Print Implicit Monad.
Print Implicit fmap.
Print Implicit ext.
Print Monad3.

Definition map3 (H : Monad3) {x y} (f : x ~{ C }~> y) := ext H (ret3 H ∘ f).
Definition join3 (H : Monad3) {x} := ext H (@id _ (M x)).

Print Implicit join3.
Print Implicit map3.
Print Implicit ret3.

(* prove that map3 is a functor *)
Program Definition Functor_from_3 {H : Monad3} : Functor :=
  {| fobj := M ; fmap := @map3 H |}.
Next Obligation.  proper. unfold map3. apply ext_respects.
rewrite X. (* setoid rewrite fail without using ext_respects. *)
reflexivity. Qed.
Next Obligation.  unfold map3.  pose ext_respects.
rewrite id_right. (* fails without using ext_respects *)
apply m_id_l. Qed.
Next Obligation.  unfold map3. rewrite m_assoc.
apply ext_respects.  rewrite !comp_assoc. (* fails w/o ext_respects *)
rewrite m_id_r. reflexivity. Qed.

Print Implicit Functor_from_3.
Check Functor_from_3_obligation_1.
Check Functor_from_3_obligation_2.
Check Functor_from_3_obligation_3.

(* 
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Coercions.
Unset Printing Implicit.
*)

Print Implicit ext_respects.

(* note that as this corresponds to how we define ext in Monad_to_3 below,
  the two transformations are mutually inverse *)
Lemma ext_jm (H : Monad3) x y (f : x ~{ C }~> M y) :
  ext H f ≈ join3 H ∘ map3 H f.
Proof. unfold join3. unfold map3. pose ext_respects.
rewrite !m_assoc, comp_assoc, m_id_r, id_left. reflexivity. Qed.

Lemma ext_ext (H : Monad3) x y (f : x ~{ C }~> (M y)) :
  ext H (ext H f) ≈ ext H f ∘ join3 H.
Proof. unfold join3. pose ext_respects.
rewrite !m_assoc. rewrite id_right. reflexivity. Qed.

Program Definition Monad_from_3 (H : Monad3) : @Monad C (@Functor_from_3 H) := 
  {| ret := @ret3 H ; join := @join3 H |}.
Next Obligation. unfold map3. rewrite m_id_r. reflexivity. Qed.
Next Obligation. rewrite <- ext_jm. unfold join3. apply ext_ext. Qed.
Next Obligation.  rewrite <- ext_jm. apply m_id_l.  Qed.
Next Obligation. unfold join3. apply m_id_r. Qed.
Next Obligation. rewrite <- ext_jm. unfold map3. apply ext_ext. Qed.

Print Implicit Monad_from_3.
Check Monad_from_3_obligation_1.
Check Monad_from_3_obligation_2.

End CMo.

Check Monad_from_3_obligation_3.
Check Monad_from_3_obligation_4.
Check Monad_from_3_obligation_5.

Lemma comp_o_r : ∀ C (y z : obj[C]) (f g : y ~{ C }~> z), f ≈ g → 
  ∀ x (h : x ~{ C }~> y), f ∘ h ≈ g ∘ h.
Proof. intros. apply compose_respects. apply X. apply setoid_refl. Qed.

Lemma comp_o_l : ∀ C (y z : obj[C]) (f g : y ~{ C }~> z), f ≈ g → 
  ∀ x (h : z ~{ C }~> x), h ∘ f ≈ h ∘ g.
Proof. intros. apply compose_respects. apply setoid_refl. apply X. Qed.

Print Implicit comp_o_l.  Print Implicit comp_o_r.

(* could do this but just confuses things even more
Section Monad.
Context `{Monad}. Check H : Monad. (* declares C M H *)
*)

Print Implicit fobj.
Print Implicit fmap.
Print Implicit ret.
Print Implicit join.
Print Implicit Monad.
Print Implicit Monad3.
Print Implicit Build_Monad3.
Print Implicit equiv.
Print Implicit join_fmap_join.
Print Implicit compose_respects.
Print Monad.

(* here are two ways of setting up the same proof *)
Lemma Monad_to_3 C M (H : @Monad C M) : @Monad3 C (@fobj _ _ M).
Proof. apply (Build_Monad3 (fun x => ret)
  (fun x y (f : x ~{ C }~> M y) => join ∘ fmap[M] f)) ; intros.
- proper. rewrite X. reflexivity. 
-  rewrite <- comp_assoc, <- fmap_ret.
rewrite comp_assoc, join_ret. apply id_left. 
- apply join_fmap_ret. 
-  rewrite !fmap_comp.
rewrite !comp_assoc.  rewrite join_fmap_join.
apply comp_o_r.  rewrite <- !comp_assoc.
rewrite join_fmap_fmap.  reflexivity. Qed.

Program Definition Monad3_from_Monad C M (H : @Monad C M) : @Monad3 C fobj := 
  {| ret3 := fun x => ret ;
    ext := fun x y (f : x ~{ C }~> M y) => join ∘ fmap[M] f |}.
Next Obligation. proper. rewrite X. reflexivity. Qed.
Next Obligation.  rewrite <- comp_assoc, <- fmap_ret.
rewrite comp_assoc, join_ret. apply id_left. Qed.
Next Obligation. apply join_fmap_ret. Qed.
Next Obligation.  rewrite !fmap_comp.
rewrite !comp_assoc.  rewrite join_fmap_join.
apply comp_o_r.  rewrite <- !comp_assoc.
rewrite join_fmap_fmap.  reflexivity. Qed.

Check Monad3_from_Monad_obligation_1.
Check Monad3_from_Monad_obligation_2.
Check Monad3_from_Monad_obligation_3.
Check Monad3_from_Monad_obligation_4.

Check Monad_to_3.
Check Monad3_from_Monad.

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
  it gives the goal Setoid ..., which can be solved either by proper.
  or by exact (@homset C X (M Y)). but in either case we subsequently
  get the problem that it can't unify (@homset C x (M z)) with
  (Kleisli_from_3_obligation_1 C M H x z) *)
Program Definition Kleisli_from_3 {C M} (H : @Monad3 C M) : Category := 
  {| obj := @obj C ; hom := fun x y => @hom C x (M y) ;
    homset := fun x y => @homset C x (M y) ;
    id := fun x => ret3 H ;
    compose := fun x y z (g : y ~{ C }~> M z) (f : x ~{ C }~> M y) =>
      ext H g ∘ f |}.
Next Obligation. proper.  apply compose_respects.
apply ext_respects. exact X. exact X0. Qed.
Next Obligation.  rewrite m_id_l. apply id_left. Qed.
Next Obligation. apply m_id_r. Qed.
Next Obligation. rewrite comp_assoc.  apply comp_o_r.  apply m_assoc. Qed.
Next Obligation. apply setoid_sym.  apply Kleisli_from_3_obligation_4. Qed.

Check Kleisli_from_3_obligation_1.
Check Kleisli_from_3_obligation_2.
Check Kleisli_from_3_obligation_3.
Check Kleisli_from_3_obligation_4.

Check Kleisli_from_3.
Print Implicit Kleisli_from_3.

(* functors from and to Kleisli category of monad *)
Program Definition ext_functor {C M} (H : @Monad3 C M) :
  @Functor (Kleisli_from_3 H) C  :=
  {| fobj := M ; fmap := fun x y (f : x ~{ C }~> M y) => ext H f |}.
Next Obligation. proper. apply ext_respects. apply X. Qed.
Next Obligation. apply m_id_l. Qed.
Next Obligation. apply setoid_sym. apply m_assoc. Qed.

Program Definition ret_o_functor {C M} (H : @Monad3 C M) :
  @Functor C (Kleisli_from_3 H)  :=
  {| fobj := fun x => x ; fmap := fun x y (f : x ~{ C }~> y) => ret3 H ∘ f |}.
Next Obligation. rewrite !comp_assoc.
  apply comp_o_r. symmetry. apply m_id_r. Qed.

Check ret_o_functor.
Check ret_o_functor_obligation_1.
Check ret_o_functor_obligation_2.
Check ret_o_functor_obligation_3.

Print Implicit id.
Print Implicit ret3.
Print Implicit obj.
Print Implicit ext.
Print Implicit hom.
Print Implicit homset.
Print Implicit uhom.
Print Implicit ext_respects.
Print Implicit Adjunction_IffEq.
Print Adjunction_IffEq.

(* adjoint functors to and from Kleisli category of monad *)
Program Definition k_adj {C M} (H : @Monad3 C M) :
  @Adjunction_IffEq (Kleisli_from_3 H) C (ret_o_functor H) (ext_functor H) := 
  {| unit' := fun x => ret3 H ;
    counit' := fun y => @id C (M y) |}.
Next Obligation. rewrite !comp_assoc.
rewrite !m_id_r. rewrite id_left.
split ; apply setoid_sym. Qed.

Check k_adj.  Check k_adj_obligation_1.

(*
(* 
Program Definition k_adj {C M} (H : @Monad3 C M) :
  Adjunction_IffEq (ext_functor H) (ret_o_functor H) :=
  {| unit' := fun x => ret3 H ; counit' := fun y => id[M y] |}.
Next Obligation. rewrite !comp_assoc.
*)


(* which of these is right ? *)
Lemma k_adj {C M} (H : @Monad3 C M) :
  @Adjunction_IffEq (Kleisli_from_3' H) C (ret_o_functor H) (ext_functor H). 
Proof.

eapply Build_Adjunction_IffEq.
intros.  simpl.

split ; intro.

(* wrong 
Lemma k_adj {C M} (H : @Monad3 C M) :
  Adjunction_IffEq (ext_functor H) (ret_o_functor H).
eapply Build_Adjunction_IffEq.
intros. split ; intro.
pose compose_respects.
pose ext_respects.
rewrite <- X.
*)
*)

