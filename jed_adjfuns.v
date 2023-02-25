
(*
coqc -R /home/jeremy/coq/category-theory Category jed_adjfuns.v
coqtop -color no -R /home/jeremy/coq/category-theory Category 
Load jed_adjfuns.
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets. (* required for morphism below *)
Require Import Coq.Classes.CMorphisms.
(* this line introduces a bizarre error
Require Import Category.Lib.Setoid. (* required for equiv *)
*)

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(*
Check allT : forall A : Type, (A -> Prop) -> Prop.
Definition allT (A : Type) (P : A -> Type) := forall x : A, P x.
Definition all2T (A B : Type) (P : A -> B -> Type) := forall x y, P x y.
Definition all2 (A B : Type) (P : A -> B -> Prop) := forall x y, P x y.

Lemma allT_prod_sep A B P : allT (A * B) P -> all2T A B (prod_uncurry P).
Proof. intros ap x y. exact (ap (x, y)). Qed.

Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.

Axiom ax_prop_ext : ClassicalFacts.prop_extensionality.
Lemma punc_fun A B C P : @prod_uncurry A B C P = (fun x y => P (x, y)).
Proof. apply functional_extensionality. intro.
apply functional_extensionality. intro. reflexivity. Qed.
*)

(* [require], when called on a hypothesis [H : P -> Q],
   asserts that P actually holds,
   and thus that H's type can be replaced with Q *)
Ltac require H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    let y := x in
    assert H1 as x; [| specialize (H x); clear y]
  end.

(*
*)
Section CDFU.

Context {C : Category}.
Context {D : Category}.
Context (F : D ⟶ C).
Context (U : C ⟶ D).

(* adjunction definitions already done, see Adjunction/Hom.v *)
Print Category.Adjunction.Hom.Build_Adjunction_Hom.
Print Category.Adjunction.Natural.Transformation.Build_Adjunction_Transform.
Print Category.Theory.Adjunction.Build_Adjunction.
(*
Notation "F ∹ G" := (Adjunction_Transform F G) : adjunction_type_scope
Notation "F ⊣ G" := (Adjunction F G) : category_scope
*)

Check Category.Adjunction.Hom.Adjunction_Hom_to_Transform.
Check Category.Adjunction.Hom.Adjunction_Transform_to_Hom.
Check Category.Adjunction.Hom.Adjunction_Hom_to_Universal.
Check Category.Adjunction.Hom.Adjunction_Universal_to_Hom.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Check Adjunction_from_Transform.  Check Adjunction_to_Transform.

Class Adjunction_OW := {
  unitOW : Id[D] ⟹ U ◯ F ;
  (* there exists an adjoint function, from adj of Adjunction *)
  adjr : forall {x y} (g : x ~{ D }~> U y), F x ~{ C }~> y ;
  (* the adjoint arrow is the unique one which makes the diagram commute *)
  adjruc : forall {x y} (f : F x ~{ C }~> y) (g : x ~{ D }~> U y),
    iffT (fmap[U] f ∘ unitOW x ≈ g) (adjr g ≈ f) }.

Lemma AOW_adjr_unit_id (H : Adjunction_OW) d : adjr (unitOW d) ≈ id.
Proof. apply adjruc. rewrite fmap_id. apply id_left. Qed.

Definition AOW_counit (H : Adjunction_OW) c := @adjr H _ c id.

Lemma AOW_fmap_counit_unit (H : Adjunction_OW) c :
  fmap[U] (AOW_counit H c) ∘ transform unitOW _ ≈ @id D (fobj[U] c).
Proof. apply adjruc. reflexivity. Qed.

Lemma AOW_adjr_unit (H : Adjunction_OW) d :
  adjr (transform unitOW _) ≈ @id C (fobj[F] d).
Proof. apply adjruc. rewrite fmap_id. apply id_left. Qed.

Lemma AOW_adjr_eq (H : Adjunction_OW) d c (g : d ~> fobj[U] c) :
  adjr g ≈ AOW_counit H _ ∘ fmap[F] g.
Proof. apply adjruc. rewrite fmap_comp, <- comp_assoc.
rewrite (naturality unitOW _ _ g). rewrite comp_assoc.
rewrite AOW_fmap_counit_unit. apply id_left. Qed.

Lemma AOW_counit_nt (H : Adjunction_OW) c c' f :
  AOW_counit H c' ∘ fmap[F] (fmap[U] f) ≈ f ∘ AOW_counit H c.
Proof. rewrite <- AOW_adjr_eq.
apply adjruc. rewrite fmap_comp, <- comp_assoc.
rewrite AOW_fmap_counit_unit. apply id_right. Qed.

Print Implicit adjr.

Class Adjunction_IffEq := {
  unit' : forall {x : obj[D]}, x ~{ D }~> U (F x) ;
  counit' : forall {y : obj[C]}, F (U y) ~{ C }~> y ;
  iffeq : forall {x y} (f : F x ~{ C }~> y) (g : x ~{ D }~> U y),
    iffT (fmap[U] f ∘ unit' ≈ g) (counit' ∘ fmap[F] g ≈ f) }.

Lemma AIE_fmap_counit_unit (H : Adjunction_IffEq) c :
  fmap[U] counit' ∘ unit' ≈ @id D (fobj[U] c).
Proof. rewrite iffeq, fmap_id. apply id_right. Qed.

Lemma AIE_counit_fmap_unit (H : Adjunction_IffEq) d :
  counit' ∘ fmap[F] unit' ≈ @id C (fobj[F] d).
Proof. rewrite <- iffeq, fmap_id. apply id_left. Qed.

Lemma AIE_counit_nt (H : Adjunction_IffEq) c c' f :
  @counit' H c' ∘ fmap[F] (fmap[U] f) ≈ f ∘ @counit' H c.
Proof. rewrite <- iffeq, fmap_comp, <- comp_assoc.
rewrite AIE_fmap_counit_unit. apply id_right.  Qed.

Lemma AIE_unit_nt (H : Adjunction_IffEq) d d' g :
  fmap[U] (fmap[F] g) ∘ @unit' H d ≈ @unit' H d' ∘ g.
Proof. rewrite iffeq, fmap_comp, comp_assoc.
rewrite AIE_counit_fmap_unit. apply id_left.  Qed.

Program Definition iff_unit (H : Adjunction_IffEq) : Id ⟹ U ◯ F :=
  {| transform := @unit' H |}.
Next Obligation.  apply (@AIE_unit_nt H). Qed.
Next Obligation.  symmetry. apply (@AIE_unit_nt H). Qed.

Program Definition iff_counit (H : Adjunction_IffEq) : F ◯ U ⟹  Id := 
  {| transform := @counit' H |}.
Next Obligation.  symmetry.  apply (@AIE_counit_nt H). Qed.
Next Obligation.  apply (@AIE_counit_nt H). Qed.

Check iff_unit_obligation_1.
Print Implicit iff_counit.
Print Implicit Adjunction_OW.
Print Implicit Adjunction_Transform.
Print Implicit naturality_sym.

Check @Category.Theory.Isomorphism.Build_Isomorphism.
Check @Category.Theory.Natural.Transformation.Build_Transform.
Check @Category.Theory.Natural.Transformation.transform.
Check Category.Theory.Isomorphism.Isomorphism.
Check @Category.Theory.Isomorphism.to.

Program Definition Adjunction_IffEq_to_Hom
  (H : Adjunction_IffEq) : Adjunction_Hom F U := {|
  hom_adj :=
    {| to := {| transform := fun _ =>
        {| morphism := fun f => fmap[U] f ∘ @unit' H _ |} |} ;
     from := {| transform := fun _ =>
        {| morphism := fun f => @counit' H _ ∘ fmap[F] f |} |} |} |}.
Next Obligation.  proper. rewrite X. reflexivity. Qed.
Next Obligation.  rewrite !fmap_comp.  rewrite !comp_assoc_sym.
rewrite AIE_unit_nt.  reflexivity. Qed.
Next Obligation.  rewrite !fmap_comp.  rewrite !comp_assoc_sym.
rewrite AIE_unit_nt.  reflexivity. Qed.
Next Obligation.  proper. rewrite X. reflexivity. Qed.
Next Obligation.  rewrite !fmap_comp.  rewrite !comp_assoc.
rewrite AIE_counit_nt.  reflexivity. Qed.
Next Obligation.  rewrite !fmap_comp.  rewrite !comp_assoc.
rewrite AIE_counit_nt.  reflexivity. Qed.
Next Obligation.  rewrite fmap_id, id_left, id_right.
rewrite iffeq. reflexivity. Qed.
Next Obligation.  rewrite fmap_id, id_left, id_right.
rewrite <- iffeq. reflexivity. Qed.

(* Lemma or Program Definition - seems to make no difference *)
Lemma Adjunction_IffEq_to_OW (H : Adjunction_IffEq) : Adjunction_OW.
Proof.  exact (Build_Adjunction_OW (@iff_unit H) _ (@iffeq H)). Qed.

Lemma Adjunction_IffEq_to_Transform (H : Adjunction_IffEq) : F ∹ U.
Proof. pose (@iffeq H).
apply (Build_Adjunction_Transform (iff_unit H) (iff_counit H)) ;
  intro ; apply i.
(* problem?, that iff_unit is nt, unit' is function, but there is a coercion *)
- rewrite fmap_id, id_left.  reflexivity.
- rewrite fmap_id, id_right.  reflexivity.  Qed.

Print Build_Isomorphism.

Program Definition iff_adj (H : Adjunction_IffEq) x y :
  F x ~{ C }~> y ≊ x ~{ D }~> U y :=
  {| to := {| morphism := fun f => fmap[U] f ∘ (@unit' H _) |} ;
   from := {| morphism := fun g => (@counit' H _) ∘ fmap[F] g |} |}.
Next Obligation.
unfold Proper. unfold respectful.  intros. rewrite X. reflexivity. Qed.
Next Obligation.
unfold Proper. unfold respectful.  intros. rewrite X. reflexivity. Qed.
Next Obligation.  apply (@iffeq H). reflexivity. Qed.
Next Obligation.  apply (@iffeq H). reflexivity. Qed.

Print Implicit iffeq.
Print Implicit iff_adj.
Print Implicit naturality.

Program Definition Adjunction_IffEq_to_Universal (H : Adjunction_IffEq) :
  F ⊣ U := {| adj := iff_adj H |}.
Next Obligation.  rewrite fmap_comp.  rewrite <- !comp_assoc.
  rewrite AIE_unit_nt. reflexivity. Qed.
Next Obligation.  rewrite fmap_comp.  apply comp_assoc_sym. Qed.
Next Obligation.  rewrite fmap_comp.  apply comp_assoc. Qed.
Next Obligation.  rewrite fmap_comp.  rewrite !comp_assoc.
  rewrite AIE_counit_nt. reflexivity. Qed.

Check Category.Adjunction.Hom.hom_unit.
Check Category.Adjunction.Hom.hom_adj.
Print Implicit Category.Theory.Natural.Transformation.transform.
Print Implicit Category.Theory.Natural.Transformation.naturality.

(*
(* turn forall x : A * B, ... to forall (x : A) (y : B), ... *) 
Ltac sep_forallp fap := 
  apply allT_prod_sep in fap ;
  rewrite punc_fun in fap ; simpl in fap ;
  unfold all2T in fap.

(* do something to a hypothesis under a forall *)
Ltac under_forall f nun :=
  eassert (allT _ _) as ufX ; [ intros ufv ;
  specialize (nun ufv) ; f nun ; exact nun |
  unfold allT in ufX ; clear nun ; rename ufX into nun ].
    
Ltac under_forall2 f nun :=
  eassert (all2T _ _ _) as ufX ; [ intros ufv ufw ;
  specialize (nun ufv ufw) ; f nun ; exact nun |
  unfold all2T in ufX ; clear nun ; rename ufX into nun ].
*)   

Lemma Adjunction_Transform_to_IffEq (A : F ∹ U) : Adjunction_IffEq.
Proof. destruct A.
apply (Build_Adjunction_IffEq (transform unit) (transform counit)).
intros. split ; intro ; rewrite <- X ; rewrite fmap_comp.
- rewrite comp_assoc.
pose (naturality_sym counit _ _ f). simpl in e.
rewrite e.  rewrite <- comp_assoc.
rewrite (counit_fmap_unit x).  apply id_right.
- rewrite <- comp_assoc.
pose (naturality unit _ _ g). simpl in e.
rewrite e.  rewrite comp_assoc.
rewrite (fmap_counit_unit y).  apply id_left. Qed.

Program Definition Adjunction_OW_to_IffEq (A : Adjunction_OW) :
  Adjunction_IffEq := {| unit' := transform unitOW ; counit' := AOW_counit A |}.
Next Obligation. rewrite <- AOW_adjr_eq. apply adjruc. Qed.

(* can use these to detect when there is a coerced function not
  shown at the head of a goal or a hypothesis
Definition ap T U f (x : U) : T := f x.
Definition apI W f (x : W) (X : f x) := X : ap Type W f x.
Definition apD W f (x : W) (X : ap Type W f x) := X : f x.
*)

End CDFU.

(* neater version of this later, but keep comments in this one
  about the difficulties encountered *)
Lemma Adjunction_Hom_to_IffEq {C D F U} (A : Adjunction_Hom F U) :
  @Adjunction_IffEq C D F U.
Proof.
destruct A.  destruct hom_adj.
destruct to as [ tun nun nsun ].
destruct from as [ tcoun ncoun nscoun ].
pose (fun x => tun (x, F x) id) as un.
pose (fun y => tcoun (U y, y) id) as coun.
simpl in *. clear nsun nscoun. (* not used *)

(* now convert forall pair to two foralls *)
(* because these fail 
rewrite -> fmap_id, id_left, id_right in iso_to_from.
rewrite fmap_id, id_left, id_right in iso_from_to.
*)
(* simpler approach to singling quantified arguments *)
pose (fun a b c d j k => nun (a, b) (c, d) (j, k)) as nuns.
pose (fun a b c d j k => ncoun (a, b) (c, d) (j, k)) as ncouns.
simpl in nuns.  simpl in ncouns.  clearbody nuns ncouns. clear nun ncoun.

(* note, this is good for understanding tun, tcoun,
  works because of implicit coercion morphism *)
pose (fun x y f => tun (x, y) f) as tuns. simpl in tuns.
pose (fun x y g => tcoun (x, y) g) as tcouns. simpl in tcouns.

apply (Build_Adjunction_IffEq F U un coun).
intros.  unfold un. unfold coun.
(* some previous version required these but not now
pose (proper_morphism (tun (x, y))) as ptuxy.
pose (proper_morphism (tcoun (x, y))) as ptcxy. *)
pose (ncouns _ _ _ _ g id id) as ncg.  rewrite fmap_id, !id_left in ncg.
pose (nuns _ _ _ _ id f id) as nuf.  rewrite fmap_id, !id_right in nuf.
rewrite ncg, nuf.  split ; intros ; rewrite <- X.
- rewrite iso_from_to, fmap_id, id_left. apply id_right.
- rewrite iso_to_from, fmap_id, id_left. apply id_right.
Qed.

Print Implicit Adjunction_Hom_to_IffEq.

(* alternative to Adjunction_Hom_to_IffEq *)
Program Definition Adjunction_Hom_to_IffEq_alt {C D F U} 
  (A : @Adjunction_Hom C D F U) : @Adjunction_IffEq C D F U := 
  {| unit' := λ x : obj[D], to hom_adj (x, fobj[F] x) id{C} ;
    counit' := λ x : obj[C], from hom_adj (fobj[U] x, x) id{D} |}.
Next Obligation.
pose (iso_to_from hom_adj) as tf.  simpl in tf.
pose (iso_from_to hom_adj) as ft.  simpl in ft.
pose (fun a b c d j k => naturality (to hom_adj) (a, b) (c, d) (j, k)) as nuns.
pose (fun a b c d j k => 
  naturality (from hom_adj) (a, b) (c, d) (j, k)) as ncouns.
simpl in *. 

pose (ncouns _ _ _ _ g id id) as ncg.  rewrite fmap_id, !id_left in ncg.
pose (nuns _ _ _ _ id f id) as nuf.  rewrite fmap_id, !id_right in nuf.
rewrite ncg, nuf.  split ; intros ; rewrite <- X.
- rewrite ft, fmap_id, id_left. apply id_right.
- rewrite tf, fmap_id, id_left. apply id_right.  Qed.

(* note here how only two of the four conditions in the
  definition of Adjunction are used, this is because
  to_adj_nat_l and from_adj_nat_l say the same thing, likewise
  to_adj_nat_r and from_adj_nat_r (given that adj is an isormorphism)
  *)
Program Definition Adjunction_Universal_to_IffEq {C D F U} (A : F ⊣ U)
  : @Adjunction_IffEq C D F U := {|
    unit' := fun x => to adj id ; counit' := fun y => from adj id |}.
Next Obligation.  split ; intro ; rewrite <- X ; rewrite <- to_adj_nat_r ;
  rewrite <- from_adj_nat_l ; rewrite id_left, id_right.
{ exact (iso_from_to (adj[A]) f). }
(* this works because (iso_from_to (adj[A])) is
  (adj[A])⁻¹ ∘ adj[A] ≈ id{Sets}
  and the definition of ≈ in SetoidMorphism_Setoid is
  equiv := λ f g : SetoidMorphism x y, ∀ x0 : x, f x0 ≈ g x0;
  so applying it to f gives ((adj[A])⁻¹ ∘ adj[A]) f ≈ id{Sets} f
  which simplifies to (adj[A])⁻¹ (adj[A] f) ≈ f *)
exact (iso_to_from (adj[A]) g). Qed.

(*
Print Implicit iso_from_to.
Print Implicit hom.
Print Implicit adj.
Print Implicit to_adj_nat_l.
*)

Arguments Adjunction_IffEq {C D} F%functor U%functor.
Arguments Adjunction_IffEq_to_Universal {C D F%functor U%functor}.
Arguments Adjunction_IffEq_to_Transform {C D F%functor U%functor}.
Arguments Adjunction_Transform_to_IffEq {C D F%functor U%functor}.
Arguments Adjunction_Universal_to_IffEq {C D F%functor U%functor}.
Arguments Adjunction_IffEq_to_OW {C D F%functor U%functor}.
Arguments Adjunction_OW_to_IffEq {C D F%functor U%functor}.
Arguments iff_unit {C D F%functor U%functor}.
Arguments iff_counit {C D F%functor U%functor}.
Arguments unit' {C D F%functor U%functor}.
Arguments counit' {C D F%functor U%functor}.
Arguments iffeq {C D F%functor U%functor}.
Arguments adjruc {C D F%functor U%functor}.
(*
*)

Print Implicit Adjunction_IffEq_to_Transform.
Print Implicit Adjunction_Transform_to_IffEq.
Print Implicit Adjunction_Universal_to_IffEq.
Print Implicit Adjunction.
Print Implicit Adjunction_OW.
Print Implicit Adjunction_OW_to_IffEq.
Print Implicit Adjunction_IffEq_to_OW.
Print Implicit Adjunction_Transform.
Print Implicit Adjunction_IffEq.
Print Implicit unit'.
Print Implicit iff_unit.
Print Implicit iffeq.
Print Implicit adjruc.
Print Implicit naturality_sym.
Print Implicit id.
Print Category.Adjunction.Natural.Transformation.Adjunction_Transform.


(* an alternative attempt at Adjunction_Universal_to_IffEq had at one point
h : {| carrier := F x ~{ C }~> F x;
             is_setoid := homset (F x) (F x) |}
	      ~{ Sets }~>
	      {| carrier := x ~{ D }~> U (F x);
               is_setoid := homset x (U (F x)) |}
when destruct h gave
morphism : {| carrier := F x ~{ C }~> F x;
             is_setoid := homset (F x) (F x) |}
             → {| carrier := x ~{ D }~> U (F x);
               is_setoid := homset x (U (F x)) |}
there is a coercion here, doing unfold carrier gives
  morphism : F x ~{ C }~> F x → x ~{ D }~> U (F x)
use Set Printing Coercions to see what is happening
which may also require Set Printing Implicit. to make output meaningful
*)
(* in proof of iff_unit, a lot of rewriting attempts lead to errors, like 
> rewrite (@fmap_id _ _ U) in i.
> ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Illegal application:
The term "@respectful" of type
 "∀ A B : Type, crelation A → crelation B → crelation (A → B)"
cannot be applied to the terms
 "Type" : "Type"
 "Type" : "Type"
 "?c3" : "crelation Type"
 "arrow" : "Type → Type → Type"
The 4th term has type "Type → Type → Type" which should be coercible to
 "crelation Type".
this is some sort of universe problem, and other errors included
> rewrite fmap_id.
> ^^^^^^^^^^^^^^^
Error: Illegal application:
The term "@flip" of type "∀ A B C : Type, (A → B → C) → B → A → C"
cannot be applied to the terms
 "Type" : "Type"
 "Type" : "Type"
 "Type" : "Type"
 "arrow" : "Type → Type → Type"
The 4th term has type
 "Type@{Top.4115} → Type@{Top.4116} → Type@{max(Top.4115,Top.4116)}"
which should be coercible to
 "Type@{max(Top.136,Top.142)} → Type@{max(Top.136,Top.142)} → Type@{Top.4117}".
*)

(* in proof of Adjunction_Hom_to_IffEq, problem in setoid rewriting where
  setoid morphism applied to equivalent arguments, needed to 
  pose (proper_morphism (f : SetoidMorphism ...)) to make rewriting work,
  see notes in that proof for details *)

(* characterization of adjoint functors, similar to Adjunction_OW,
  but without requiring that F be a functor or that unit is a nt,
  (we _define_ action of F on arrows), 
  see Robin Cockett notes, draft April 2008, s2.2.1 *)

(*
Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
*)

Print Build_Adjunction_IffEq.
Print Build_Adjunction_OW.
Print Implicit Functor.
Print Build_Functor.
Check respectful Setoid.equiv Setoid.equiv.

Class Adjunction_OWnf {C D} (U : C ⟶ D) (Fo : obj[D] -> obj[C]) := {
  unitOWnf : forall {x : obj[D]}, (x ~{ D }~> U (Fo x)) ;
  adjrnf : forall {x y} (g : x ~{ D }~> U y), Fo x ~{ C }~> y ;
  adjrnf_respects : ∀ {x y}, 
    CMorphisms.Proper (Setoid.equiv ==> Setoid.equiv) (@adjrnf x y) ;
  (* the adjoint arrow is the unique one which makes the diagram commute *)
  adjrucnf : forall {x y} (f : Fo x ~{ C }~> y) (g : x ~{ D }~> U y),
    iffT (fmap[U] f ∘ unitOWnf ≈ g) (adjrnf g ≈ f)
  }.

Print Build_Adjunction_OWnf.

Program Definition Adjunction_nf_to_fun {C D} U Fo (H : Adjunction_OWnf U Fo) :
  @Functor D C := {| fobj := Fo ;
    fmap := fun x y h => adjrnf (unitOWnf ∘ h) |}.
Next Obligation. proper. apply adjrnf_respects.
  apply compose_respects. - reflexivity. - apply X. Qed.
Next Obligation. apply adjrucnf.  rewrite fmap_id.
  rewrite id_right. apply id_left. Qed.
Next Obligation. apply adjrucnf.  rewrite fmap_comp.
(* a more complex consequence of iff of equivs - maybe a lemma? *)
pose (fun x y (g : x ~> U y) => snd (adjrucnf _ g) 
  (Coq.Classes.CRelationClasses.Equivalence_Reflexive _)) as rfu.
rewrite <- comp_assoc.  rewrite rfu.  rewrite comp_assoc.  rewrite rfu.
symmetry.  apply comp_assoc. Qed.

Print Implicit unitOWnf.
Print Implicit Transform.
Print Implicit Adjunction_nf_to_fun.
Check Adjunction_nf_to_fun.
Check Adjunction_nf_to_fun_obligation_1.
Check Adjunction_nf_to_fun_obligation_2.
Check Adjunction_nf_to_fun_obligation_3.

Program Definition Adjunction_nf_to_nt {C D} U Fo 
  (H : @Adjunction_OWnf C D U Fo) :
  Id[D] ⟹ U ◯ (Adjunction_nf_to_fun U Fo H) := 
  {| transform := @unitOWnf _ _ _ _ H |}.
Next Obligation. apply adjrucnf. reflexivity. Qed.
Next Obligation. symmetry. apply adjrucnf. reflexivity. Qed.

Check Adjunction_nf_to_nt.
Print Implicit Adjunction_nf_to_nt.
Print Implicit Adjunction_OWnf.

Program Definition Adjunction_nf_to_OW {C D} U Fo 
  (H : @Adjunction_OWnf C D U Fo) :
  Adjunction_OW (Adjunction_nf_to_fun U Fo H) U := 
  {| unitOW := Adjunction_nf_to_nt U Fo H ;
    adjr := fun x y => adjrnf ;
    adjruc := fun x y => adjrucnf |}.

Print Implicit Adjunction_nf_to_OW.
Check Adjunction_nf_to_OW.
Print Implicit Adjunction_OWnf.
Print Implicit adjruc.

(* the converse to this should be quite trivial *)
Program Definition Adjunction_OW_to_nf {C D} F U 
  (H : @Adjunction_OW C D F U) :
  Adjunction_OWnf U (@fobj _ _ F) := 
  {| unitOWnf := transform (@unitOW _ _ _ _ H) ;
    adjrnf := @adjr _ _ F U H ;
    adjrucnf := @adjruc _ _ F U H |}.
Next Obligation. proper.
(* interesting proof of Proper (equiv ==> equiv) (adjr _ _) 
  maybe make this a lemma ? *)
apply adjruc. rewrite X. apply adjruc. reflexivity. Qed.

(*
So can we drop the assumption in Adjunction_OW that unit is a nt,
and prove it as in Adjunction_OWnf, by showing that fmap[F]
is as defined in Adjunction_nf_to_fun?
Unlikely as Class Adjunction_OW says nothing about fmap[F]
except that unitOW is a nt
*)

Print Implicit unit'.
Print Implicit Compose.

(* composition of adjunctions *)
Program Definition Adjunction_IffEq_comp {C D E F F' U U'} 
  (H : @Adjunction_IffEq C D F U) (H' : @Adjunction_IffEq D E F' U') :
  @Adjunction_IffEq C E (F ◯ F') (U' ◯ U) :=
  {| unit' := fun x => fmap[U'] (unit' H (F' x)) ∘ (unit' H' x) ;
  counit' := fun y => (counit' H y) ∘ fmap[F] (counit' H' (U y)) |}.
Next Obligation.  (* rewrite <- comp_assoc. fails *)
split ; intro.
- rewrite <- comp_assoc.  rewrite <- fmap_comp.
apply iffeq.  symmetry. apply iffeq.
rewrite fmap_comp.  rewrite <- comp_assoc.  exact X.
- rewrite comp_assoc.  rewrite <- fmap_comp.
apply iffeq.  apply symmetry. apply iffeq.
rewrite fmap_comp.  rewrite comp_assoc.  exact X.
Qed.

Check Adjunction_IffEq_comp_obligation_1.
Print Adjunction_IffEq_comp.

(*
Set Printing Coercions.
Set Printing Implicit.
Set Printing Notations.
Unset Printing Coercions.
Unset Printing Implicit.
Unset Printing Notations.
*)

