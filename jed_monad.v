
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
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets. (* required for morphism below *)
Require Import Category.Monad.Kleisli.
Require Import jed_adjfuns.

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
Print Category.Theory.Monad.Monad.
(* Monad: including 2 properties of function, 7 conditions,
  note that the first two of the 5 given say that ret and join
  are natural transformations *)
Print Adjunction.

(* this is the definition, in the Monad, of ext as used in Monad3 *)
Definition extm {C M} (H : @Monad C M) x y (f : x ~> M y) := 
  @join C M H _ ∘ fmap[M] f : M x ~> M y.
  
Lemma extm_respects {C M} (H : @Monad C M) x y :
  Proper (equiv ==> equiv) (extm H x y).
Proof. proper. unfold extm. apply compose_respects.
- reflexivity.  - rewrite X. reflexivity. Qed.

(* defining join and fmap[M] from it as used in Monad_from_3 below
  gives back the original join and fmap[M] *)

Lemma join_ext_id {C M} (H : @Monad C M) x : @join C M H x ≈ extm H _ x id.
Proof. unfold extm. rewrite fmap_id, id_right. reflexivity. Qed.

Lemma map_ext_uo {C M} (H : @Monad C M) x y (f : x ~> y) :
  fmap[M] f ≈ extm H x y (ret[M] ∘ f).
Proof. unfold extm. rewrite fmap_comp, comp_assoc.
  rewrite join_fmap_ret.  rewrite id_left.  reflexivity. Qed.

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

Lemma map3_respects (H : Monad3) (x y : obj[C]) :
  Proper (equiv ==> equiv) (@map3 H x y).
Proof. proper. apply ext_respects.  rewrite X. reflexivity. Qed.

Print Implicit join3.
Print Implicit map3.
Print Implicit ret3.

(* prove that map3 is a functor *)
Program Definition Functor_from_3 (H : Monad3) : Functor :=
  {| fobj := M ; fmap := @map3 H |}.
Next Obligation.  proper. apply map3_respects. exact X. Qed.
Next Obligation.  unfold map3. pose ext_respects.
rewrite id_right. (* fails without using ext_respects *) apply m_id_l. Qed.
Next Obligation.  unfold map3. rewrite m_assoc.
apply ext_respects.  rewrite !comp_assoc. (* fails w/o ext_respects *)
rewrite m_id_r. reflexivity. Qed.

Print Implicit Functor_from_3.
Check Functor_from_3_obligation_1.
Check Functor_from_3_obligation_2.
Check Functor_from_3_obligation_3.

Definition map3_id := Functor_from_3_obligation_2.
Definition map3_comp := Functor_from_3_obligation_3.

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

Lemma ext_o (H : Monad3) x y z (f : x ~{ C }~> y) (g : y ~{ C }~> M z) :
  ext H (g ∘ f) ≈ ext H g ∘ map3 H f.
Proof. rewrite !ext_jm. rewrite map3_comp.  apply comp_assoc. Qed.

Program Definition Monad_from_3 (H : Monad3) : @Monad C (Functor_from_3 H) := 
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
Proof. intros. apply compose_respects. - apply X. - reflexivity. Qed.

Lemma comp_o_l : ∀ C (y z : obj[C]) (f g : y ~{ C }~> z), f ≈ g → 
  ∀ x (h : z ~{ C }~> x), h ∘ f ≈ h ∘ g.
Proof. intros. apply compose_respects. - reflexivity. - apply X. Qed.

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
Print Category.Theory.Monad.Monad.

(* here are two ways of setting up the same proof,
  but the Program Definition is much nicer to print *)
Lemma Monad_to_3 {C M} (H : @Monad C M) : @Monad3 C (@fobj _ _ M).
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

Program Definition Monad3_from_Monad {C M} (H : @Monad C M) : @Monad3 C fobj := 
  {| ret3 := fun x => ret ; ext := extm H|}.
Next Obligation. proper. pose extm_respects. rewrite X. reflexivity. Qed.
Next Obligation. unfold extm.  rewrite <- comp_assoc, <- fmap_ret.
rewrite comp_assoc, join_ret. apply id_left. Qed.
Next Obligation. apply join_fmap_ret. Qed.
Next Obligation. unfold extm. rewrite !fmap_comp.
rewrite !comp_assoc.  rewrite join_fmap_join.
apply comp_o_r.  rewrite <- !comp_assoc.
rewrite join_fmap_fmap.  reflexivity. Qed.

Check Monad3_from_Monad_obligation_1.
Check Monad3_from_Monad_obligation_2.
Check Monad3_from_Monad_obligation_3.
Check Monad3_from_Monad_obligation_4.

Check Monad_to_3.
Check Monad3_from_Monad.

(* round-trip, get back to the same functor *)
Lemma m_to_3_same_fun {C M} (H : @Monad C M) :
  Functor_from_3 (Monad3_from_Monad H) ≈ M.
Proof. simpl. exists (fun x => @iso_id _ (fobj[M] x)).
intros. simpl. rewrite id_left. rewrite id_right.
unfold extm. rewrite fmap_comp, comp_assoc.
rewrite join_fmap_ret. apply id_left. Qed.

Definition m_3_m {C M} (H : @Monad C M) :=
  Monad_from_3 (Monad3_from_Monad H).

Lemma m_3_m_join {C M} (H : @Monad C M) x :
  @join _ _ (m_3_m H) x ≈ @join _ _ H x.
Proof. simpl. unfold extm. rewrite fmap_id. apply id_right. Qed.

Lemma m_3_m_ret {C M} (H : @Monad C M) x :
  @ret _ _ (m_3_m H) x ≈ @ret _ _ H x.
Proof. reflexivity. Qed.

(* definition of round-trip, Monad3 -> Monad -> Monad3,
  that it is accepted shows that we get back the same object map M *)
Definition m3_m_3 {C M} (H : @Monad3 C M) :=
  Monad3_from_Monad (Monad_from_3 H) : @Monad3 C M.

Lemma m3_m_3_ext {C M} (H : @Monad3 C M) x y (f : x ~> M y) : 
  ext (m3_m_3 H) f ≈ ext H f.
Proof. simpl. unfold extm. simpl. rewrite ext_jm. reflexivity. Qed.

Lemma m3_m_3_ret3 {C M} (H : @Monad3 C M) x : @ret3 _ _ (m3_m_3 H) x ≈ ret3 H.
Proof. reflexivity. Qed.

(* round-trip, get back to the same monad
Lemma m_3_m_same C M (H : @Monad C M) :
  Monad_from_3 (Monad3_from_Monad H) ≈ H.
The term "H" has type "Monad M" while it is expected to have type
"Monad (Functor_from_3 (Monad3_from_Monad H))"

Lemma m3_m_3_same C Mo (H : @Monad3 C Mo) :
  Monad3_from_Monad (Monad_from_3 H) ≈ H.
  different error:
  Unable to satisfy the following constraints:
In environment: ...
?Setoid : "Setoid Monad3"
(as equivalences of monads are not defined)
*)

(* 
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Coercions.
Unset Printing Implicit.
*)

(** the Kleisli category of a monad **)
Print Category.Monad.Kleisli.Kleisli. (* Kleisli construction is a category *)
Print Implicit Category.Monad.Kleisli.kleisli_compose.
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
- apply ext_respects. exact X. - exact X0. Qed.
Next Obligation.  rewrite m_id_l. apply id_left. Qed.
Next Obligation. apply m_id_r. Qed.
Next Obligation. rewrite comp_assoc.  apply comp_o_r.  apply m_assoc. Qed.
Next Obligation. symmetry.  apply Kleisli_from_3_obligation_4. Qed.

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
Next Obligation. symmetry. apply m_assoc. Qed.

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
split ; symmetry ; assumption. Qed.

Check k_adj.  Check k_adj_obligation_1.

Print Implicit Compose. (* composition of functors, "F ◯ G" := Compose F G *)
Print Implicit adjruc.
Print Implicit adjrucnf.

(** Every adjunction gives rise to a monad. **)
Require Category.Monad.Adjunction.
Check Category.Monad.Adjunction.Adjunction_Monad.

Program Definition AOW_to_Monad3 {C D F U}
  (H : @Adjunction_OW C D F U) : @Monad3 D (fobj[Compose U F]) :=
  {| ret3 := transform (unitOW F U) ;
     ext := fun x z h => fmap[U] (adjr F U h : F x ~{ C }~> F z) |}.
Next Obligation. proper. apply fmap_respects.
apply adjruc. rewrite X. apply adjruc. reflexivity. Qed.
Next Obligation.  apply adjruc. reflexivity. Qed.

(* rewrite AOW_adjr_unit_id fails - why?  but next succeeds *)
Next Obligation.  rewrite (AOW_adjr_unit_id F U H x). apply fmap_id. Qed.
 
Next Obligation.
Check adjr.  Check unitOW.  Check (adjruc H).
rewrite <- fmap_comp. apply fmap_respects. 
symmetry. apply adjruc.
rewrite fmap_comp.  rewrite <- comp_assoc.
apply comp_o_l. apply adjruc. reflexivity. Qed.

(* this proof very similar to AOW_to_Monad3 *)
Program Definition AIE_to_Monad3 {C D F U}
  (H : @Adjunction_IffEq C D F U) : @Monad3 D (fobj[Compose U F]) :=
  {| ret3 := unit' H ;
    ext := fun x z h => fmap[U] (counit' H _ ∘ fmap[F] h) |}.
Next Obligation. proper. apply fmap_respects. rewrite X. reflexivity. Qed.
Next Obligation.  apply iffeq.  reflexivity. Qed.
Next Obligation. rewrite AIE_counit_fmap_unit.  apply fmap_id. Qed.
Next Obligation.  rewrite <- fmap_comp. apply fmap_respects. 
rewrite (@fmap_comp _ _ F). rewrite !comp_assoc.
rewrite AIE_counit_nt.  reflexivity. Qed.

Check AOW_to_Monad3.  Check AIE_to_Monad3.
Check AIE_to_Monad3_obligation_2.
Check AIE_to_Monad3_obligation_3.
Check AIE_to_Monad3_obligation_4.

(* show that the monad arising from the adjunction k_adj
  is the same one we started with *)
(* note - that Coq accepts this definition shows that the object map
  resulting from AIE_to_Monad3 (k_adj H) is the same as M *)
Definition m3_k_adj_m3x {C M} (H : @Monad3 C M) :=
  AIE_to_Monad3 (k_adj H) : @Monad3 C M.

Lemma m3_k_adj_m3_ext {C M} (H : @Monad3 C M) x y :
  ext (m3_k_adj_m3x H) ≈ @ext C M H x y.
Proof. simpl. intros.  apply ext_respects.
rewrite comp_assoc. rewrite m_id_r. apply id_left. Qed.

Lemma m3_k_adj_m3_ret3 {C M} (H : @Monad3 C M) x :
  ret3 (m3_k_adj_m3x H) ≈ @ret3 C M H x.
Proof. reflexivity. Qed.

(* try separate proof for Monad *)
Program Definition AIE_to_Monad {C D F U}
  (H : @Adjunction_IffEq C D F U) : @Monad D (Compose U F) :=
  {| ret := unit' H ; join := fun x => fmap[U] (counit' H _) |}.
Next Obligation. symmetry. apply AIE_unit_nt. Qed.
Next Obligation. rewrite <- !fmap_comp. apply fmap_respects.
  apply AIE_counit_nt. Qed.
Next Obligation. rewrite <- fmap_comp. rewrite AIE_counit_fmap_unit.
  apply fmap_id. Qed.
Next Obligation. apply AIE_fmap_counit_unit. Qed.
Next Obligation. rewrite <- !fmap_comp. apply fmap_respects. 
  apply AIE_counit_nt. Qed.

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

(** Eilenberg-Moore category **)
Require Import Category.Monad.Algebra.
Print Category.Monad.Algebra.Build_TAlgebra.
Print Category.Monad.Algebra.Build_TAlgebraHom.
Require Import Category.Monad.Eilenberg.Moore.
Check Category.Monad.Eilenberg.Moore.EilenbergMoore.
Check @Category.Monad.Eilenberg.Moore.EilenbergMoore.
Print Category.Monad.Eilenberg.Moore.EilenbergMoore.
Print Implicit TAlgebra. (* C, H implicit, maximal - weird *)
Print Implicit EilenbergMoore. (* ditto *)

(* join of a monad M is an M-algebra *)
Program Definition join_is_alg {C M} H a : @TAlgebra C M H (fobj[M] a) :=
  {| t_alg := join ; t_id := join_ret ; t_action := join_fmap_join |}.

Definition join_is_ex_alg {C M} H a : ∃ y, @TAlgebra C M H y :=
 existT (@TAlgebra C M H) (fobj[M] a) (join_is_alg H a).

Program Definition join_alg_arr {C M} (H : @Monad C M) x y (arr : @hom C x y) :
  @TAlgebraHom C M H _ _ (join_is_alg H x) (join_is_alg H y) :=
  {| t_alg_hom := fmap[M] arr |}.
Next Obligation. symmetry. apply join_fmap_fmap. Qed.

(* given a T-algebra, there is a T-Algebra arrow from the join algebra to it *)
Program Definition join_to_alg {C M} H a (alg : @TAlgebra C M H a) :
  @TAlgebraHom C M H _ _ (join_is_alg H a) alg := {| t_alg_hom := t_alg |}.
Next Obligation. symmetry. apply t_action. Qed.

(* obtaining the object and arrow from an object of the Eilenberg-Moore
  category (which is an algebra of existential type) *)
(* note notation `1 (y) meaning (projT1 y), etc *)
Definition alg_obj {C M H} (alg : ∃ a : obj[C], @TAlgebra C M H a) :=
  projT1 alg : obj[C].
Definition alg_arr {C M H} (alg : ∃ a : obj[C], @TAlgebra C M H a) :=
  t_alg[projT2 alg].
Definition alg_obj_alt {C M H} alg := cod (@alg_arr C M H alg).
Definition alg_hom {C M H} (x y : ∃ a : obj[C], @TAlgebra C M H a)
  (ah : TAlgebraHom M _ _ (projT2 x) (projT2 y)) := t_alg_hom[ah].

(* JED version of Eilenberg-Moore category, because the version in
Print Category.Monad.Eilenberg.Moore.EilenbergMoore.
uses EilenbergMoore_obligation_1 where 
EilenbergMoore_obligation_1 C M H seems to be H but can't be used
because it is opaque and can't be made transparent; thus we find we need
((∃ y, TAlgebra M y) = obj[EilenbergMoore M]) but can't prove it;

Program Definition fun_to_EM C M (H : @Monad C M) : @Functor 
  C (@EilenbergMoore C M H) :=
  {| fobj := fun a => existT (@TAlgebra C M H) 
    (fobj[M] a) (join_is_alg H a) |}.
    gives error Unable to unify "@TAlgebra C M H" with
 "λ a : obj[C], @TAlgebra C M (Moore.EilenbergMoore_obligation_1 C M H) a".

Set Printing Implicit.
Unset Printing Implicit.
*)

Program Definition JEM {C T} (H : @Monad C T) : Category := {|
  obj     := ∃ a : C, @TAlgebra C T H a;
  hom     := fun x y => TAlgebraHom T ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => t_alg_hom[f] ≈ t_alg_hom[g] |};
  id      := fun _ => {| t_alg_hom := id |};
  compose := fun _ _ _ f g => {| t_alg_hom := t_alg_hom[f] ∘ t_alg_hom[g] |}
|}.
Next Obligation.  rewrite fmap_comp.  rewrite comp_assoc.
  rewrite <- t_alg_hom_commutes.  rewrite <- !comp_assoc.
  rewrite <- t_alg_hom_commutes.  reflexivity.  Qed.

Print JEM.

Check fun C M H a => join_is_ex_alg H a : obj[JEM H].

(* functors to and from Eilenberg-Moore category *)
Program Definition fun_from_JEM {C M} (H : @Monad C M) : @Functor 
  (JEM H) C := {| fobj := alg_obj ; fmap := alg_hom |}.

Program Definition fun_to_JEM {C M} (H : @Monad C M) : @Functor C (JEM H) :=
  {| fobj := join_is_ex_alg H ; fmap := join_alg_arr H |}.
Next Obligation. proper. apply fmap_respects. exact X. Qed.
Next Obligation. apply fmap_comp. Qed.

(* now to show these functors are adjoint *)
Program Definition adj_EM {C M} (H : @Monad C M) : 
  Adjunction_IffEq (fun_to_JEM H) (fun_from_JEM H) :=
  {| unit' := @ret C M H ;
    counit' := fun alg => join_to_alg H (projT1 alg) (projT2 alg) |}.
Next Obligation. unfold alg_hom. split ; intro ; rewrite <- X0.
- rewrite fmap_comp, comp_assoc.
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ f).  simpl.
  rewrite <- comp_assoc.  rewrite join_fmap_ret. apply id_right.
- rewrite <- comp_assoc.  rewrite <- fmap_ret.
  rewrite comp_assoc.  rewrite t_id.  apply id_left. Qed.

Check adj_EM_obligation_1.

(* the functors to and from the EM category compose to give the functor M *)
Lemma EM_funs_M {C M} (H : @Monad C M) : fun_from_JEM H ◯ fun_to_JEM H ≈ M.
Proof. exists (fun x => iso_id). intros. simpl.
rewrite id_left, id_right. reflexivity. Qed.

Definition m_adj_EM_m {C M} (H : @Monad C M) := AIE_to_Monad (adj_EM H).

(* show that the monad arising from this adjunction
  is the same one we started with *)

(* this isn't accepted by Coq without the type annotation *)
Lemma m_adj_EM_m_join {C M} H x : @join _ _ (m_adj_EM_m H) x ≈ 
    (@join _ _ H x : fobj[M] (fobj[M] x) ~{ C }~> fobj[M] x).
Proof. reflexivity. Qed.

Lemma m_adj_EM_m_ret {C M} H x : @ret _ _ (m_adj_EM_m H) x ≈ 
    (@ret _ _ H x : x ~{ C }~> fobj[M] x).
Proof. reflexivity. Qed.

(* Eilenberg-Moore category final among ways of factoring a monad
  as an adjoint pair of functors *)
(* given an adjunction, natural choice of algebra *) 
Program Definition AIE_to_alg {C D F U} 
  (H : @Adjunction_IffEq C D F U) (c : obj[C]) :
  @TAlgebra D _ (Monad_from_3 (AIE_to_Monad3 H)) (fobj[U] c) :=
  {| t_alg := fmap[U] (counit' H c) ; 
    t_id := AIE_fmap_counit_unit F U H c |}.
Next Obligation.  rewrite fmap_id, id_right.
rewrite (@fmap_comp _ _ F).  rewrite comp_assoc, fmap_comp.
rewrite AIE_to_Monad3_obligation_3.  rewrite id_left.
rewrite <- !fmap_comp.  apply fmap_respects.
apply AIE_counit_nt. Qed.

Program Definition AIE_to_fun_to_EM {C D F U} (H : @Adjunction_IffEq C D F U) :
  @Functor C (JEM (Monad_from_3 (AIE_to_Monad3 H))) :=
  {| fobj := fun c => existT _ (fobj[U] c) (AIE_to_alg H c) ;
    fmap := fun c c' f => {| t_alg_hom := fmap[U] f |} |}.
Next Obligation.  rewrite (@fmap_comp _ _ F). rewrite comp_assoc, fmap_comp.
rewrite AIE_to_Monad3_obligation_3.  rewrite id_left.
rewrite <- !fmap_comp.  apply fmap_respects.
symmetry. apply AIE_counit_nt. Qed.
Next Obligation. proper. rewrite X. reflexivity. Qed.
Next Obligation. apply fmap_comp. Qed.

Print AIE_to_alg.
Print join_is_alg.
Print join_is_ex_alg.

Program Definition ex_iso_alg {C D F U} (H : @Adjunction_IffEq C D F U) x :
  @Isomorphism (JEM (Monad_from_3 (AIE_to_Monad3 H))) 
  (fobj[U] (fobj[F] x); AIE_to_alg H (fobj[F] x))
  (fobj[U] (fobj[F] x); join_is_alg (Monad_from_3 (AIE_to_Monad3 H)) x) :=
  {| to := {| t_alg_hom := id |} ;
    from := {| t_alg_hom := id |} |}.
Next Obligation. rewrite fmap_id, !id_right, id_left.
rewrite AIE_counit_fmap_unit. 
rewrite fmap_id, id_right. reflexivity. Qed.
Next Obligation. rewrite fmap_id, !id_right, id_left.
rewrite AIE_counit_fmap_unit. 
rewrite fmap_id, id_right. reflexivity. Qed.

(* without (JEM _) get errors
The term "(fobj[U] (fobj[F] x); AIE_to_alg H (fobj[F] x))" has type
 "∃ y, ?P y" while it is expected to have type "obj[?C]".  *)

(* but the following 
Lemma ex_iso_alg_alt {C D F U} (H : @Adjunction_IffEq C D F U) x :
  @Isomorphism (JEM (Monad_from_3 (AIE_to_Monad3 H))) 
  (fobj[U] (fobj[F] x); AIE_to_alg H (fobj[F] x))
  (fobj[U] (fobj[F] x); join_is_alg (Monad_from_3 (AIE_to_Monad3 H)) x).
Proof.  eapply iso_id.
gives error Unable to unify
 "(fobj[U] (fobj[F] x); join_is_alg (Monad_from_3 (AIE_to_Monad3 H)) x)" with
 "(fobj[U] (fobj[F] x); AIE_to_alg H (fobj[F] x))".

illustration of types
Check (fobj[U] (fobj[F] x); AIE_to_alg H (fobj[F] x)).
Check join_is_ex_alg (Monad_from_3 (AIE_to_Monad3 H)) x.
 : ∃ y : obj[D], TAlgebra (Functor_from_3 (AIE_to_Monad3 H)) y.

Check (AIE_to_alg H (fobj[F] x)).
  : TAlgebra (Functor_from_3 (AIE_to_Monad3 H)) (fobj[U] (fobj[F] x))
Check (join_is_alg (Monad_from_3 (AIE_to_Monad3 H)) x).
  : TAlgebra (Functor_from_3 (AIE_to_Monad3 H))
         (fobj[Functor_from_3 (AIE_to_Monad3 H)] x).

so in the notation for existT, 
P is TAlgebra (Functor_from_3 (AIE_to_Monad3 H))
x is (fobj[U] (fobj[F] x)) or (fobj[Functor_from_3 (AIE_to_Monad3 H)] x)

projT1
(fobj[U] (fobj[F] x); join_is_alg (Monad_from_3 (AIE_to_Monad3 H)) x) : obj[D]
projT2
(fobj[U] (fobj[F] x); join_is_alg (Monad_from_3 (AIE_to_Monad3 H)) x) : 
  TAlgebra (Functor_from_3 (AIE_to_Monad3 H)) (fobj[U] (fobj[F] x)).
*)

Lemma AIE_F_EM_comp {C D F U} (H : @Adjunction_IffEq C D F U) :
  Compose (AIE_to_fun_to_EM H) F ≈ 
  fun_to_JEM (Monad_from_3 (AIE_to_Monad3 H)).
Proof. simpl. exists (ex_iso_alg H). intros. simpl.
rewrite id_left, id_right.  apply fmap_respects.
symmetry.  apply iffeq. apply AIE_unit_nt. Qed.

Lemma AIE_EM_comp_U {C D F U} (H : @Adjunction_IffEq C D F U) :
  Compose (fun_from_JEM (Monad_from_3 (AIE_to_Monad3 H)))
  (AIE_to_fun_to_EM H) ≈ U. 
Proof. simpl.  exists (fun x => (@iso_id _ _)). intros.
rewrite id_left.  rewrite id_right. reflexivity. Qed.
  
Print TAlgebra.
Print TAlgebraHom.
Print Implicit naturality.
Print Implicit Kleisli_from_3.
Print Implicit ret_o_functor.
Print Implicit counit'.
Print Implicit iffeq.
Print Implicit fobj.
Print Implicit iso_id.
Print Category.Theory.Functor.Functor.
Print Implicit Functor.
Print Adjunction_IffEq.
Print Implicit Kleisli_from_3.  
Print Implicit AIE_to_Monad3.  

(* 
Set Printing Coercions.
Set Printing Implicit.
Set Printing Notations.
Unset Printing Coercions.
Unset Printing Implicit.
Unset Printing Notations.
*)

