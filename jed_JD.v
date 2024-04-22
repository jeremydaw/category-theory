
(* need to use
coqtop -color no -R /home/jeremy/coq/category-theory Category
Load jed_JD.
coqc -R /home/jeremy/coq/category-theory Category jed_JD.v
cat jed_JD.v - | coqtop -color no -R /home/jeremy/coq/category-theory Category
*)

(* implementation of material in 
  Mark P. Jones and Luc Duponcheel, Composing Monads
  Research Report YALEU/DCS/RR-1004, Yale University, December 1993 *)

Require Import Category.Lib. (* needed for notation *)
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Algebra.
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
Print Implicit Functor.
Print Implicit fmap_comp.
Print Functor.

(* this is the prod construction conditions of Jones & Duponcheel, s3.2,
  expressed using their definitions of unitMN and mapMN and joinMN ;
  for joinMN we write it using ext *)

Definition retc x := @ret3 C M M3 _ ∘ @ret3 C N N3 x.
Definition mapc {x y} f := map3 M3 (@map3 C N N3 x y f).
Definition MNo x := M (N x). (* object map *)

Lemma mapc_id {x} : mapc (@id C x) ≈ id.
Proof. unfold mapc. pose (map3_respects M3). rewrite map3_id.
apply map3_id. Qed.

Lemma mapc_comp {x y z : obj[C]} (f : y ~{ C }~> z) (g : x ~{ C }~> y) : 
  mapc (f ∘ g) ≈ mapc f ∘ mapc g.
Proof. unfold mapc. pose (map3_respects M3). rewrite map3_comp.
  apply map3_comp.  Qed.

Lemma mapc_respects {x y : obj[C]} : Proper (equiv ==> equiv) (@mapc x y).
Proof. proper.  unfold mapc.  apply (map3_respects M3).
apply (map3_respects N3). exact X. Qed.

(* MNf is functor, MNo is object map *)
(* not used any more, as we got a type error 
... has type "Monad (Functor_from_3 M3 ◯ Functor_from_3 N3)"
while it is expected to have type "Monad MNf". 
Program Definition MNf : Functor := {| fobj := MNo ; fmap := @mapc ;
  fmap_id := @mapc_id ; fmap_comp := @mapc_comp ;
  fmap_respects := @mapc_respects |}.
*)

Definition MNf : Functor := (Functor_from_3 M3 ◯ Functor_from_3 N3).
Definition MNf_fobj x : fobj[MNf] x = MNo x := eq_refl.
Definition MNf_fmap [x y] (f : x ~> y) : fmap[MNf] f = mapc f := eq_refl.

(* composition of premonads is a premonad, Jones & Duponcheel, Figure 2 *)
(* uses only fmap_ret3 *)
Lemma premonad_comp x y (f : x ~{ C }~> y) : retc y ∘ f ≈ mapc f ∘ retc x.
Proof. unfold retc. unfold mapc. 
rewrite comp_assoc. rewrite <- (fmap_ret3 M3).  rewrite <- !comp_assoc.
rewrite <- (fmap_ret3 N3).  reflexivity. Qed.

(* Jones & Duponcheel, s3.2 *)
Record JD_P : Type := 
  { prod : ∀ x : obj[C], N (M (N x)) ~{ C }~> M (N x) ;
    P1 : ∀ x y (f : x ~{ C }~> y), 
      prod y ∘ map3 N3 (mapc f) ≈ mapc f ∘ prod x ;
    P2 : ∀ x, prod x ∘ ret3 N3 ≈ id ;
    P3 : ∀ x, prod x ∘ map3 N3 (retc x) ≈ ret3 M3 ;
    P4 : ∀ x, prod x ∘ map3 N3 (ext M3 (prod x)) ≈ ext M3 (prod x) ∘ prod _ }.

(* defining join using prod, J&D also use this to state P4 *)
Definition join_P (P : JD_P) x := ext M3 (prod P x).
Definition pext_P (P : JD_P) {x y} (f : x ~> M (N y)) := prod P y ∘ map3 N3 f.
Definition ext_P (P : JD_P) {x y} (f : x ~> M (N y)) := ext M3 (pext_P P f).
Definition swap_P (P : JD_P) x := pext_P P (map3 M3 (@ret3 _ _ N3 x)).

Lemma prod_pext_id (P : JD_P) x : prod P x ≈ pext_P P id.
Proof. unfold pext_P. rewrite map3_id. rewrite id_right. reflexivity. Qed.

Lemma pext_P_respects (P : JD_P) (x y : obj[C]) :
  Proper (equiv ==> equiv) (@pext_P P x y).
Proof. proper. unfold pext_P.  apply comp_o_l.
apply map3_respects. apply X. Qed.

Lemma ext_P_jm (P : JD_P) {x y} (f : x ~> M (N y)) :
  ext_P P f ≈ join_P P _ ∘ mapc f.
Proof. unfold ext_P. unfold pext_P. unfold join_P.  apply ext_o. Qed.

Definition ext_P_jm' (P : JD_P) {x y} (f : x ~> M (N y)) :
  ext_P P f ≈ join_P P _ ∘ mapc f := ext_o M3 _ _.

Print Implicit JD_P.
Print Implicit P4.
Print Implicit pext_P.
Print Implicit ret3.
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

Program Definition JD_Pext_P (Pext : JD_Pext) : JD_P :=
  {| prod := fun x => pext Pext id |}.
Next Obligation. rewrite <- Pext1.  rewrite <- pext_o.
 pose pext_respects.  rewrite id_left.  reflexivity. Qed.
Next Obligation.  apply Pext2. Qed.
Next Obligation. rewrite <- pext_o. pose pext_respects.  
  rewrite id_left.  apply Pext3. Qed.
Next Obligation.  rewrite <- pext_o. pose pext_respects.  
  rewrite id_left.  apply Pext4. Qed.

(* P1 to P4 give monad in Kleisli category of M *)
Program Definition JD_P_NK (P : JD_P) : @Monad3 (@Kleisli_from_3 C M M3) N :=
  {| ret3 := fun x : obj[C] => ret3 M3 ∘ @ret3 _ _ N3 x ;
    ext := fun (x y : obj[C]) (f : x ~> M (N y)) => pext_P P f |}.
Next Obligation. proper. apply pext_P_respects.  rewrite X. reflexivity. Qed.
Next Obligation. rewrite comp_assoc.  rewrite m_id_r.
unfold pext_P. rewrite <- comp_assoc.  rewrite <- (fmap_ret3 N3).
rewrite comp_assoc.  rewrite P2.  apply id_left. Qed.
Next Obligation. apply P3. Qed.
Next Obligation.  pose (map3_respects N3).  unfold pext_P. rewrite !ext_o.
rewrite !map3_comp.  rewrite !comp_assoc.  rewrite P4.  apply comp_o_r.
rewrite <- !comp_assoc.  apply comp_o_l.  symmetry.  apply P1. Qed.

Check JD_P_NK_obligation_1.
Check JD_P_NK_obligation_2.
Check JD_P_NK_obligation_3.
Check JD_P_NK_obligation_4.

(* Pext1 to Pext4 give monad in Kleisli category of M *)
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

Lemma pext_ext (Pext : JD_Pext) [x y z] 
  (g : y ~{ C }~> M (N z)) (f : x ~{ C }~> M (N y)) :
pext Pext (ext M3 (pext Pext g) ∘ f) ≈ ext M3 (pext Pext g) ∘ pext Pext f.
Proof. symmetry. apply JD_Pext_NK_obligation_4. Qed.

(* pext is a functor from Kleisli category of N in the Kleisli category of M
  to the Kleisli category of M *)
Definition pext_functor' (Pext : JD_Pext) :=
  @ext_functor (Kleisli_from_3 M3) N (JD_Pext_NK Pext) :
  @Functor (Kleisli_from_3 (JD_Pext_NK Pext)) (Kleisli_from_3 M3). 

Print Implicit fmap.
Print Implicit ret3.
Print Implicit compose.
Print Implicit id.
Print Implicit join3.
Print Implicit map3.

Check jed_monad.Monad_from_3_obligation_1.
Check jed_monad.Monad_from_3_obligation_2.
Check jed_monad.Monad_from_3_obligation_3.

Check jed_monad.Functor_from_3_obligation_3.
Check JD_P_Pext_obligation_6.

Print Implicit ret3.
Print Implicit join3.
Print Implicit pext_P.
Print Implicit ext.

(* Jones & Duponcheel, s3.4 *)
Record JD_S : Type := 
  { swap : ∀ x : obj[C], N (M x) ~{ C }~> M (N x) ;
    S1 : ∀ x y (f : x ~{ C }~> y), 
      swap y ∘ map3 N3 (map3 M3 f) ≈ mapc f ∘ swap x ;
    S2 : ∀ x, swap x ∘ ret3 N3 ≈ map3 M3 (ret3 N3) ;
    S3 : ∀ x, swap x ∘ map3 N3 (ret3 M3) ≈ ret3 M3 ;
    S4 : ∀ x, map3 M3 (join3 N3) ∘ swap (N x) ∘ map3 N3 (ext M3 (swap x)) ≈
      ext M3 (swap x) ∘ map3 M3 (join3 N3) ∘ swap (N (M x)) }.

(* defining prod and drop using swap, J&D also use these to state S4 *)
Definition prod_S (S : JD_S) x := map3 M3 (join3 N3) ∘ swap S (N x).
Definition dorp_S (S : JD_S) x := ext M3 (swap S x).

(* Jones & Duponcheel, s3.3 *)
Record JD_D : Type := 
  { dorp : ∀ x : obj[C], M (N (M x)) ~{ C }~> M (N x) ;
    D1 : ∀ x y (f : x ~{ C }~> y), 
      dorp y ∘ mapc (map3 M3 f) ≈ mapc f ∘ dorp x ;
    D2 : ∀ x, dorp x ∘ retc (M x) ≈ map3 M3 (ret3 N3) ;
    D3 : ∀ x, dorp x ∘ mapc (ret3 M3) ≈ id ;
    D4 : ∀ x, dorp x ∘ map3 M3 (join3 N3) ∘ dorp (N (M x)) ≈
      map3 M3 (join3 N3) ∘ dorp (N x) ∘ mapc (dorp x) }.

(* defining join using dorp, J&D also use this to state D4 *)
Definition join_D (D : JD_D) x := map3 M3 (join3 N3) ∘ dorp D (N x).
Definition ext_D (D : JD_D) {x y} (f : x ~> M (N y)) := join_D D y ∘ mapc f.
Definition swap_D (D : JD_D) x := dorp D x ∘ ret3 M3.

Lemma ext_D_respects (D : JD_D) (x y : obj[C]) :
  Proper (equiv ==> equiv) (@ext_D D x y).
Proof. proper. unfold ext_D.  apply comp_o_l.
apply map3_respects. apply map3_respects. apply X. Qed.

Print Implicit ret3.
Print Implicit join_P.

(* this is equivalent to J(2) in that it says mapM joinN is ext _ *)
Lemma D_mapM_joinN (D : JD_D) (x : obj[C]) : 
  ext_D D (@ret3 C M M3 (N x)) ≈ map3 M3 (join3 N3).
Proof. unfold ext_D. unfold join_D. rewrite <- comp_assoc.
rewrite D3. apply id_right. Qed.

Lemma D_ext_mapM_unitN (D : JD_D) x : ext_D D (map3 M3 (ret3 N3)) ≈ dorp D x.
Proof. unfold ext_D. unfold join_D. rewrite <- comp_assoc.
rewrite D1. rewrite comp_assoc. unfold mapc.
rewrite <- map3_comp. pose (map3_respects M3). rewrite join_fmap_ret3.
rewrite map3_id.  apply id_left. Qed.

Print Implicit join3.
Print Implicit ret3.
Print Implicit pext_P.
Print Implicit dorp_S.
Print Implicit swap_D.
Print Implicit swap.
Print Implicit ext_ext.

(* round-trip lemma for prod -> swap -> prod, condition
  related to J(2) but not involving compound monad *)
Lemma p_s_p' (P : JD_P)
  (j2p : forall y, @pext_P P _ y (ret3 M3) ≈ ret3 M3 ∘ join3 N3) x :
  map3 M3 (join3 N3) ∘ (pext_P P (map3 M3 (ret3 N3))) ≈ prod P x.
Proof. unfold map3.  pose (ext_respects M3).  rewrite <- j2p.
fold (map3 M3 (@ret3 _ _ N3 (N x))).
(* example of using monad results for monad in Kleisli category *)
pose (m_assoc (JD_P_NK P)).  simpl in e.  rewrite e.
pose (pext_P_respects).  rewrite <- ext_o. 
(* example of using Pext conditions given assumptions P(1) to P(4) *)
rewrite (Pext2 (JD_P_Pext P)).  rewrite m_id_l.
rewrite prod_pext_id. reflexivity. Qed.

(* reverse construction, swap from prod *)
(* TO LOOK AT - why do we need J(2) condition, paper says not *)
Program Definition P_to_S (P : JD_P) 
  (j2p : forall x, @pext_P P _ x (ret3 M3) ≈ ret3 M3 ∘ join3 N3) :=
  {| swap := swap_P P |} : JD_S.
Next Obligation. unfold swap_P. unfold pext_P.
rewrite comp_assoc. rewrite <- P1. 
rewrite <- !comp_assoc.  apply comp_o_l.
pose (map3_respects N3). unfold mapc.  rewrite <- !map3_comp.
apply map3_respects. apply map3_respects. apply fmap_ret3. Qed.
Next Obligation. unfold swap_P. unfold pext_P.
rewrite <- comp_assoc.  rewrite <- fmap_ret3.
rewrite comp_assoc.  rewrite P2.  apply id_left. Qed.
Next Obligation. unfold swap_P. unfold pext_P.
rewrite <- comp_assoc. rewrite <- map3_comp.
pose (map3_respects N3).  rewrite <- fmap_ret3. apply P3. Qed.
Next Obligation. unfold swap_P.
rewrite (p_s_p' P j2p).  rewrite <- comp_assoc.  rewrite (p_s_p' P j2p).
(* example of using monad results for monad in Kleisli category *)
pose (m_assoc (JD_P_NK P)).  simpl in e.
rewrite (prod_pext_id P (M x)).  rewrite e.
pose pext_P_respects.  rewrite id_right. reflexivity. Qed.

(* reverse construction, swap from dorp,
  using a version of J(1) which doesn't involve the compound monad *)
(* TO LOOK AT - why do we need J(1) condition, paper says not *)
Program Definition D_to_S (D : JD_D) (j1d : forall x, J1g M3 (dorp D x)) := 
  {| swap := swap_D D |} : JD_S.
Next Obligation. unfold swap_D.  rewrite comp_assoc.
rewrite <- D1. rewrite <- !comp_assoc. apply comp_o_l. apply fmap_ret3. Qed.
Next Obligation. unfold swap_D.  rewrite <- comp_assoc. apply D2. Qed.
Next Obligation. unfold swap_D.  rewrite <- comp_assoc.
rewrite fmap_ret3. rewrite comp_assoc. rewrite D3. apply id_left. Qed.
Next Obligation. unfold swap_D.  rewrite <- !comp_assoc.  rewrite fmap_ret3.
unfold J1g in j1d.  pose (map3_respects M3).  pose (map3_respects N3).
rewrite <- (J1g_char _ _ (j1d x)).
rewrite X. rewrite !comp_assoc. rewrite <- D4. reflexivity. Qed.

(* obtaining dorp or prod from swap *)
(* Jones & Duponcheel, Figure 6 *)
Program Definition S_to_D (S : JD_S) := {| dorp := dorp_S S |} : JD_D.
Next Obligation. unfold dorp_S. unfold mapc.
rewrite <- ext_o. pose (ext_respects M3). rewrite S1.
unfold mapc. unfold map3. symmetry. apply m_assoc. Qed.
Next Obligation. unfold dorp_S. unfold retc. rewrite comp_assoc.
rewrite m_id_r. apply S2. Qed.
Next Obligation. unfold dorp_S. unfold mapc.
rewrite <- ext_o. pose (ext_respects M3). rewrite S3. apply m_id_l. Qed.
Next Obligation. unfold dorp_S. pose (S4 S x).  apply (ext_respects M3) in e.
pose (ext_respects M3).  rewrite <- !comp_assoc in e.
rewrite <- m_assoc in e.  rewrite !ext_map_o in e.  rewrite !comp_assoc in e.
rewrite <- e.  rewrite ext_o.  apply comp_assoc. Qed.

(* Jones & Duponcheel, Figure 3 *)
Program Definition P_to_7 (P : JD_P) := {| ret := retc ; join := join_P P |} : 
  Monad (Compose (Functor_from_3 M3) (Functor_from_3 N3)).
Next Obligation.  apply premonad_comp. Qed.
Next Obligation. unfold join_P.  rewrite <- ext_o.
rewrite m_assoc.  apply ext_respects.  apply P4. Qed.
Next Obligation. unfold join_P.  rewrite <- ext_o.
pose (ext_respects M3).  rewrite P3. apply m_id_l.  Qed.
Next Obligation. unfold join_P. unfold retc.  rewrite comp_assoc.
rewrite m_id_r. apply P2. Qed.
Next Obligation. unfold join_P.  rewrite <- ext_o.  pose (ext_respects M3).   
fold (mapc f). rewrite (P1 P).  apply ext_map_o. Qed.

(* extraordinary difficulty equating MNf with 
(Compose (Functor_from_3 M3) (Functor_from_3 N3)) ;
  for some reason Print MNf shows MNo and mapc *)
Program Definition P_to_7' (P : JD_P) := {| ret := retc ; join := join_P P |} : 
  Monad MNf.
Next Obligation.  apply premonad_comp. Qed.
Next Obligation. unfold join_P.  unfold MNo. unfold mapc.
rewrite <- (ext_o M3).  rewrite m_assoc.
apply ext_respects.  apply P4. Qed.
Next Obligation. unfold join_P. unfold MNo. unfold mapc. rewrite <- ext_o.
pose (ext_respects M3).  rewrite P3. apply m_id_l.  Qed.
Next Obligation. unfold join_P. unfold retc.  rewrite comp_assoc.
unfold MNo. rewrite m_id_r. apply P2. Qed.
Next Obligation. unfold join_P. unfold MNo. unfold mapc.
rewrite <- ext_o.  pose (ext_respects M3).   
fold (mapc f). rewrite (P1 P).  apply ext_map_o. Qed.

Print Implicit Functor_from_3.
Print Implicit Compose.
Print Implicit D3.
Print Implicit comp_o_r.

(* tried this, seemed as though it might be easier, but seems not
Program Definition D_to_3 (D : JD_D) : @Monad3 C (Basics.compose M N) :=
  {| ret3 := retc ; ext := fun x y => ext_D D |}.
  *)

(* Jones & Duponcheel, Figure 4 *)
Program Definition D_to_7 (D : JD_D) := {| ret := retc ; join := join_D D |} : 
  Monad (Compose (Functor_from_3 M3) (Functor_from_3 N3)).
Next Obligation.  apply premonad_comp. Qed.
Next Obligation.  unfold join_D. rewrite <- !comp_assoc.
pose (D4 D (N x)). rewrite <- !comp_assoc in e. rewrite e.
pose (map3_respects M3).  rewrite !map3_comp.
rewrite !comp_assoc. apply comp_o_r.
rewrite <- comp_assoc. pose (D1 D).
unfold mapc in e0.  rewrite e0.
rewrite comp_assoc.  apply comp_o_r.
rewrite <- !map3_comp.  apply map3_respects.
apply join_fmap_join3. Qed.
Next Obligation.  unfold retc. pose (map3_respects M3). rewrite !map3_comp.
rewrite comp_assoc. pose D_mapM_joinN. unfold ext_D in e. rewrite e.
rewrite <- map3_comp.  rewrite (join_fmap_ret3 N3).  apply map3_id. Qed.
Next Obligation.  unfold join_D. rewrite <- comp_assoc.
rewrite D2. rewrite <- map3_comp.
pose (map3_respects M3).  rewrite (join_ret3 N3).  apply map3_id. Qed.
Next Obligation.  unfold join_D. rewrite <- comp_assoc.
rewrite (D1 D _ _ (map3 N3 f)).
rewrite !comp_assoc. apply comp_o_r.
unfold mapc. rewrite <- !map3_comp.
apply (map3_respects M3).  apply join_fmap_fmap3. Qed.

(* compound monad from D satisfies J2, noting J2 can be expressed using J1g *)
Lemma D_J2 (D : JD_D) x : 
  J1g (Monad3_from_Monad (D_to_7 D)) (map3 M3 (@join3 _ _ N3 x)).
Proof. unfold J1g. simpl. unfold extm. simpl. unfold join_D.
pose (map3_respects M3). rewrite !map3_id. rewrite id_right.
rewrite <- comp_assoc.  pose D1. unfold mapc in e. rewrite e.
rewrite !comp_assoc.  apply comp_o_r. rewrite <- !map3_comp.
apply map3_respects. apply join_fmap_join3. Qed.

(* equivalences of J(2) - equiv to conclusion of D_mapM_joinN *)
Lemma J2_mj_eqv (MN : @Monad C MNf) 
  (retc_eq : forall x, @ret _ _ MN x ≈ retc x) y :
  iffT (J1g (Monad3_from_Monad MN) (map3 M3 (@join3 _ _ N3 y)))
    (extm MN (@ret3 _ _ M3 (N y)) ≈ map3 M3 (join3 N3)).
Proof. split.
- intro.  rewrite (J1g_char _ _ X). simpl.
apply (extm_respects MN).  rewrite retc_eq.  unfold retc.
rewrite comp_assoc.  rewrite <- fmap_ret3.  rewrite <- comp_assoc.
rewrite join_ret3.  rewrite id_right.  reflexivity.
- intro.  unfold J1g. simpl.  pose (extm_respects MN).
rewrite <- X.  apply (ext_ext (Monad3_from_Monad MN)). Qed.

Print Implicit
Monad3_from_Monad.

Check D_to_7_obligation_3.

(* Jones & Duponcheel, Figure 5 *)
Program Definition S_to_P (S : JD_S) := {| prod := prod_S S |} : JD_P.
Next Obligation. unfold prod_S. unfold mapc.
rewrite <- !comp_assoc. rewrite S1. 
rewrite !comp_assoc. apply comp_o_r.
unfold mapc. rewrite <- !map3_comp.  apply map3_respects.
apply join_fmap_fmap3. Qed.
Next Obligation. unfold prod_S. rewrite <- comp_assoc.
rewrite S2. rewrite <- map3_comp.
unfold join3.  pose (map3_respects M3). rewrite m_id_r.
apply map3_id. Qed.
Next Obligation. unfold prod_S. unfold retc.  rewrite map3_comp.
pose (@comp_o_r _ _ _ _ _ (S3 S (N x))).  pose (e _ (map3 N3 (ret3 N3))).
rewrite <- comp_assoc.  rewrite <- comp_assoc in e0.  rewrite e0.
rewrite comp_assoc.  rewrite <- (fmap_ret3 M3).  rewrite <- comp_assoc.
rewrite (join_fmap_ret3 N3).  apply id_right. Qed.
Next Obligation. unfold prod_S. 
(* why doesn't rewrite ext_map_o work here ?? *)
pose (ext_respects M3).  pose (map3_respects M3).
pose (ext_map_o M3 (swap S (N x)) (join3 N3)).
pose (@comp_o_r _ _ _ _ _ e _ (map3 M3 (join3 N3) ∘ swap S (N (M (N x))))).
rewrite e0.  rewrite <- !comp_assoc.  pose (S4 S (N x)).
rewrite <- !comp_assoc in e1.  rewrite <- e1.
pose (map3_respects N3).  rewrite (ext_map_o M3).
rewrite map3_comp.  rewrite !comp_assoc.  apply comp_o_r.
rewrite <- !comp_assoc.  rewrite S1.
rewrite !comp_assoc.  apply comp_o_r.
unfold mapc.  rewrite <- !map3_comp.  apply map3_respects.
apply (join_fmap_join3 N3). Qed.

(* from swap, defining join/ext via dorp or via prod is the same *)
Lemma join_SDP_eq (S : JD_S) x : join_P (S_to_P S) x ≈ join_D (S_to_D S) x.
Proof. unfold join_P. unfold join_D. simpl.
unfold prod_S. unfold dorp_S. apply ext_map_o. Qed.

Lemma ext_SDP_eq (S : JD_S) {x y} (f : x ~> M (N y)) :
  ext_P (S_to_P S) f ≈ ext_D (S_to_D S) f.
Proof. unfold ext_P. unfold ext_D. simpl.
unfold pext_P. unfold join_D. simpl. unfold prod_S. unfold dorp_S.
pose (ext_respects M3).  rewrite <- comp_assoc.
rewrite ext_map_o.  rewrite ext_o.  apply comp_assoc.  Qed.

(* versions of D_mapM_joinN and D_ext_mapM_unitN from swap *)
Lemma S_unitM_joinN (S : JD_S) (x : obj[C]) : 
  pext_P (S_to_P S) (@ret3 C M M3 (N x)) ≈ ret3 M3 ∘ join3 N3.
Proof. unfold pext_P. simpl. unfold prod_S. rewrite <- comp_assoc.
rewrite S3. symmetry.  apply fmap_ret3. Qed.

Lemma S_pext_mapM_unitN (S : JD_S) x :
  pext_P (S_to_P S) (map3 M3 (ret3 N3)) ≈ swap S x.
Proof. unfold pext_P. simpl. unfold prod_S. rewrite <- comp_assoc.
rewrite S1. rewrite comp_assoc. unfold mapc.
rewrite <- map3_comp. pose (map3_respects M3). rewrite join_fmap_ret3.
rewrite map3_id.  apply id_left. Qed.

(* NB this is expressed using only pext, does it require the swap rules? 
  probably yes, since the prod construction doesn't involve N being a monad *)
Lemma S_pext_pext (S : JD_S) [x y] (f : x ~{ C }~> M (N y)) :
  pext_P (S_to_P S) (pext_P (S_to_P S) f) ≈ pext_P (S_to_P S) f ∘ join3 N3.
Proof.  pose (JD_P_NK (S_to_P S)) as K3.
pose (ext_ext K3 f) as ee. simpl in ee. rewrite ee.
rewrite (S_unitM_joinN S). rewrite comp_assoc. 
apply comp_o_r. apply m_id_r. Qed.

Lemma pext_swap (S : JD_S) x :
  pext_P (S_to_P S) (swap S x) ≈ swap S x ∘ join3 N3.
Proof. pose pext_P_respects. rewrite <- !S_pext_mapM_unitN.
apply S_pext_pext. Qed.

Lemma pext_extM (S : JD_S) [x y] (f : x ~{ C }~> M (N y)) :
  pext_P (S_to_P S) (ext M3 f) ≈ ext M3 (pext_P (S_to_P S) f) ∘ swap S x.
Proof. rewrite <- S_pext_mapM_unitN.
pose (JD_P_NK (S_to_P S)) as K3.
pose (m_assoc K3) as ma. simpl in ma.  rewrite ma.
pose pext_P_respects.  pose (ext_respects M3).  rewrite <- (ext_o M3).
rewrite (Pext2 (JD_P_Pext (S_to_P S))).  reflexivity. Qed.

Print Implicit
ret3.

Lemma dorp_swap (S : JD_S) x :
  dorp (S_to_D S) x ∘ swap S _ ≈ swap S x ∘ map3 N3 (join3 M3).
Proof. simpl. unfold dorp_S.  pose (ext_respects M3).
rewrite <- S_pext_mapM_unitN.  rewrite <- pext_extM.
pose (pext_o (JD_P_Pext (S_to_P S))) as po.  rewrite <- po.
pose pext_respects.  pose pext_P_respects.
rewrite <- join_fmap_fmap3.  rewrite ext_jm. reflexivity. Qed.

(* NB this is expressed using only dorp, does it require the swap rules? 
  probably yes, since the dorp construction doesn't involve M being a monad *)
Lemma dorp_dorp (S : JD_S) x : 
  dorp (S_to_D S) x ∘ dorp (S_to_D S) _ ≈ dorp (S_to_D S) x ∘ mapc (join3 M3).
Proof. simpl. unfold dorp_S. rewrite m_assoc. pose (ext_respects M3).
  pose (dorp_swap S x) as ds. simpl in ds.
  unfold dorp_S in ds.  rewrite ds.  apply ext_o. Qed.

Program Definition dorp_functor (S : JD_S) : @Functor (Kleisli_from_3 M3) C :=
  {| fobj := MNo ; fmap := fun x y f => dorp (S_to_D S) y ∘ mapc f |}.
Next Obligation. proper. apply comp_o_l. exact (mapc_respects _ _ X). Qed.
Next Obligation. apply (D3 (S_to_D S)). Qed.
Next Obligation.  rewrite mapc_comp.  rewrite !comp_assoc.  apply comp_o_r.
rewrite <- comp_assoc.  rewrite <- (D1 (S_to_D S)).  rewrite comp_assoc.
pose (dorp_dorp S z) as dd. simpl in dd.  rewrite dd.
rewrite <- comp_assoc.  rewrite <- mapc_comp.  apply comp_o_l.
apply mapc_respects.  apply ext_jm. Qed.

Print Implicit MNo.
Print Implicit JD_P_NK.

Definition pext_map_functor (P : JD_P) :
  @Functor (Kleisli_from_3 M3) (Kleisli_from_3 M3) :=
  Functor_from_3 (JD_P_NK P).

Program Definition swap_functor (S : JD_S) : 
  @Functor (Kleisli_from_3 M3) (Kleisli_from_3 M3) :=
  {| fobj := N ; fmap := fun x y f => swap S y ∘ map3 N3 f |}.
Next Obligation. proper. apply comp_o_l. apply map3_respects. exact X. Qed.
Next Obligation. apply S3. Qed.
Next Obligation.  (* trying to use pext_map_functor looks too complicated *)
rewrite map3_comp.  rewrite !comp_assoc.  apply comp_o_r.
rewrite ext_o.  rewrite <- comp_assoc.
fold (mapc f).  rewrite <- (S1 S).  rewrite comp_assoc.
pose (dorp_swap S z) as ds. simpl in ds.  rewrite ds.
rewrite <- comp_assoc.  rewrite <- map3_comp.  apply comp_o_l.
apply map3_respects.  apply ext_jm. Qed.

(* this functor is the map of the monad N in the Kleisli category of M *)
Lemma pext_map_swap_fun (S : JD_S) :
  swap_functor S ≈ pext_map_functor (S_to_P S).
Proof. simpl. (* getting right types in the following is difficult! *)
exists (fun (x : obj[C]) => @Isomorphism.iso_id (Kleisli_from_3 M3) (N x)).
intros. simpl. unfold pext_P. simpl. unfold prod_S.
rewrite m_id_r.  pose (map3_respects N3). rewrite ext_o.
rewrite !m_id_l, !id_left.
rewrite map3_comp. rewrite !comp_assoc. apply comp_o_r.
rewrite <- comp_assoc. rewrite (S1 S). rewrite comp_assoc.
unfold mapc. rewrite <- map3_comp. pose (map3_respects M3).
rewrite join_fmap_ret3. rewrite map3_id, id_left. reflexivity. Qed.

(* round-trip lemmas *)
(* swap_D and dorp_S are inverses one way - S_to_D uses dorp_S *)
Lemma s_d_s (S : JD_S) x : swap_D (S_to_D S) x ≈ swap S x.
Proof. unfold swap_D. simpl. unfold dorp_S. apply m_id_r. Qed.

(* the other way requires a J1 condition *)
Lemma d_s_d (D : JD_D) j1d x : dorp_S (D_to_S D j1d) x ≈ dorp D x.
Proof. unfold dorp_S. simpl. unfold swap_D.
unfold J1g in j1d. rewrite ext_o. rewrite j1d.
rewrite <- comp_assoc. rewrite join_fmap_ret3. apply id_right. Qed.

Definition s_p_s' (S : JD_S) x : swap_P (S_to_P S) x ≈ swap S x :=
  S_pext_mapM_unitN S x.

Definition p_s_p P j2p x : prod_S (P_to_S P j2p) x ≈ prod P x :=
  (p_s_p' P j2p x).

(* 
Set Printing Coercions.
Set Printing Implicit.
Set Printing Notations.
Unset Printing Coercions.
Unset Printing Implicit.
Unset Printing Notations.
*)

Print Implicit ret3.
Print Implicit m_assoc.
Print Implicit
Monad.

(* for converse results, given a compound monad MN, we need the assumptions
  that MN has map and unit functions as mapc and retc,
  assumption stated bottom of pg 12 of Jones & Duponcheel *)
(* note the following says nothing about action of map of MN3 on arrows,
  we need something like mapc, and also unitMN being unitM o unitN
Definition pext_MN (MN3 : @Monad3 C MN) {x y} (f : x ~> MN y) :=
  ext MN3 f ∘ ret3 M3. 
Definition dorp_MN (MN3 : @Monad3 C MN) x :=
  ext MN3 (map3 M3 (@ret3 _ _ N3 x)).
*)
Definition pext_MN (MN : @Monad C MNf) [x y] (f : x ~> MNo y) :=
  extm MN f ∘ ret3 M3. 
Definition dorp_MN (MN : @Monad C MNf) x :=
  extm MN (map3 M3 (@ret3 _ _ N3 x)).

(* note equivalences of conditions variously labelled j2p, j2e *)
Lemma j2p_e (P : JD_P) x
  (j2p : @pext_P P _ x (ret3 M3) ≈ ret3 M3 ∘ join3 N3) :
  ext M3 (@pext_P P _ x (ret3 M3)) ≈ map3 M3 (@join3 _ _ N3 x).
Proof. pose (ext_respects M3). rewrite j2p. reflexivity. Qed.

Lemma j2e_p (MN : @Monad C MNf) x
  (j2e : extm MN (ret3 M3) ≈ map3 M3 (@join3 _ _ N3 x)) :
  @pext_MN MN _ x (ret3 M3) ≈ ret3 M3 ∘ join3 N3.
Proof. unfold pext_MN. rewrite j2e. symmetry. simpl. apply fmap_ret3. Qed.

(* round-trip lemmas, compound monad <-> dorp/prod *)

Print join_P.
Print join_D.
Print ext_P.
Print ext_D.

Print Implicit
extm.

(* note - to match types often need these: unfold MNo. unfold mapc. 
  apparently somehow these come from the functor MNf (do Print MNf.)
  note - Print MNf. seems to produce variable results *)
Lemma p_e_p (P : JD_P) [x y] (f : x ~{ C }~> M (N y)) : 
  pext_MN (P_to_7' P) f ≈ pext_P P f.
Proof. unfold pext_MN. unfold extm. simpl. unfold join_P.
unfold MNo. unfold mapc.  rewrite <- (ext_o M3).  apply m_id_r. Qed.

Definition d_e_d (D : JD_D) x : dorp_MN (D_to_7 D) x ≈ dorp D x :=
  D_ext_mapM_unitN D x.

(* TO LOOK AT - why do we need J(1) condition, paper says not *)
Program Definition MN_to_Pext (MN : @Monad C MNf) 
  (j1e : forall x y f, J1g M3 (@extm _ _ MN x y f)) 
  (retc_eq : forall x, @ret _ _ MN x ≈ retc x) : JD_Pext :=
  {| pext := @pext_MN MN |}.
Next Obligation. proper. unfold pext_MN. pose (extm_respects MN).
rewrite X. reflexivity. Qed.
Next Obligation. unfold pext_MN. unfold extm.  rewrite fmap_comp.
rewrite <- !comp_assoc. apply comp_o_l. apply comp_o_l.
simpl. unfold mapc. symmetry. apply (fmap_ret3 M3). Qed.
Next Obligation. unfold pext_MN. unfold extm. simpl.
pose (map3_respects M3).  rewrite !map3_id. rewrite id_right.
rewrite comp_assoc.  apply comp_o_r. apply (@join_fmap_fmap _ _ MN). Qed.
Next Obligation. unfold pext_MN. 
pose (m_id_r (Monad3_from_Monad MN) _ _ f).  simpl in e.
rewrite retc_eq in e. rewrite <- comp_assoc. exact e. Qed.
Next Obligation. unfold pext_MN.
pose (extm_respects MN).  rewrite <- retc_eq.
rewrite (m_id_l (Monad3_from_Monad MN)).  apply id_left. Qed.
Next Obligation. unfold pext_MN.  pose (extm_respects MN).
rewrite <- !(J1g_char M3 _ (j1e _ _ f)).
rewrite (ext_ext (Monad3_from_Monad MN) f).  simpl.
apply comp_assoc_sym. Qed.

Print Implicit
Build_Monad.

Lemma e_p_e (MN : @Monad C MNf) j1e retc_eq y :
  join_P (JD_Pext_P (MN_to_Pext MN j1e retc_eq)) y ≈ @join _ _ MN y.
Proof. unfold join_P. simpl. unfold pext_MN.
rewrite <- (J1g_char M3 _ (j1e _ _ id[MNo y])).
unfold extm.  rewrite fmap_id.  apply id_right. Qed.

Lemma j2e_mjd (MN : @Monad C MNf) 
  (j2e : forall x, extm MN (ret3 M3) ≈ map3 M3 (@join3 _ _ N3 x)) y :
  map3 M3 (join3 N3) ∘ dorp_MN MN (N y) ≈ extm MN id.
Proof. unfold dorp_MN. rewrite <- !j2e.
pose (m_assoc (Monad3_from_Monad MN)).
simpl in e. simpl. unfold MNo. unfold MNo in e. rewrite e. (* why ?? *)
apply (extm_respects MN). rewrite j2e.  rewrite <- (map3_comp M3).
pose (map3_respects M3). rewrite join_ret3. apply (map3_id M3). Qed.

(* 
Set Printing Coercions.
Set Printing Implicit.
Set Printing Notations.
Unset Printing Coercions.
Unset Printing Implicit.
Unset Printing Notations.
*)

(* TO LOOK AT - why do we need J(2) condition, paper says not *)
(* note - previously Print MNf gave functor referring to MNo, mapc,
  now gives it as Functor_from_3 M3 ◯ Functor_from_3 N3 ;
  need to change the proof accordingly *)  
Program Definition MN_to_D (MN : @Monad C MNf) 
  (j2e : forall x, extm MN (ret3 M3) ≈ map3 M3 (@join3 _ _ N3 x)) 
  (retc_eq : forall x, @ret _ _ MN x ≈ retc x) : JD_D :=
  {| dorp := @dorp_MN MN |}.
Next Obligation. unfold dorp_MN. 
(* need these lines or following two depending on what Print MNf. gives 
  and similarly further down
pose (ext_o_m MN). simpl in e. unfold MNo in e. rewrite <- e.
pose (ext_map_o_m MN).  simpl in e0. unfold MNo in e0. rewrite <- e0.
*)
pose (ext_o_m MN). simpl in e. unfold mapc. rewrite <- e.
pose (ext_map_o_m MN).  simpl in e0. rewrite <- e0.
apply (extm_respects MN). unfold mapc. 
rewrite <- !(map3_comp M3).
apply (map3_respects M3).  apply fmap_ret3. Qed.

Next Obligation. unfold dorp_MN. 
rewrite <- retc_eq. apply (m_id_r (Monad3_from_Monad MN)).  Qed.

Next Obligation. unfold dorp_MN. 
(* pose (ext_o_m MN). simpl in e. unfold MNo in e. rewrite <- e.  *)
pose (ext_o_m MN). simpl in e. unfold mapc. rewrite <- e.
pose (extm_respects MN).  rewrite <- (fmap_ret3 M3).
rewrite <- (retc_eq x).  apply (m_id_l (Monad3_from_Monad MN)).  Qed.

Next Obligation. unfold dorp_MN. 
rewrite (j2e_mjd MN j2e x).  rewrite <- comp_assoc.
rewrite (j2e_mjd MN j2e (M x)).
pose (m_assoc (Monad3_from_Monad MN)). simpl in e. unfold MNo in e.
rewrite e.
(* pose (ext_o_m MN). simpl in e0. unfold MNo in e0. rewrite <- e0.  *)
pose (ext_o_m MN). simpl in e0. unfold mapc. rewrite <- e0.
apply (extm_respects MN). rewrite id_left.  apply id_right. Qed.

Print Implicit fmap_ret3.
Print Implicit ret3.

Lemma e_d_e (MN : @Monad C MNf) j2e retc_eq y :
  join_D (MN_to_D MN j2e retc_eq) y ≈ @join _ _ MN y.
Proof. unfold join_D. simpl.  rewrite (j2e_mjd MN j2e y).
unfold extm. rewrite fmap_id. apply id_right. Qed.

(* defining swap from join/ext via dorp or via prod is the same *)
Lemma swap_DP_eq (MN : @Monad C MNf) j1e j2e retc_eq x : 
  swap_P (JD_Pext_P (MN_to_Pext MN j1e retc_eq)) x ≈ 
  swap_D (MN_to_D MN j2e retc_eq) x.
Proof. unfold swap_P. unfold swap_D. unfold pext_P. simpl.
unfold pext_MN. unfold dorp_MN. unfold extm. simpl.
pose (map3_respects M3). rewrite !map3_id. rewrite id_right.
rewrite <- !comp_assoc. apply comp_o_l. apply fmap_ret3. Qed.

End CMN. (* more to be done, but this lets the file compile *)

(* compound monad, monad in Kleisli category of another monad *)
(* this is the basis of the prod construction of Jones & Duponcheel *)

Program Definition MinK_comp {C M} (M3 : @Monad3 C M) {N} 
  (K3 : @Monad3 (@Kleisli_from_3 C M M3) N) : @Monad3 C MNo :=
  {| ret3 := @ret3 _ _ K3 ; ext := fun x y f => ext M3 (ext K3 f) |}.
Next Obligation.  proper. apply (ext_respects M3).
apply (ext_respects K3). apply X. Qed.
Next Obligation.  (* rewrite (m_id_r K3). or rewrite m_id_r. fail here *)
exact (m_id_r K3 _ _ f). Qed.
Next Obligation. pose (ext_respects M3). (* needed, including the M3 *)
rewrite (m_id_l K3). simpl. apply (m_id_l M3). Qed.
Next Obligation. rewrite (m_assoc M3 (N x) (N y) (N z)). 
apply (ext_respects M3).
(* apply setoid_trans. fails, why?? and rewrite (m_assoc K3). fails *)
apply (m_assoc K3 x y z g f). Qed.

Check MinK_comp.

Print Implicit join3.
Print Implicit ext_ext.

(* when we have a compound monad defined in this way, it satisfies J(1) *)
Lemma MinK_J1 {C M} (M3 : @Monad3 C M) {N} 
  (K3 : @Monad3 (@Kleisli_from_3 C M M3) N) x : 
  J1g M3 (@join3 _ _ (MinK_comp M3 K3) x).
Proof. simpl. unfold J1g.  apply (ext_ext M3). Qed.

(* the prod or pext construction gives an associativity result between 
  the composition in C and that in the Kleisli category of M *)
Lemma MinK_omo {C M} (M3 : @Monad3 C M) {N} 
  (K3 : @Monad3 (@Kleisli_from_3 C M M3) N) x y z w 
  (f : z ~{ C }~> M w) (g : y ~{ C }~> M z) (h : x ~{ C }~> y) : 
    @compose (@Kleisli_from_3 C M M3) _ _ _ f (@compose C _ _ _ g h) ≈
    @compose C _ _ _ (@compose (@Kleisli_from_3 C M M3) _ _ _ f g) h.
Proof. simpl. apply comp_assoc. Qed.

(* when we have a compound monad defined in this way, its map function
  is mapM o mapN, ie, mapc, but this depends on the monad
  in the Kleisli category being defined using pext satisfying JD_Pext,
  unlike the previous few results *)
Lemma MinK_mapc {C M N} M3 N3 (Pext : JD_Pext M3 N3) [x y] (f : x ~> y) :
  map3 (MinK_comp M3 (@JD_Pext_NK C M N M3 N3 Pext)) f ≈
  map3 M3 (map3 N3 f).
Proof. unfold map3. simpl. pose (ext_respects M3). rewrite pext_o.
rewrite Pext3. reflexivity. Qed.

(* pext is a functor from the Kleisli cat of MN to the Kleisli cat of M,
  see pext_functor' above *)
Program Definition pext_functor {C M N} M3 N3 (Pext : @JD_Pext C M N M3 N3) :=
  {| fobj := N ; fmap := @pext C M N M3 N3 Pext |} : 
  @Functor (Kleisli_from_3 (MinK_comp M3 (JD_Pext_NK M3 N3 Pext)))
  (Kleisli_from_3 M3).
Next Obligation. proper. apply pext_respects. exact X. Qed.
Next Obligation. apply Pext3. Qed.
Next Obligation.  symmetry.  apply (JD_Pext_NK_obligation_4 M3 N3 Pext). Qed.

Print Implicit JD_Pext_NK.
Print Implicit MinK_comp.
Print Implicit JD_Pext.

(* monad in Kleisli category of another monad, implies Pext rules *)
(* or does it?? maybe it requires the J1 condition
Program Definition MinK_Pext {C M N} (M3 : @Monad3 C M) (N3 : @Monad3 C N)
  (K3 : @Monad3 (@Kleisli_from_3 C M M3) N) : JD_Pext M3 N3 :=
  {| pext := fun x y (f : x ~> M (N y)) => ext K3 f |}.
Next Obligation.  proper.  apply (ext_respects K3). apply X. Qed.
Next Obligation.  rewrite !m_id_r. what to do now

Program Definition MinK_P {C M N} (M3 : @Monad3 C M) (N3 : @Monad3 C N)
  (K3 : @Monad3 (@Kleisli_from_3 C M M3) N) : JD_P M3 N3 :=
  {| prod := fun x => ext K3 (@id C (M (N x))) |}.
Next Obligation.  proper.  apply (ext_respects K3). apply X. Qed.
Next Obligation.  rewrite !m_id_r. what to do now
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
Lemma MinK_comp_adj {C M} (M3 : @Monad3 C M) {N} 
  (K3 : @Monad3 (@Kleisli_from_3 C M M3) N) : @Monad3 C (Basics.compose M N).
Proof.  pose (Adjunction_IffEq_comp (k_adj K3) (k_adj M3)).
exact (AIE_to_Monad3 a). Defined.
Check MinK_comp_adj.

(* this shows the type of ext, not how it is defined *)
Check (fun M3 K3 => ext (MinK_comp_adj M3 K3)). 
Check (fun M3 K3 => ext (MinK_comp M3 K3)). 

Print Implicit ext_D.
Print Implicit join3.
Print Implicit ret3.
Print Implicit TAlgebra.
Print Implicit JD_P_NK.

(** compound monads and algebras *)

(* prod is an N-algebra (assuming JD_S) *)
(* TODO - can this be a functor into the JEM category for N,
  and thereby give a compound monad (from two adjoint functors) ? *)
Program Definition prod_is_alg {C M N} M3 N3 (S : @JD_S C M N M3 N3) a :
  @TAlgebra C _ (Monad_from_3 N3) (M (N a)) :=
  {| t_alg := prod _ _ (S_to_P M3 N3 S) a ; 
    t_id := P2 _ _ (S_to_P M3 N3 S) a |}.
Next Obligation. pose (S_to_P M3 N3 S) as P.
pose (JD_P_NK M3 N3 P) as K3.
pose (ext_ext K3 (@id C (M (N a)))) as ee.  simpl in ee.
unfold pext_P in ee.  pose (map3_respects N3).  pose (ext_respects M3).
rewrite !map3_id, !id_right in ee.  simpl in ee.  rewrite ee.
pose (S_unitM_joinN M3 N3 S (M (N a))) as uj.
unfold pext_P in uj. simpl in uj.  rewrite uj.
rewrite comp_assoc.  apply comp_o_r.  apply m_id_r.  Qed.
    
Definition prod_is_ex_alg {C M N} M3 N3 S a : ∃ y, @TAlgebra C _ _ y :=
existT (@TAlgebra C _ _) (M (N a)) (prod_is_alg M3 N3 S a).

Program Definition prod_alg_arr {C M N} M3 N3 (S : @JD_S C M N M3 N3) x y 
  (arr : @hom C x y) :
  @TAlgebraHom C _ _ _ _ (prod_is_alg M3 N3 S x) (prod_is_alg M3 N3 S y) :=
  {| t_alg_hom := mapc M3 N3 arr |}.
Next Obligation. symmetry.  apply (P1 M3 N3 (S_to_P M3 N3 S)). Qed.

Program Definition prod_fun_to_JEM {C M N} M3 N3 (S : @JD_S C M N M3 N3) :
  @Functor C (JEM (Monad_from_3 N3)) :=
  {| fobj := prod_is_ex_alg M3 N3 S ; fmap := prod_alg_arr M3 N3 S |}.
Next Obligation.  proper. apply (mapc_respects M3 N3). exact X. Qed.
Next Obligation.  apply mapc_id. Qed.
Next Obligation.  apply mapc_comp. Qed.

(* analogy with join_to_alg doesn't seem to work
(* given a T-algebra, there is a T-Algebra arrow from the prod algebra to it *)
Program Definition prod_to_alg {C M N} M3 N3 (S : @JD_S C M N M3 N3) a
  (alg : @TAlgebra C _ _ a) :
  @TAlgebraHom C _ _ _ _ (prod_is_alg M3 N3 S a) alg :=
  {| t_alg_hom := t_alg |}.
Next Obligation. symmetry. apply t_action. Qed.

(* now to show these functors are adjoint *)
Program Definition prod_adj_EM {C M N} M3 N3 (S : @JD_S C M N M3 N3) :
  Adjunction_IffEq (prod_fun_to_JEM M3 N3 S) (fun_from_JEM _) :=
  {| unit' := @ret C M H ; ???
    counit' := fun alg => prod_to_alg H (projT1 alg) (projT2 alg) |}.
*)
Print Implicit 
Functor.

(* given an N-algebra f, mapM f o swap is an N-algebra (assuming JD_S) *)
Program Definition ms_alg {C M N} M3 N3 (S : @JD_S C M N M3 N3) a
  (alg : @TAlgebra C _ (Monad_from_3 N3) a) :
  @TAlgebra C _ (Monad_from_3 N3) (M a) :=
  {| t_alg := map3 M3 (@t_alg _ _ _ _ alg) ∘ swap M3 N3 S _ |}.
Next Obligation. rewrite <- comp_assoc. rewrite S2.
rewrite <- map3_comp. pose (map3_respects M3).
rewrite (@t_id _ _ _ _ alg). apply map3_id. Qed.
Next Obligation.  rewrite map3_comp.
pose (S1 M3 N3 S _ _ t_alg[alg]) as s1.  eapply comp_o_r in s1.
rewrite <- !comp_assoc in s1.  rewrite <- !comp_assoc.  rewrite s1.
rewrite !comp_assoc.  unfold mapc. rewrite <- map3_comp.
pose (@t_action _ _ _ _ alg). simpl in e.
pose (map3_respects M3). rewrite e.
rewrite map3_comp.  rewrite <- !comp_assoc.  apply comp_o_l.
simpl. rewrite <- pext_swap. unfold pext_P. simpl. 
unfold prod_S. apply comp_assoc. Qed.

(* TODO M is a monad in the category of N-algebras *)

(* TODO this one works assuming only JD_D (except that you need ms_alg) *)
Program Definition N_alghom_unitM {C M N} [M3 N3] (S : @JD_S C M N M3 N3) [a]
  (alg : @TAlgebra C _ (Monad_from_3 N3) a) :
  @TAlgebraHom C _ (Monad_from_3 N3) a (M a) alg (ms_alg _ _ S a alg) :=
  {| t_alg_hom := ret3 M3 |}.
Next Obligation.  rewrite <- comp_assoc. rewrite S3. apply fmap_ret3. Qed.

Program Definition N_alghom_joinM {C M N} [M3 N3] (S : @JD_S C M N M3 N3) [a]
  (alg : @TAlgebra C _ (Monad_from_3 N3) a) :
  @TAlgebraHom C _ (Monad_from_3 N3) (M (M a)) (M a)
    (ms_alg _ _ S _ (ms_alg _ _ S a alg)) (ms_alg _ _ S a alg) :=
  {| t_alg_hom := join3 M3 |}.
Next Obligation. rewrite map3_comp. rewrite !comp_assoc. 
rewrite join_fmap_fmap3. rewrite <- !comp_assoc. apply comp_o_l.
rewrite <- dorp_swap. unfold dorp_S.
rewrite comp_assoc.  rewrite <- ext_jm. reflexivity. Qed.

Program Definition N_alghom_mapM {C M N} [M3 N3] (S : @JD_S C M N M3 N3) [a b]
  (alga : @TAlgebra C _ (Monad_from_3 N3) a)
  (algb : @TAlgebra C _ (Monad_from_3 N3) b)
  (fah : @TAlgebraHom C _ (Monad_from_3 N3) a b alga algb) :
  @TAlgebraHom C _ (Monad_from_3 N3) (M a) (M b)
    (ms_alg _ _ S a alga) (ms_alg _ _ S b algb) :=
  {| t_alg_hom := map3 M3 (@t_alg_hom _ _ _ _ _ _ _ fah) |}.
Next Obligation. rewrite <- comp_assoc. rewrite S1.
unfold mapc. rewrite !comp_assoc. apply comp_o_r.
rewrite <- !map3_comp. apply map3_respects.
exact (@t_alg_hom_commutes _ _ _ _ _ alga algb fah). Qed.

Print Implicit 
TAlgebraHom.