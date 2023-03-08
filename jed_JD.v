
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

(* TODO - show relationship to J(2) condition *)

Print Implicit join3.
Print Implicit ret3.
Print Implicit pext_P.
Print Implicit dorp_S.
Print Implicit swap_D.
Print Implicit swap.
Print Implicit ext_ext.

(* round-trip lemma for prod -> swap -> prod, condition
  related to J(2) but not involving compound monad *)
(* TODO show how this condition is related to J(2) *)
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
(* rewrite <- !ext_join_imp. fails *)
assert (forall x, ext M3 (dorp D x ∘ ret3 M3) ≈ dorp D x).
- intro.  rewrite ext_o. rewrite j1d. rewrite <- comp_assoc.
rewrite join_fmap_ret3. apply id_right.
- rewrite X. rewrite !comp_assoc. rewrite <- D4. reflexivity. Qed.

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

  (*

  @equiv _ (@homset C (M (N (M (N (M (N x)))))) (M (N x)))
    (@compose C (M (N (M (N (M (N x)))))) (M (N (M (N x))))
       (M (N x)) (@ext _ _ M3 (N (M (N x))) (N x) (prod P x))
       (@map3 C M M3 (N (M (N (M (N x))))) (N (M (N x)))
          (@map3 C N N3 (M (N (M (N x)))) (M (N x))
             (@ext _ _ M3 (N (M (N x))) (N x) (prod P x)))))
    (@compose C (M (N (M (N (M (N x)))))) (M (N (M (N x))))
       (M (N x)) (@ext _ _ M3 (N (M (N x))) (N x) (prod P x))
       (@ext _ _ M3 (N (M (N (M (N x))))) (N (M (N x))) (prod P (M (N x)))))

*)

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

(* TODO - show the compound monad satisfies J2 *)

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
Next Obligation. unfold prod_S. unfold retc.
rewrite map3_comp.
pose (@comp_o_r _ _ _ _ _ (S3 S (N x))).
pose (e _ (map3 N3 (ret3 N3))).
rewrite <- comp_assoc. 
rewrite <- comp_assoc in e0.  rewrite e0.
rewrite comp_assoc.  rewrite <- (fmap_ret3 M3).  rewrite <- comp_assoc.
rewrite (join_fmap_ret3 N3).  apply id_right. Qed.
Next Obligation. unfold prod_S. 
(* why doesn't rewrite ext_map_o work here ?? *)
pose (ext_respects M3).  pose (map3_respects M3).
pose (ext_map_o M3 (swap S (N x)) (join3 N3)).
pose (@comp_o_r _ _ _ _ _ e _ (map3 M3 (join3 N3) ∘ swap S (N (M (N x))))).
rewrite e0.
rewrite <- !comp_assoc.  pose (S4 S (N x)).
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

(* round-trip lemmas *)
(* swap_D and dorp_S are inverses one way - S_to_D uses dorp_S *)
Lemma s_d_s (S : JD_S) x : swap_D (S_to_D S) x ≈ swap S x.
Proof. unfold swap_D. simpl. unfold dorp_S. apply m_id_r. Qed.

(* the other way requires a J1 condition *)
Lemma d_s_d (D : JD_D) (j1d : forall y, J1g M3 (dorp D y)) x : 
  dorp_S (D_to_S D j1d) x ≈ dorp D x.
Proof. unfold dorp_S. simpl. unfold swap_D.
unfold J1g in j1d. rewrite ext_o. rewrite j1d.
rewrite <- comp_assoc. rewrite join_fmap_ret3. apply id_right. Qed.

Lemma s_p_s (S : JD_S) x : swap_P (S_to_P S) x ≈ swap S x.
Proof. unfold swap_P. unfold pext_P. simpl. unfold prod_S.
rewrite <- comp_assoc. rewrite S1.  unfold mapc.
rewrite comp_assoc.
rewrite <- map3_comp.
pose (map3_respects M3).  rewrite join_fmap_ret3. 
rewrite map3_id. apply id_left. Qed.

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

Print Implicit ext.
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

(* round-trip lemmas, compound monad <-> dorp/prod *)

Print join_P.
Print join_D.
Print ext_P.
Print ext_D.

Print Implicit
extm.

(* note - to match types often need these: unfold MNo. unfold mapc. 
  apparently somehow these come from the functor MNf (do Print MNf.) *)
Lemma p_e_p (P : JD_P) [x y] (f : x ~{ C }~> M (N y)) : 
  pext_MN (P_to_7' P) f ≈ pext_P P f.
Proof. unfold pext_MN. unfold extm. simpl. unfold join_P.
unfold MNo. unfold mapc.  rewrite <- (ext_o M3).  apply m_id_r. Qed.

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

Lemma e_p_e (MN : @Monad C MNf) 
  (j1e : forall x y f, J1g M3 (@extm _ _ MN x y f))
  (retc_eq : forall x, @ret _ _ MN x ≈ retc x) y :
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

(* TODO defining swap from join/ext via dorp or via prod is the same *)
(* TODO - roundtrip lemmas *)

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
  ext M3 (join3 (MinK_comp M3 K3)) ≈ @join3 _ _ (MinK_comp M3 K3) x ∘ join3 M3.
Proof. simpl. unfold MNo.  apply (ext_ext M3). Qed.

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
Lemma MinK_mapc {C M N} (M3 : @Monad3 C M) (N3 : @Monad3 C N)
  (Pext : JD_Pext M3 N3) x y (f : x ~> y) :
  map3 (MinK_comp (M3 : @Monad3 C M) (JD_Pext_NK M3 N3 Pext)) f ≈
  map3 M3 (map3 N3 f).
Proof. unfold map3. simpl. pose (ext_respects M3). rewrite pext_o.
rewrite Pext3. reflexivity. Qed.
  
Print Implicit map3.
Print Implicit JD_Pext_NK.
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

