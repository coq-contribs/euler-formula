(*==========================================================
============================================================
            TOPOLOGICAL FMAPS, QHMAPS, HMAPS -

       PROOFS OF THE GENUS THEOREM AND THE EULER RELATION 

                        PART 3:

  EQUIVALENCES, CHARACTERISTICS, GENUS, EULER_POINCARE, 
         CONSTRUCTIVE CONDITION OF PLANARITY 

              (J.-F. Dufourd - June 2006)

============================================================
==========================================================*)

Require Export Euler2.

(*==========================================================
           DART EQUIVALENCES IN QHMAPS
==========================================================*)

(* Face equivalence: *)

Definition eqf(m:fmap)(x y:dart):=
  expf m x y \/ expf m y x.

(* Reflexivity of eqf: *)

Lemma refl_eqf : forall (m:fmap)(x:dart),
  exd m x -> eqf m x x.
Proof.
intros.
unfold eqf in |- *.
assert (expf m x x).
 apply refl_expf.
   tauto.
 tauto.
Qed.

(* Symmetry of eqf: *)

Lemma symm_eqf : forall (m:fmap)(x y:dart),
  eqf m x y -> eqf m y x.
Proof.
unfold eqf in |- *.
intros.
tauto.
Qed.

(* Transitivity of eqf: *)

Lemma trans_eqf : forall (m:fmap),
  inv_qhmap m -> forall (x y z:dart),
  eqf m x y -> eqf m y z -> eqf m x z.
Proof.
unfold eqf in |- *.
intros.
elim H0.
 elim H1.
  left.
    apply trans_expf with y.
   tauto.
   tauto.
  intros.
    eapply diff2_expf.
   tauto.
   apply H3.
     tauto.
 elim H1.
  intros.
    eapply diff1_expf.
   tauto.
   apply H3; tauto.
     tauto.
  right.
    eapply trans_expf with y.
   tauto.
   tauto.
Qed.

(* Decidability of eqf: *)

Lemma eqf_dec : forall (m:fmap)(x y:dart),
  {eqf m x y} + {~eqf m x y}.
Proof.
unfold eqf in |- *.
intros m x y.
generalize (expf_dec m x y).
intro.
elim H.
 tauto.
 generalize (expf_dec m y x).
   intro.
   elim H0.
  tauto.
  tauto.
Qed.

(* Connectivity : Definition in Prop "a la" Warshall *)

Fixpoint eqc(m:fmap)(x y:dart){struct m}:Prop:=
 match m with
     V => False
  |  I m0 x0 => x=x0 /\ y=x0 \/ eqc m0 x y
  |  L m0 _ x0 y0 =>
      eqc m0 x y
     \/ eqc m0 x x0 /\ eqc m0 y0 y
     \/ eqc m0 x y0 /\ eqc m0 x0 y
 end.

(* Decidability of eqc: *)

Lemma eqc_dec : forall (m:fmap)(x y:dart),
   {eqc m x y} + {~eqc m x y}.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (IHm x y).
  tauto.
  elim (eq_dart_dec x d).
   elim (eq_dart_dec y d).
    tauto.
    tauto.
   tauto.
 simpl in |- *.
   intros x y.
   elim (IHm x y).
  tauto.
  elim (IHm x d0).
   elim (IHm d1 y).
    tauto.
    elim (IHm x d1).
     elim (IHm d0 y).
      tauto.
      tauto.
     tauto.
   elim (IHm d1 y).
    elim (IHm x d1).
     elim (IHm d0 y).
      tauto.
      tauto.
     tauto.
    elim (IHm x d1).
     elim (IHm d0 y).
      tauto.
      tauto.
     elim (IHm d0 y).
      tauto.
      tauto.
Qed.

(* Reflexivity of eqc: *)

Lemma refl_eqc: forall(m:fmap)(x:dart),
   exd m x -> eqc m x x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  tauto.
  right.
    apply IHm.
    tauto.
 simpl in |- *.
   intros.
   left.
   apply IHm.
   tauto.
Qed.

(* Symmetry of eqc: *)

Lemma symm_eqc: forall(m:fmap)(x y:dart),
   eqc m x y -> eqc m y x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  tauto.
  intro.
    generalize (IHm x y).
    tauto.
 simpl in |- *.
   intros.
   elim H.
  left.
    apply IHm.
    tauto.
  clear H.
    intro.
    elim H.
   clear H.
     intro.
     right.
     right.
     split.
    apply IHm.
      tauto.
    apply IHm.
      tauto.
   intros.
     right.
     left.
     split.
    apply IHm; tauto.
    apply IHm; tauto.
Qed.

(* Transitivity of eqc: *)

Lemma trans_eqc: forall(m:fmap)(x y z:dart),
   eqc m x y -> eqc m y z -> eqc m x z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim H.
  elim H0.
   tauto.
   intro.
     intros.
     elim H2.
     intros.
     rewrite H3.
     rewrite H4 in H1.
     tauto.
  intros.
    elim H0.
   intro.
     elim H2.
     intros.
     rewrite H4.
     rewrite H3 in H1.
     tauto.
   right.
     eapply IHm.
    apply H1.
      tauto.
 simpl in |- *.
   intros.
   elim H.
  clear H.
    elim H0.
   clear H0.
     left.
     eapply IHm.
    apply H0.
      tauto.
   clear H0.
     intros.
     elim H.
    clear H.
      intro.
      right.
      left.
      split.
     apply (IHm x y d0).
      tauto.
      tauto.
     tauto.
    intro.
      right.
      right.
      split.
     apply (IHm x y d1).
      tauto.
      tauto.
     tauto.
  clear H.
    intro.
    elim H.
   clear H.
     intro.
     elim H0.
    clear H0.
      intro.
      right.
      left.
      split.
     tauto.
     apply (IHm d1 y z).
      tauto.
      tauto.
    intros.
      elim H1.
     intros.
       clear H1.
       right.
       left.
       tauto.
     intro.
       clear H1.
       left.
       apply (IHm x d0 z).
      tauto.
      tauto.
   intro.
     clear H.
     elim H0.
    clear H0.
      intro.
      right.
      right.
      split.
     tauto.
     apply (IHm d0 y z).
      tauto.
      tauto.
    clear H0.
      intro.
      elim H.
     clear H.
       intro.
       left.
       apply (IHm x d1 z).
      tauto.
      tauto.
     intro.
       clear H.
       right.
       right.
       tauto.
Qed.

(* LEMMAS, USED IN THE FOLLOWING: *)

Lemma succ_eqc_A_r : forall m:fmap,
 inv_qhmap m ->
  forall (k:dim)(x:dart),
      succ m k x -> eqc m x (A m k x).
Proof.
intros.
induction m.
 simpl in |- *.
   unfold succ in H0.
   simpl in H0.
   tauto.
 unfold succ in H0.
   simpl in H0.
   simpl in |- *.
   unfold inv_qhmap in H.
   fold inv_qhmap in H.
   unfold prec_I in H.
   right.
   apply IHm.
  tauto.
  unfold succ in |- *.
    tauto.
 simpl in H.
   unfold prec_Lq in H.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   decompose [and] H.
   clear H.
   simpl in |- *.
   elim (eq_dim_dec k d).
  elim (eq_dart_dec x d0).
   intros.
     rewrite a.
     right.
     left.
     split.
    apply refl_eqc.
      tauto.
    apply refl_eqc.
      tauto.
   intros.
     left.
     apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
  intros.
    left.
    apply IHm.
   tauto.
   unfold succ in |- *; tauto.
Qed.

(* Idem, for A_1: *)

Lemma pred_eqc_A_1_r : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x:dart),
     pred m k x -> eqc m x (A_1 m k x).
Proof.
intros.
induction m.
 simpl in |- *.
   unfold pred in H0.
   simpl in H0.
    tauto.
unfold pred in H0.
  simpl in H0.
  simpl in |- *.
  unfold inv_qhmap in H.
  fold inv_qhmap in H.
  unfold prec_I in H.
  right.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
simpl in H.
  unfold prec_Lq in H.
  unfold pred in H0.
  simpl in H0.
  generalize H0.
  clear H0.
  decompose [and] H.
  clear H.
  simpl in |- *.
  elim (eq_dim_dec k d).
 elim (eq_dart_dec x d1).
  intros.
    rewrite a in |- *.
    right.
    right.
    split.
   apply refl_eqc.
      tauto.
  apply refl_eqc.
     tauto.
 intros.
   left.
   apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  left.
  apply IHm.
  tauto.
unfold pred in |- *.  
tauto.
Qed.

(* OK: *)

Lemma eqc_eqc_A_1_l : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   eqc m x y -> pred m k x -> eqc m (A_1 m k x) y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold pred in |- *.
   simpl in |- *.
   intros.
   elim H0; clear H0; intro.
  decompose [and] H0; clear H0.
    rewrite H2 in H1.
    elim H1.
    apply not_exd_A_1_nil.
   tauto.
   tauto.
  right.
    apply IHm.
   tauto.
   tauto.
   unfold pred in |- *.
     tauto.
 simpl in |- *.
   unfold pred in |- *.
   simpl in |- *.
   unfold prec_Lq in |- *.
   intros Hinv k x y.
   intro.
   elim (eq_dim_dec k d).
  intro.
    elim (eq_dart_dec x d1).
   intros.
     elim H; clear H; intro.
    right.
      left.
      split.
     apply refl_eqc.
       tauto.
     rewrite <- a0.
       tauto.
    elim H; clear H; intro.
     right.
       left.
       split.
      apply refl_eqc.
        tauto.
      tauto.
     tauto.
   intros.
     elim H; clear H; intro.
    left.
      apply IHm.
     tauto.
     tauto.
     unfold pred in |- *.
       tauto.
    elim H; clear H; intro.
     right.
       left.
       split.
      apply IHm.
       tauto.
       tauto.
       unfold pred in |- *; tauto.
      tauto.
     right.
       right.
       split.
      apply IHm.
       tauto.
       tauto.
       unfold pred in |- *; tauto.
      tauto.
  intros.
 elim H; clear H; intro.
   left.
     apply IHm.
    tauto.
    tauto.
    unfold pred in |- *.
      tauto.
   elim H; clear H; intro.
    right.
      left.
      split.
     apply IHm.
      tauto.
      tauto.
      unfold pred in |- *; tauto.
     tauto.
    right.
      right.
      split.
     apply IHm.
      tauto.
      tauto.
      unfold pred in |- *; tauto.
     tauto.
Qed.

(* INVERSES, Idem: *)

Lemma eqc_A_1_l_eqc : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   pred m k x ->  eqc m (A_1 m k x) y -> eqc m x y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  elim H1.
 clear H1.
   intro.
   decompose [and] H1.
   clear H1.
   rewrite <- H2 in H.
    absurd (exd m (A_1 m k x)).
   tauto.
 apply pred_exd_A_1.
   tauto.
 unfold pred in |- *.
    tauto.
intro.
  clear H1.
  right.
  apply IHm with k.
  tauto.
unfold pred in |- *.
   tauto.
 tauto.
simpl in |- *.
  unfold pred in |- *.
  simpl in |- *.
  unfold prec_Lq in |- *.
  intros Hinv k x y.
  elim (eq_dim_dec k d).
 intro.
   elim (eq_dart_dec x d1).
  intros.
    elim H0.
   clear H0.
     intro.
     right.
     right.
     rewrite a0 in |- *.
     split.
    apply refl_eqc.
       tauto.
    tauto.
  clear H0.
    intro.
    elim H0.
   clear H0.
     intro.
     rewrite a0 in |- *.
      tauto.
  clear H0.
    intro.
    rewrite a0 in |- *.
    right.
    right.
    split.
   apply refl_eqc.
      tauto.
   tauto.
 intros.
   elim H0.
  intro.
    clear H0.
    left.
     eapply IHm.
      tauto.
    unfold pred in |- *.
    apply H.
     tauto.
   clear H0.
   intro.
   elim H0.
  clear H0.
    intro.
    assert (eqc m x d0).
    eapply IHm.
       tauto.
     unfold pred in |- *.
     apply H.
      tauto.
     tauto.
   clear H0.
   intro.
   assert (eqc m x d1).
   eapply IHm.
      tauto.
    unfold pred in |- *.
    apply H.
     tauto.
    tauto.
  intros.
  elim H0.
 clear H0.
   intro.
   left.
    eapply IHm.
     tauto.
   unfold pred in |- *.
   apply H.
    tauto.
  clear H0.
  intro.
  elim H0.
 intro.
   clear H0.
   assert (eqc m x d0).
   eapply IHm.
      tauto.
    unfold pred in |- *.
    apply H.
     tauto.
    tauto.
  clear H0.
  intro.
  assert (eqc m x d1).
  eapply IHm.
     tauto.
   unfold pred in |- *.
   apply H.
    tauto.
   tauto.
Qed.

(* OK: *)

Lemma eqc_A_r_eqc : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   succ m k y ->  eqc m x (A m k y) -> eqc m x y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold succ in |- *.
  simpl in |- *.
  intros.
  elim H1.
 clear H1.
   intro.
   decompose [and] H1.
   clear H1.
   rewrite <- H3 in H.
    absurd (exd m (A m k y)).
   tauto.
 apply succ_exd_A.
   tauto.
 unfold succ in |- *.
    tauto.
intro.
  right.
   eapply IHm.
    tauto.
  unfold succ in |- *.
  apply H0.
   tauto.
  simpl in |- *.
  unfold succ in |- *.
  simpl in |- *.
  unfold prec_Lq in |- *.
  intros Hinv k x y.
  elim (eq_dim_dec k d).
 intro.
   elim (eq_dart_dec y d0).
  intros.
    elim H0.
   clear H0.
     intro.
     rewrite a0 in |- *.
     right.
     right.
     split.
     tauto.
   apply refl_eqc.
      tauto.
  clear H0.
    intro.
    elim H0.
   clear H0.
     intro.
     rewrite a0 in |- *.
      tauto.
  clear H0.
    intro.
    rewrite a0 in |- *.
    right.
    right.
    split.
    tauto.
  apply refl_eqc.
     tauto.
 intros.
   elim H0.
  clear H0.
    intro.
    left.
     eapply IHm.
      tauto.
    unfold succ in |- *.
    apply H.
     tauto.
   clear H0.
   intro.
   elim H0.
  clear H0.
    intro.
    assert (eqc m d1 y).
    eapply IHm.
       tauto.
     unfold succ in |- *.
     apply H.
      tauto.
     tauto.
   clear H0.
   intro.
   assert (eqc m d0 y).
   eapply IHm.
      tauto.
    unfold succ in |- *.
    apply H.
     tauto.
    tauto.
  intros.
  elim H0.
 intro.
   clear H0.
   left.
    eapply IHm.
     tauto.
   unfold succ in |- *.
   apply H.
    tauto.
  clear H0.
  intro.
  elim H0.
 clear H0.
   intro.
   assert (eqc m d1 y).
   eapply IHm.
      tauto.
    unfold succ in |- *.
    apply H.
     tauto.
    tauto.
  clear H0.
  intro.
  assert (eqc m d0 y).
  eapply IHm.
     tauto.
   unfold succ in |- *.
   apply H.
    tauto.
   tauto.
Qed.

(* Face path implies equivalence: with the LEMMAS above: *)

Lemma expf_eqc : forall m:fmap,
 inv_qhmap m ->
   forall (x y:dart), expf m x y -> eqc m x y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   elim H0.
  clear H0; intro.
    right.
    apply IHm.
   tauto.
   tauto.
  clear H0.
    intro.
    decompose [and] H0; clear H0.
    rewrite H1; rewrite H2; tauto.
 simpl in |- *.
   unfold prec_Lq in |- *.
   intros Hinv x y.
   induction d.
  intros.
    elim H.
   intro.
     left.
     apply IHm.
    tauto.
    tauto.
   clear H; intro.
     right.
     right.
     split.
    apply IHm.
     tauto.
     tauto.
    assert (eqc m (A_1 m di1 d0) y).
     apply IHm.
      tauto.
      tauto.
     eapply eqc_A_1_l_eqc.
      tauto.
      decompose [and] H.
        unfold pred in |- *.
        apply H1.
        tauto.
  intro.
    elim H.
   left.
     apply IHm.
    tauto.
    tauto.
   clear H; intro.
     right.
     right.
     split.
    assert (eqc m x (A m di0 d1)).
     apply IHm.
      tauto.
      tauto.
     eapply eqc_A_r_eqc.
      tauto.
      unfold succ in |- *.
        decompose [and] H.
        apply H1.
        tauto.
    apply IHm.
     tauto.
     tauto.
Qed.

(* OK: *)

Lemma expf_A_1_l_eqc : forall m:fmap,
 inv_qhmap m ->
   forall (x y:dart)(k:dim),
       expf m (A_1 m k x) y -> eqc m x y.
Proof.
intros.
eapply eqc_A_1_l_eqc.
 tauto.
 unfold pred in |- *.
   assert (A_1 m k x <> nil).
  generalize (expf_exd_exd m (A_1 m k x) y).
    intros.
    assert (exd m (A_1 m k x)).
   tauto.
   eapply exd_not_nil.
    apply H.
      tauto.
  apply H1.
   apply expf_eqc.
  tauto.
  tauto.
Qed.

(* IDEM : *)

Lemma expf_A_r_eqc : forall(m:fmap)(k:dim),
 inv_qhmap m ->
   forall (x y:dart), expf m x (A m k y) -> eqc m x y.
Proof.
intros.
eapply eqc_A_r_eqc.
 tauto.
 unfold succ in |- *.
   assert (A m k y <> nil).
  generalize (expf_exd_exd m x (A m k y)).
    intros.
    assert (exd m (A m k y)).
   tauto.
   eapply exd_not_nil.
    apply H.
      tauto.
  apply H1.
   apply expf_eqc.
  tauto.
  tauto.
Qed.

(*========================================================
      	      NUMBERING AND CHARACTERISTICS:
=========================================================*)

Require Import ZArith.
Open Scope Z_scope.

(* Number of darts: *)

Fixpoint nd(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nd m0 + 1
  | L m0 _ _ _ => nd m0
 end.

(* Number of vertices: *)

Fixpoint nv(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nv m0 + 1
  | L m0 di0 x y => nv m0
  | L m0 di1 x y => nv m0 -
      if eq_dart_dec (A (clos m0) di1 x) y
      then 0 else 1
 end.

(* Number of edges: *)

Fixpoint ne(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => ne m0 + 1
  | L m0 di0 x y => ne m0 -
      if eq_dart_dec (A (clos m0) di0 x) y
      then 0 else 1
  | L m0 di1 x y => ne m0
 end.

(* Number of faces: *)

Fixpoint nf(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nf m0 + 1
  | L m0 di0 x y =>
      let mc := clos m0 in
      let x0 := A mc di0 x in
      let x_1:= A_1 mc di1 x in
      nf m0 +
       if eq_dart_dec y x0 then 0
       else if expf_dec mc x_1 y then 1
	    else -1
  | L m0 di1 x y =>
      let mc := clos m0 in
      let x1 := A mc di1 x in
      let y0 := A mc di0 y in
      nf m0 +
       if eq_dart_dec y x1 then 0
       else if expf_dec mc x y0 then 1
	    else -1
 end.

(* Number of connected components: *)

Fixpoint nc(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nc m0 + 1
  | L m0 _ x y => nc m0 -
       if eqc_dec (clos m0) x y then 0 else 1
 end.

(* Euler-Poincare characteristic: *)

Definition ec(m:fmap): Z:=
  nv m + ne m + nf m - nd m.

(* The Euler-Poincare characteristic is even: OK: *)

Theorem even_ec : forall m:fmap, Zeven (ec m).
Proof.
unfold ec in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   cut
    (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) =
     Zsucc (Zsucc (nv m + ne m + nf m - nd m))).
  intros.
    rewrite H.
    apply Zeven_Sn.
    apply Zodd_Sn.
    tauto.
  omega.
 induction d.
  simpl in |- *.
    elim (eq_dart_dec (A (clos m) di0 d0) d1).
   intro.
     elim (eq_dart_dec d1 (A (clos m) di0 d0)).
    intro.
      cut
       (nv m + (ne m - 0) + (nf m + 0) - nd m =
        nv m + ne m + nf m - nd m).
     intro.
       rewrite H.
       tauto.
     omega.
    symmetry  in a.
      tauto.
   intro.
     elim (eq_dart_dec d1 (A (clos m) di0 d0)).
    intro.
      symmetry  in a.
      tauto.
    intro.
      elim (expf_dec (clos m) (A_1 (clos m) di1 d0) d1).
     intro.
       cut
        (nv m + (ne m - 1) + (nf m + 1) - nd m =
         nv m + ne m + nf m - nd m).
      intro.
        rewrite H.
        tauto.
      omega.
     intro.
       cut
        (nv m + (ne m - 1) + (nf m + -1) - nd m =
         Zpred (Zpred (nv m + ne m + nf m - nd m))).
      intro.
        rewrite H.
        apply Zeven_pred.
        apply Zodd_pred.
        tauto.
      unfold Zpred in |- *.
        omega.
  simpl in |- *.
    elim (eq_dart_dec (A (clos m) di1 d0) d1).
   intro.
     elim (eq_nat_dec d1 (A (clos m) di1 d0)).
    intro.
      cut
       (nv m - 0 + ne m + (nf m + 0) - nd m =
        nv m + ne m + nf m - nd m).
     intro.
       symmetry  in a.
       elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intro.
        cut
         (nv m - 0 + ne m + (nf m + 0) - nd m =
          nv m + ne m + nf m - nd m).
       intro.
         rewrite H.
         tauto.
       omega.
      tauto.
     omega.
    symmetry  in a.
      tauto.
   intro.
     elim (eq_dart_dec d1 (A (clos m) di1 d0)).
    intro.
      symmetry  in a.
      tauto.
    intro.
      elim (expf_dec (clos m) d0 (A (clos m) di0 d1)).
     intro.
       cut
        (nv m - 1 + ne m + (nf m + 1) - nd m =
         nv m + ne m + nf m - nd m).
      intro.
        rewrite H.
        tauto.
      omega.
     intro.
       cut
        (nv m - 1 + ne m + (nf m + -1) - nd m =
         Zpred (Zpred (nv m + ne m + nf m - nd m))).
      intro.
        rewrite H.
        apply Zeven_pred.
        apply Zodd_pred.
        tauto.
      unfold Zpred in |- *.
        omega.
Qed.

(* THEOREME OF THE GENUS: OK *)

Theorem genus_theorem : forall m:fmap,
  inv_qhmap m -> 2 * (nc m) >= (ec m).
Proof.
unfold ec in |- *.
intros.
rename H into Invm.
induction m.
 simpl in |- *.
   omega.
 unfold nc in |- *.
   fold nc in |- *.
   unfold nv in |- *; fold nv in |- *.
   unfold ne in |- *; fold ne in |- *.
   unfold nf in |- *; fold nf in |- *.
   unfold nd in |- *; fold nd in |- *.
   unfold inv_qhmap in Invm.
   fold inv_qhmap in Invm.
   assert (2 * nc m >= nv m + ne m + nf m - nd m).
  tauto.
  omega.
 unfold inv_qhmap in Invm; fold inv_qhmap in Invm.
   induction d.
  unfold nc in |- *; fold nc in |- *.
    unfold nv in |- *; fold nv in |- *.
    unfold ne in |- *; fold ne in |- *.
    unfold nf in |- *; fold nf in |- *.
    unfold nd in |- *; fold nd in |- *.
    elim (eqc_dec (clos m) d0 d1).
   intro.
     elim (eq_dart_dec (A (clos m) di0 d0) d1).
    intro.
      elim (eq_dart_dec d1 (A (clos m) di0 d0)).
     intro.
       assert (2 * nc m >= nv m + ne m + nf m - nd m).
      apply IHm.
        tauto.
      cut
       (nv m + (ne m - 0) + (nf m + 0) - nd m =
        nv m + ne m + nf m - nd m).
       intro.
         rewrite H0.
         cut (nc m - 0 = nc m).
        intro.
          rewrite H1.
          tauto.
        omega.
       omega.
     intro.
       symmetry  in a0.
       tauto.
    elim (eq_dart_dec d1 (A (clos m) di0 d0)).
     intro.
       symmetry  in a0.
       tauto.
     elim (expf_dec (clos m) (A_1 (clos m) di1 d0) d1).
      intros.
        assert (2 * nc m >= nv m + ne m + nf m - nd m).
       apply IHm; tauto.
       cut
        (nv m + (ne m - 1) + (nf m + 1) - nd m =
         nv m + ne m + nf m - nd m).
        intro.
          cut (nc m - 0 = nc m).
         intro.
           omega.
         omega.
        omega.
      intros.
        assert (2 * nc m >= nv m + ne m + nf m - nd m).
       apply IHm; tauto.
       cut
        (nv m + (ne m - 1) + (nf m + -1) - nd m =
         Zpred (Zpred (nv m + ne m + nf m - nd m))).
        intro.
          rewrite H0.
          unfold Zpred in |- *.
          omega.
        unfold Zpred in |- *.
          omega.
   intros.
     assert (2 * nc m >= nv m + ne m + nf m - nd m).
    apply IHm; tauto.
    elim (eq_dart_dec (A (clos m) di0 d0) d1).
     intro.
       elim b.
       rewrite <- a.
       apply succ_eqc_A_r.
      assert (inv_hmap (clos m)).
       apply inv_hmap_clos.
         tauto.
       rename H0 into Invc.
         unfold inv_hmap in Invc.
         tauto.
      unfold succ in |- *.
        rewrite a.
        intro.
        unfold prec_Lq in Invm.
        rewrite H0 in Invm.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
     intro.
       elim (eq_dart_dec d1 (A (clos m) di0 d0)).
      intro.
        symmetry  in a.
        tauto.
      intro.
        assert (2 * nc m >= nv m + ne m + nf m - nd m).
       apply IHm; tauto.
       elim (expf_dec (clos m) (A_1 (clos m) di1 d0) d1).
        intro.
          elim b.
          eapply expf_A_1_l_eqc.
         assert (inv_hmap (clos m)).
          apply inv_hmap_clos.
            tauto.
          rename H1 into Invc.
            unfold inv_hmap in Invc.
            tauto.
         apply a.
        intro.
          assert (2 * nc m >=
	   nv m + ne m + nf m - nd m).
         apply IHm; tauto.
         omega.
  unfold nc in |- *; fold nc in |- *.
    unfold nv in |- *; fold nv in |- *.
    unfold ne in |- *; fold ne in |- *.
    unfold nf in |- *; fold nf in |- *.
    unfold nd in |- *; fold nd in |- *.
    assert (2 * nc m >= nv m + ne m + nf m - nd m).
   apply IHm.
     tauto.
   elim (eqc_dec (clos m) d0 d1).
    intro.
      elim (eq_dart_dec (A (clos m) di1 d0) d1).
     elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intros.
        omega.
      intros.
        symmetry  in a0.
        tauto.
     intros.
       elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intro.
        symmetry  in a0.
        tauto.
      elim (expf_dec (clos m) d0 (A (clos m) di0 d1)).
       intros.
         omega.
       intros.
         omega.
    intro.
      elim (eq_dart_dec (A (clos m) di1 d0) d1).
     intro.
       elim b.
       rewrite <- a.
       apply succ_eqc_A_r.
      assert (inv_hmap (clos m)).
       apply inv_hmap_clos.
         tauto.
       rename H0 into Invc.
         unfold inv_hmap in Invc.
         tauto.
      unfold succ in |- *.
        rewrite a.
        intro.
        unfold prec_Lq in Invm.
        rewrite H0 in Invm.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
     intro.
       elim (eq_dart_dec d1 (A (clos m) di1 d0)).
      intro.
        symmetry  in a.
        tauto.
      intro.
        elim (expf_dec (clos m) d0 (A (clos m) di0 d1)).
       intro.
         elim b.
         eapply expf_A_r_eqc.
        assert (inv_hmap (clos m)).
         apply inv_hmap_clos.
           tauto.
         rename H0 into Invc.
           unfold inv_hmap in Invc.
           tauto.
        apply a.
       intro.
         omega.
Qed.

Definition genus(m:fmap):= (nc m) - (ec m)/2.

(* COROLLARY, OK: *)

Theorem genus_corollary : forall m:fmap,
  inv_qhmap m -> genus m >= 0.
Proof.
intros.
unfold genus in |- *.
generalize (genus_theorem m H).
generalize (even_ec m).
generalize (ec m).
generalize (nc m).
intros a b.
intros.
cut (a >= b / 2).
intro.
   omega.
 assert (b = 2 * Zdiv2 b).
  apply Zeven_div2.
    tauto.
  rewrite H2 in H1.
    assert (a >= Zdiv2 b).
   omega.
   rewrite H2.
 rewrite Zmult_comm.
     assert (Zdiv2 b * 2 / 2 = Zdiv2 b).
  apply Z_div_mult.
      omega.
    rewrite H4.
      tauto.
Qed.

Definition planar(m:fmap):= genus m = 0.

(* EULER-POINCARE FOMRMULA: *)

Theorem Euler_Poincare: forall m:fmap,
  inv_qhmap m -> planar m ->
    ec m / 2 = nc m.
Proof.
unfold planar in |- *.
unfold genus in |- *.
intros.
omega.
Qed.

(* REMARK: SYMMETRY OF expf in the closure NOT USED *)

(* ==========================================================
         PLANARITY CRITERIA (SUFFICIENT CONDITIONS)  
=============================================================*)

(* Dimension 0: *)

Theorem expf_planar_0: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m -> 
   prec_Lq m di0 x y -> let mc:= clos m in
    expf mc (A_1 mc di1 x) y -> 
      planar (L m di0 x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_Lq in |- *.
intros.
elim (eqc_dec (clos m) x y).
 intro.
   elim (eq_dart_dec (A (clos m) di0 x) y).
  intro.
    elim (eq_dart_dec y (A (clos m) di0 x)).
   intros.
     assert
      (nv m + (ne m - 0) + (nf m + 0) - nd m = 
          nv m + ne m + nf m - nd m).
     omega.
   rewrite H3 in |- *.
      omega.
  symmetry  in a0.
     tauto.
 elim (eq_dart_dec y (A (clos m) di0 x)).
  intro.
    symmetry  in a0.
     tauto.
 elim (expf_dec (clos m) (A_1 (clos m) di1 x) y).
  intros.
    assert
     (nv m + (ne m - 1) + (nf m + 1) - nd m = 
       nv m + ne m + nf m - nd m).
    omega.
  rewrite H3 in |- *.
     omega.
  tauto.
intro.
  elim b.
   eapply expf_A_1_l_eqc.
   assert (inv_hmap (clos m)).
  apply inv_hmap_clos.
     tauto.
 unfold inv_hmap in H3.
    tauto.

  apply H2.
Qed.

(* Dimension 1: *) 

Theorem expf_planar_1: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m ->
    prec_Lq m di1 x y -> let mc:= clos m in
      expf mc x (A mc di0 y) -> 
        planar (L m di1 x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_Lq in |- *.
intros.
elim (eqc_dec (clos m) x y).
 elim (eq_dart_dec (A (clos m) di1 x) y).
  intros.
    elim (eq_dart_dec y (A (clos m) di1 x)).
   intros.
     assert (nv m - 0 + ne m + (nf m + 0) - nd m = 
         nv m + ne m + nf m - nd m).
     omega.
   rewrite H3 in |- *.
      omega.
  symmetry  in a.
     tauto.
 intros.
   elim (eq_dart_dec y (A (clos m) di1 x)).
  intro.
    symmetry  in a0.
     tauto.
 elim (expf_dec (clos m) x (A (clos m) di0 y)).
  intros.
    assert (nv m - 1 + ne m + (nf m + 1) - nd m = 
        nv m + ne m + nf m - nd m).
    omega.
  rewrite H3 in |- *.
     omega.
  tauto.
intro.
  elim b.
   eapply expf_A_r_eqc.

   assert (inv_hmap (clos m)).
  apply inv_hmap_clos.
     tauto.
 unfold inv_hmap in H3.
    tauto.
  apply H2.
Qed.

(*==========================================================
============================================================

		      THE END

============================================================
===========================================================*)
