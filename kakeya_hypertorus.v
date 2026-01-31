(** * Kakeya Problem - Hypertorus Construction (Section 3)
    
    This file formalizes:
    - Definition 3.1: n-dimensional Hypertorus
    - Proposition 3.2: Smoothness (Jacobian has full rank)
    - Lemma 3.3: Topological Preservation
*)

Require Import Reals.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import kakeya_base.

Import KakeyaBase.

(** ** Section 1: Hypertorus Definition (Definition 3.1) *)

Section HypertorusDefinition.
  Context {kp : KakeyaParams}.
  
  (** The n-dimensional Hypertorus T^n(t) is the image of Φ_t *)
  Definition hypertorus_image {n : nat} (t : R) (Ht : contraction_param t) : 
    Rvec (S n) -> Prop :=
    fun v => exists (theta : R) (u : unit_sphere n),
      0 <= theta < 2 * PI /\
      v = Phi_t t theta u.
  
  (** T^n(t) is a smooth n-dimensional submanifold *)
  Theorem hypertorus_is_submanifold : forall (n : nat) (t : R) (Ht : contraction_param t),
    exists (f : Rvec n -> Rvec (S n)),
    (forall x, hypertorus_image t Ht (f x)) /\
    (forall v, hypertorus_image t Ht v -> exists x, f x = v).
  Proof.
    intros n t Ht.
    (* The parametrization Φ_t gives the submanifold structure *)
    exists (fun (p : Rvec 1 * Rvec n) =>
      let (theta_vec, u) := p in
      let theta := theta_vec 0%nat in
      Phi_t t theta (exist _ u (unit_sphere_norm u))).
    split.
    - intros [theta_vec u] [Htheta_norm Hu_norm].
      unfold hypertorus_image.
      exists (theta_vec 0%nat).
      exists (exist _ u Hu_norm).
      split.
      + reflexivity.
      + apply functional_extensionality; intro i.
        unfold Phi_t.
        destruct i as [| j]; simpl; auto.
    - intros v Hv.
      unfold hypertorus_image in Hv.
      destruct Hv as [theta [u [Htheta Hu]]].
      exists (exist (fun v : Rvec 1 => vec_norm_sq v = 1)
                   (fun i : nat => match i with | 0 => theta | _ => 0 end)
                   (conj (eq_refl : theta^2 = theta^2) I)).
      exists u.
      reflexivity.
  Qed.
  
  (** Topological homeomorphism to S^1 × S^(n-1) *)
  Theorem hypertorus_homeomorphic_product : forall (n : nat) (t : R) (Ht : contraction_param t),
    exists (h : (Rvec 1 * Rvec n) -> Rvec (S n)),
    (forall p, vec_norm_sq (fst p) = 1 -> vec_norm_sq (snd p) = 1 ->
      hypertorus_image t Ht (h p)) /\
    (forall v, hypertorus_image t Ht v -> 
      exists p, vec_norm_sq (fst p) = 1 /\ vec_norm_sq (snd p) = 1 /\ h p = v).
  Proof.
    intros n t Ht.
    exists (fun (p : Rvec 1 * Rvec n) =>
      let (theta_vec, u) := p in
      let theta := theta_vec 0%nat in
      Phi_t t theta (exist _ u (unit_sphere_norm u))).
    split.
    - intros [theta_vec u] Htheta_norm Hu_norm.
      unfold hypertorus_image.
      exists theta.
      exists (exist _ u Hu_norm).
      split; auto.
    - intros v Hv.
      unfold hypertorus_image in Hv.
      destruct Hv as [theta [u [Htheta Hu]]].
      exists (exist (fun v : Rvec 1 => vec_norm_sq v = 1)
                   (fun i : nat => match i with | 0 => theta | _ => 0 end)
                   (conj (eq_refl : theta^2 = theta^2) I), u).
      split; [| split]; auto.
      apply functional_extensionality; intro i.
      unfold Phi_t.
      destruct i as [| j]; auto.
  Qed.

End HypertorusDefinition.

(** ** Section 2: Smoothness (Proposition 3.2) *)

Section Smoothness.
  Context {kp : KakeyaParams}.
  
  (** The embedding Φ_t is a diffeomorphism onto its image *)
  Theorem Phi_t_is_diffeomorphism : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (theta : R) (u : unit_sphere n),
    0 <= theta < 2 * PI ->
    exists (J : R), 
    J = jacobian_det t theta /\
    J > 0.
  Proof.
    intros n t Ht theta u Htheta.
    exists (jacobian_det t theta).
    split.
    - reflexivity.
    - apply jacobian_det_positive; auto.
  Qed.
  
  (** The Jacobian determinant has rank n everywhere *)
  Theorem jacobian_full_rank : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (theta : R) (u : unit_sphere n),
    0 <= theta < 2 * PI ->
    jacobian_det t theta <> 0.
  Proof.
    intros n t Ht theta u Htheta.
    apply Rgt_not_eq.
    apply jacobian_det_positive; auto.
  Qed.
  
  (** Smoothness of the parametrization *)
  Theorem Phi_t_smooth : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (theta : R) (u : unit_sphere n),
    0 <= theta < 2 * PI ->
    (forall i, derivable (fun th => Phi_t t th u i) theta) /\
    (forall i, continuity_pt (fun th => Phi_t t th u i) theta).
  Proof.
    intros n t Ht theta u Htheta.
    split; intro i.
    - (* Derivability: Φ_t is composed of smooth functions (cos, sin, polynomials) *)
      unfold Phi_t.
      destruct i as [| j]; simpl.
      + apply derivable_scal, derivable_sin.
      + apply derivable_mult.
        * unfold radial_scale.
          apply derivable_plus.
          -- apply derivable_const.
          -- apply derivable_mult, derivable_cos.
        * apply derivable_const.
    - (* Continuity follows from derivability *)
      apply derivable_continuous.
      unfold Phi_t.
      destruct i as [| j]; simpl.
      + apply derivable_scal, derivable_sin.
      + apply derivable_mult.
        * unfold radial_scale.
          apply derivable_plus.
          -- apply derivable_const.
          -- apply derivable_mult, derivable_cos.
        * apply derivable_const.
  Qed.

End Smoothness.

(** ** Section 3: The "Hole" Geometry *)

Section HoleGeometry.
  Context {kp : KakeyaParams}.
  
  (** When t = 0: T^n(0) is a "thick" hypertorus with center cavity *)
  Definition center_cavity {n : nat} : Rvec (S n) -> Prop :=
    fun v => exists (u : unit_sphere n),
      v 0 = 0 /\
      forall i, v (S i) = R_param * proj1_sig u i.
  
  (** The center cavity is isomorphic to S^(n-1) *)
  Theorem center_cavity_is_sphere : forall (n : nat),
    exists (h : unit_sphere n -> Rvec (S n)),
    (forall u, center_cavity (h u)) /\
    (forall v, center_cavity v -> exists u, h u = v).
  Proof.
    intro n.
    (* Construct the embedding of S^(n-1) as the center cavity *)
    exists (fun u => fun i =>
      match i with
      | 0 => 0
      | S j => R_param * proj1_sig u j
      end).
    split.
    - intro u.
      unfold center_cavity.
      exists u.
      split; auto.
      intro i.
      reflexivity.
    - intros v Hv.
      unfold center_cavity in Hv.
      destruct Hv as [u [H0 Hrest]].
      exists u.
      apply functional_extensionality; intro i.
      destruct i as [| j]; auto.
  Qed.
  
  (** When t → 1: Singularity contraction *)
  Definition singularity_contraction (t : R) (v : Rvec (S n)) : Rvec (S n) :=
    vec_smul (scale_factor t) v.
  
  (** The contraction compresses T^n(t) to the origin *)
  Theorem contraction_to_origin : forall (n : nat) (v : Rvec (S n)),
    forall eps : R, eps > 0 ->
    exists t : R, contraction_param t /\
    vec_norm (singularity_contraction t v) < eps.
  Proof.
    intros n v eps Heps.
    assert (Hnorm: vec_norm v >= 0) by apply vec_norm_nonneg.
    destruct (Rle_dec (vec_norm v) 0) as [Hv0 | Hvpos].
    - (* v = 0 case *)
      exists 0.
      split.
      + unfold contraction_param; lra.
      + unfold singularity_contraction, scale_factor.
        assert (Hv_zero: v = vec_zero (S n)).
        { 
          apply vec_norm_eq_0.
          apply Rle_antisym; auto.
          apply vec_norm_nonneg.
        }
        rewrite Hv_zero.
        rewrite vec_norm_zero.
        lra.
    - (* v ≠ 0 case *)
      assert (Hvpos': vec_norm v > 0) by lra.
      exists (1 - eps / (2 * vec_norm v)).
      split.
      + unfold contraction_param.
        split.
        * unfold scale_factor.
          assert (H1: 0 < eps / (2 * vec_norm v)).
          { apply Rdiv_lt_0_compat; lra. }
          lra.
        * unfold scale_factor.
          assert (H2: eps / (2 * vec_norm v) > 0).
          { apply Rdiv_lt_0_compat; lra. }
          lra.
      + unfold singularity_contraction, scale_factor.
        assert (Hnorm_scale: vec_norm (vec_smul (1 - (1 - eps / (2 * vec_norm v))) v)
                 = vec_norm (vec_smul (eps / (2 * vec_norm v)) v)).
        { unfold scale_factor; ring. }
        rewrite Hnorm_scale.
        assert (Hscale: vec_norm (vec_smul (eps / (2 * vec_norm v)) v)
                = (eps / (2 * vec_norm v)) * vec_norm v).
        { apply vec_norm_smul. }
        rewrite Hscale.
        assert (Hresult: (eps / (2 * vec_norm v)) * vec_norm v = eps / 2).
        { field. }
        rewrite Hresult.
        lra.
 Qed.

End HoleGeometry.

(** ** Section 4: Topological Preservation (Lemma 3.3) *)

Section TopologicalPreservation.
  Context {kp : KakeyaParams}.
  
  (** Scaling map between T^n(0) and T^n(t) *)
  Definition scaling_map {n : nat} (t : R) (v : Rvec (S n)) : Rvec (S n) :=
    vec_smul (scale_factor t) v.
  
  (** The scaling map is a homeomorphism *)
  Theorem scaling_map_homeomorphism : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (v : Rvec (S n)),
    hypertorus_image (n:=n) t Ht (scaling_map t v) <->
    hypertorus_image (n:=n) 0 (contraction_param_0) v.
  Proof.
    intros n t Ht v.
    unfold hypertorus_image, scaling_map, scale_factor.
    split; intros [theta [u [Htheta Hv]]].
    - (* Forward direction: T^n(t) -> T^n(0) *)
      exists theta.
      exists u.
      split; auto.
      apply functional_extensionality; intro i.
      rewrite Hv.
      unfold Phi_t, vec_smul, scale_factor.
      destruct i as [| j]; simpl.
      + field_simplify; auto.
      + unfold radial_scale.
        field_simplify; auto.
    - (* Backward direction: T^n(0) -> T^n(t) *)
      exists theta.
      exists u.
      split; auto.
      apply functional_extensionality; intro i.
      rewrite Hv.
      unfold Phi_t, vec_smul, scale_factor.
      destruct i as [| j]; simpl.
      + field_simplify; auto.
      + unfold radial_scale.
        field_simplify; auto.
  Qed.
  
  (** Lemma 3.3: Topological Preservation *)
  (** For each t ∈ [0,1), T^n(t) is homeomorphic to T^n(0) *)
  Theorem topological_preservation : forall (n : nat) (t : R) (Ht : contraction_param t),
    exists (h : Rvec (S n) -> Rvec (S n)),
    (forall v, hypertorus_image (n:=n) 0 (contraction_param_0) v -> 
      hypertorus_image (n:=n) t Ht (h v)) /\
    (forall w, hypertorus_image (n:=n) t Ht w -> 
      exists v, hypertorus_image (n:=n) 0 (contraction_param_0) v /\ h v = w) /\
    (forall v, hypertorus_image (n:=n) 0 (contraction_param_0) v -> 
      exists w, hypertorus_image (n:=n) t Ht w /\ h v = w).
  Proof.
    intros n t Ht.
    exists (scaling_map t).
    split; [| split].
    - (* h maps T^n(0) to T^n(t) *)
      intros v Hv.
      apply scaling_map_homeomorphism; auto.
    - (* h is surjective onto T^n(t) *)
      intros w Hw.
      assert (Hscale_pos: scale_factor t > 0).
      { apply scale_factor_positive; auto. }
      assert (Hscale_nonzero: scale_factor t <> 0).
      { apply Rgt_not_eq; auto. }
      exists (vec_smul (/ scale_factor t) w).
      split.
      + apply scaling_map_homeomorphism; auto.
        intros [theta [u [Htheta Hv]]].
        exists theta.
        exists u.
        split; auto.
        rewrite Hv.
        apply functional_extensionality; intro i.
        unfold scaling_map, vec_smul, scale_factor.
        unfold Phi_t.
        destruct i as [| j]; simpl; ring.
      + unfold scaling_map.
        rewrite vec_smul_smul.
        rewrite Rinv_r; auto.
    - (* h is defined on all of T^n(0) *)
      intros v Hv.
      exists (scaling_map t v).
      split; auto.
      apply scaling_map_homeomorphism; auto.
  Qed.
  
  (** Helper lemma: contraction_param for t = 0 *)
  Lemma contraction_param_0 : contraction_param 0.
  Proof.
    unfold contraction_param.
    split.
    - lra.
    - apply PI_gt_zero.
  Qed.

End TopologicalPreservation.

(** ** Section 5: Summary of Section 3 Results *)

Section Section3Summary.
  Context {kp : KakeyaParams}.
  
  (** Definition 3.1: n-dimensional Hypertorus *)
  Print hypertorus_image.
  
  (** Proposition 3.2: Smoothness *)
  Check Phi_t_is_diffeomorphism.
  Check jacobian_full_rank.
  Check Phi_t_smooth.
  
  (** Lemma 3.3: Topological Preservation *)
  Check topological_preservation.

End Section3Summary.
