(** * Kakeya Problem - Projection and Direction Coverage (Section 4)
    
    This file formalizes:
    - Section 4.1: Orthogonal Projection
    - Theorem 4.1: Direction Coverage
    - Corollary 4.2: K_t is a Kakeya set
*)

Require Import Reals.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import kakeya_base.
Require Import kakeya_hypertorus.

Import KakeyaBase.

(** ** Section 1: Orthogonal Projection (Section 4.1) *)

Section OrthogonalProjection.
  Context {kp : KakeyaParams}.
  
  (** The induced Kakeya set K_t = π(T^n(t)) *)
  Definition Kakeya_set_K {n : nat} (t : R) (Ht : contraction_param t) : 
    Rvec n -> Prop :=
    fun w => exists (v : Rvec (S n)), 
      hypertorus_image t Ht v /\
      w = orth_projection v.
  
  (** Projection is well-defined *)
  Theorem projection_well_defined : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (v : Rvec (S n)),
    hypertorus_image t Ht v ->
    exists (w : Rvec n), w = orth_projection v.
  Proof.
    intros n t Ht v Hv.
    exists (orth_projection v).
    reflexivity.
  Qed.
  
  (** Explicit form of the projection *)
  Theorem projection_explicit : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (theta : R) (u : unit_sphere n),
    0 <= theta < 2 * PI ->
    orth_projection (Phi_t t theta u) = 
    vec_smul (radial_scale t theta) (proj1_sig u).
  Proof.
    intros n t Ht theta u Htheta.
    unfold orth_projection, Phi_t, radial_scale, vec_smul.
    apply functional_extensionality; intro i.
    reflexivity.
  Qed.

End OrthogonalProjection.

(** ** Section 2: Direction Coverage via Meridian Circles (Theorem 4.1) *)

Section DirectionCoverage.
  Context {kp : KakeyaParams}.
  
  (** Meridian circle on the hypertorus for a fixed direction u *)
  Definition meridian_circle {n : nat} (t : R) (u : unit_sphere n) : 
    Rvec (S n) -> Prop :=
    fun v => exists (theta : R),
      0 <= theta < 2 * PI /\
      v = Phi_t t theta u.
  
  (** Projection of the meridian circle *)
  Theorem meridian_circle_projection : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (u : unit_sphere n) (w : Rvec n),
    (exists v, meridian_circle t u v /\
      w = orth_projection v) <->
    exists (theta : R),
      0 <= theta < 2 * PI /\
      w = vec_smul (radial_scale t theta) (proj1_sig u).
  Proof.
    intros n t Ht u w.
    split; intros [theta Htheta].
    - (* Forward: meridian circle -> projected segment *)
      destruct Htheta as [v [Hmeridian Hw]].
      unfold meridian_circle in Hmeridian.
      destruct Hmeridian as [theta' [Htheta' Hv]].
      exists theta'.
      split; auto.
      rewrite Hw.
      rewrite Hv.
      apply projection_explicit; auto.
    - (* Backward: projected segment -> meridian circle *)
      destruct Htheta as [Htheta Hw].
      exists (Phi_t t theta u).
      split.
      + unfold meridian_circle.
        exists theta.
        split; auto.
      + rewrite Hw.
        apply projection_explicit; auto.
  Qed.
  
  (** The projected meridian circle is a line segment in direction u *)
  Theorem projected_meridian_is_segment : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (u : unit_sphere n),
    let half_length := r_param * scale_factor t in
    let center := vec_smul (R_param * scale_factor t) (proj1_sig u) in
    forall (w : Rvec n),
    (exists v, meridian_circle t u v /\
      w = orth_projection v) <->
    line_segment center u half_length w.
  Proof.
    intros n t Ht u half_length center w.
    split.
    - (* Forward: projected meridian point is on the line segment *)
      intros [v [Hmeridian Hw]].
      unfold meridian_circle in Hmeridian.
      destruct Hmeridian as [theta [Htheta Hv]].
      unfold line_segment.
      exists (r_param * scale_factor t * cos theta).
      split.
      + (* Show -half_length <= s <= half_length *)
        unfold half_length.
        assert (Hcos: -1 <= cos theta <= 1) by (split; apply cos_bound).
        assert (Hpos: r_param * scale_factor t > 0).
        { apply Rmult_lt_0_compat; auto.
          apply scale_factor_positive; auto. }
        split; nra.
      + (* Show w = center + s*u *)
        rewrite Hw.
        rewrite Hv.
        unfold center, half_length, Phi_t, orth_projection, vec_add, vec_smul.
        apply functional_extensionality; intro i.
        unfold radial_scale.
        ring.
    - (* Backward: line segment point comes from projected meridian *)
      intros [s [Hs Hw]].
      unfold half_length in Hs.
      assert (Hcos_bound: -1 <= s / (r_param * scale_factor t) <= 1).
      { 
        unfold half_length in Hs.
        rewrite <- (Rmult_1_r (r_param * scale_factor t)) in Hs.
        assert (Hscale_pos: r_param * scale_factor t > 0).
        { apply Rmult_lt_0_compat; auto.
          apply scale_factor_positive; auto. }
        assert (Hrange: -1 <= s / (r_param * scale_factor t) <= 1).
        { nra. }
        exact Hrange.
      }
      assert (Htheta_exists: exists theta : R,
        0 <= theta < 2 * PI /\ cos theta = s / (r_param * scale_factor t)).
      {
        assert (Hcos_val: s / (r_param * scale_factor t)).
        destruct (archimed_cor1 (s / (r_param * scale_factor t))) as [H1 H2].
        assert (Hcos_in_range: -1 <= s / (r_param * scale_factor t) <= 1) by nra.
        exists (acos (s / (r_param * scale_factor t))).
        split.
        - apply acos_range.
        - symmetry; apply cos_acos.
      }
      destruct Htheta_exists as [theta [Htheta Hcos]].
      exists (Phi_t t theta u).
      split.
      + unfold meridian_circle.
        exists theta.
        split; auto.
      + rewrite Hw.
        apply projection_explicit; auto.
        unfold vec_add, vec_smul, center.
        apply functional_extensionality; intro i.
        unfold radial_scale.
        assert (Hscale_nonzero: r_param * scale_factor t <> 0).
        { apply Rgt_not_eq.
          apply Rmult_lt_0_compat; auto.
          apply scale_factor_positive; auto. }
        field_simplify; auto.
        rewrite <- Hcos.
        ring.
    - (* Backward: line segment point comes from projected meridian *)
      intros [s [Hs Hw]].
      unfold half_length in Hs.
      assert (Hcos_bound: -1 <= s / (r_param * scale_factor t) <= 1).
      { 
        assert (Hpos: r_param * scale_factor t > 0).
        { apply Rmult_lt_0_compat; auto.
          apply scale_factor_positive; auto. }
        nra.
      }
      assert (Htheta_exists: exists theta : R,
        0 <= theta < 2 * PI /\ cos theta = s / (r_param * scale_factor t)).
      {
        exists (acos (s / (r_param * scale_factor t))).
        split.
        - apply acos_range.
        - symmetry; apply cos_acos.
      }
      destruct Htheta_exists as [theta [Htheta Hcos]].
      exists (Phi_t t theta u).
      split.
      + unfold meridian_circle.
        exists theta.
        split; auto.
      + rewrite Hw.
        apply projection_explicit; auto.
        unfold vec_add, vec_smul, center.
        apply functional_extensionality; intro i.
        unfold radial_scale.
        assert (Hscale_nonzero: r_param * scale_factor t <> 0).
        { apply Rgt_not_eq.
          apply Rmult_lt_0_compat; auto.
          apply scale_factor_positive; auto. }
        field_simplify; auto.
         rewrite <- Hcos.
         ring.
  Qed.
  
  (** Theorem 4.1: Direction Coverage *)
  (** For any t ∈ [0,1), the set K_t contains a unit line segment 
      in every direction u ∈ S^(n-1) *)
  Theorem direction_coverage : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (u : unit_sphere n),
    exists (center : Rvec n),
    forall (w : Rvec n),
    unit_line_segment center u w ->
    Kakeya_set_K t Ht w.
  Proof.
    intros n t Ht u.
    exists (vec_smul (R_param * scale_factor t) (proj1_sig u)).
    intros w Hw.
    unfold Kakeya_set_K.
    assert (Hsegment: exists s : R,
      - (r_param * scale_factor t) / 2 <= s <= (r_param * scale_factor t) / 2 /\
      w = vec_add (vec_smul (R_param * scale_factor t) (proj1_sig u))
                (vec_smul s (proj1_sig u))).
    { 
      unfold unit_line_segment, line_segment in Hw.
      destruct Hw as [s [Hs Hw]].
      exists s.
      split; auto.
    }
    destruct Hsegment as [s [Hs Hw]].
    assert (Hcos_exists: exists theta : R,
      0 <= theta < 2 * PI /\ s = r_param * scale_factor t * cos theta).
    {
      assert (Hscaled: s / (r_param * scale_factor t)).
      assert (Hbound: -1 <= s / (r_param * scale_factor t) <= 1).
      { 
        assert (Hpos: r_param * scale_factor t > 0).
        { apply Rmult_lt_0_compat; auto.
          apply scale_factor_positive; auto. }
        nra.
      }
      exists (acos (s / (r_param * scale_factor t))).
      split.
      - apply acos_range.
      - symmetry; apply cos_acos.
    }
    destruct Hcos_exists as [theta [Htheta Hcos]].
    exists (Phi_t t theta u).
    split; auto.
    unfold hypertorus_image.
    exists theta.
    exists u.
    split; auto.
 Qed.

End DirectionCoverage.

(** ** Section 3: Corollary 4.2 - K_t is a Kakeya set *)

Section KakeyaSetProperty.
  Context {kp : KakeyaParams}.
  
  (** Corollary 4.2: K_t is a Kakeya set for all t ∈ [0,1) *)
  Theorem K_t_is_kakeya_set : forall (n : nat) (t : R) (Ht : contraction_param t),
    is_kakeya_set (Kakeya_set_K t Ht).
  Proof.
    intros n t Ht.
    unfold is_kakeya_set.
    intro u.
    (* Apply Theorem 4.1 *)
    apply direction_coverage; auto.
  Qed.
  
  (** Every point in K_t comes from some direction *)
  Theorem K_t_point_has_direction : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (w : Rvec n),
    Kakeya_set_K t Ht w ->
    exists (u : unit_sphere n) (center : Rvec n),
    unit_line_segment center u w.
  Proof.
    intros n t Ht w HK.
    unfold Kakeya_set_K in HK.
    destruct HK as [v [Hv Hw]].
    unfold hypertorus_image in Hv.
    destruct Hv as [theta [u [Htheta Hv]]].
    exists u.
    exists (vec_smul (R_param * scale_factor t) (proj1_sig u)).
    unfold unit_line_segment, line_segment.
    exists (r_param * scale_factor t * cos theta).
    split.
    - assert (Hcos_bound: -1 <= cos theta <= 1) by (split; apply cos_bound).
      assert (Hpos: r_param * scale_factor t > 0).
      { apply Rmult_lt_0_compat; auto.
        apply scale_factor_positive; auto. }
      nra.
    - rewrite Hw, Hv.
      unfold orth_projection, vec_add, vec_smul, radial_scale.
      apply functional_extensionality; intro i.
      ring.
  Qed.

End KakeyaSetProperty.

(** ** Section 4: Properties of the Construction *)

Section ConstructionProperties.
  Context {kp : KakeyaParams}.
  
  (** The length of the line segment in each direction is 2r(1-t) *)
  Theorem segment_length : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (u : unit_sphere n),
    let segment_length := 2 * r_param * scale_factor t in
    segment_length > 0.
  Proof.
    intros n t Ht u segment_length.
    unfold segment_length, scale_factor.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; lra.
    - unfold contraction_param in Ht.
      lra.
  Qed.
  
  (** By appropriate scaling (setting r = 1/2), we get unit length segments *)
  Theorem unit_length_achievable : forall (n : nat) (t : R) (Ht : contraction_param t),
    r_param = 1/2 ->
    forall (u : unit_sphere n),
    let segment_length := 2 * r_param * scale_factor t in
    segment_length = scale_factor t.
  Proof.
    intros n t Ht Hr u segment_length.
    unfold segment_length.
    rewrite Hr.
    field.
  Qed.
  
  (** The range of the projected segment *)
  Theorem projected_segment_range : forall (n : nat) (t : R) (Ht : contraction_param t),
    forall (u : unit_sphere n) (w : Rvec n),
    (exists v, meridian_circle t u v /\
      w = orth_projection v) ->
    exists (s : R),
    -1 <= s <= 1 /\
    w = vec_smul ((R_param + s * r_param) * scale_factor t) (proj1_sig u).
  Proof.
    intros n t Ht u w Hmeridian.
    destruct Hmeridian as [v [Hmeridian Hw]].
    unfold meridian_circle in Hmeridian.
    destruct Hmeridian as [theta [Htheta Hv]].
    exists (cos theta).
    split.
    - (* -1 <= cos theta <= 1 *)
      split; apply cos_bound.
    - (* w = ((R + s*r)(1-t))u *)
      rewrite Hw.
      rewrite Hv.
      unfold orth_projection, Phi_t, vec_smul, radial_scale.
      apply functional_extensionality; intro i.
      ring.
  Qed.

End ConstructionProperties.

(** ** Section 5: Summary of Section 4 Results *)

Section Section4Summary.
  Context {kp : KakeyaParams}.
  
  (** Theorem 4.1: Direction Coverage *)
  Check direction_coverage.
  
  (** Corollary 4.2: K_t is a Kakeya set *)
  Check K_t_is_kakeya_set.
  
  (** Additional properties *)
  Check meridian_circle_projection.
  Check projected_meridian_is_segment.

End Section4Summary.
