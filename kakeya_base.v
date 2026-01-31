(** * Kakeya Problem - Base Definitions and Setup
    
    This file establishes the foundational mathematical structures needed for the
    Kakeya problem formalization, including:
    - Real number parameters (R, r, t)
    - Vector spaces and spheres
    - Basic topological definitions
*)

Require Import Reals.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

(** ** Section 1: Real Number Parameters *)

(** Fixed constants for the Kakeya construction *)
Class KakeyaParams := {
  R_param : R;  (** Major radius: distance from origin to tube center *)
  r_param : R;  (** Minor radius: radius of the tube itself *)
  R_positive : R_param > 0;
  r_positive : r_param > 0;
  R_gt_r : R_param > r_param;
}.

(** Contraction parameter t ∈ [0, 1) *)
Definition contraction_param (t : R) := 0 <= t < 1.

(** Scaling factor (1-t) *)
Definition scale_factor (t : R) := 1 - t.

Lemma scale_factor_positive : forall (t : R), contraction_param t -> scale_factor t > 0.
Proof.
  intros t Ht.
  unfold scale_factor, contraction_param in *.
  lra.
Qed.

Lemma scale_factor_le_1 : forall (t : R), 0 <= t -> scale_factor t <= 1.
Proof.
  intros t Ht.
  unfold scale_factor.
  lra.
Qed.

(** ** Section 2: Vector Space Definitions *)

(** n-dimensional real vector *)
Definition Rvec (n : nat) := nat -> R.

(** Zero vector *)
Definition vec_zero (n : nat) : Rvec n := fun _ => 0.

(** Vector addition *)
Definition vec_add {n : nat} (u v : Rvec n) : Rvec n :=
  fun i => u i + v i.

(** Scalar multiplication *)
Definition vec_smul {n : nat} (c : R) (v : Rvec n) : Rvec n :=
  fun i => c * v i.

(** Dot product *)
Definition vec_dot {n : nat} (u v : Rvec n) : R :=
  sum_f_R0 (fun i => u i * v i) (n - 1).

(** Vector norm squared *)
Definition vec_norm_sq {n : nat} (v : Rvec n) : R :=
  vec_dot v v.

(** Vector norm *)
Definition vec_norm {n : nat} (v : Rvec n) : R :=
  sqrt (vec_norm_sq v).

(** ** Section 3: Sphere Definitions *)

(** Unit sphere S^(n-1) in R^n *)
Definition unit_sphere (n : nat) : Type :=
  { u : Rvec n | vec_norm_sq u = 1 }.

(** Unit circle S^1 parametrized by angle θ *)
Definition unit_circle := { theta : R | 0 <= theta < 2 * PI }.

(** Circle coordinates *)
Definition circle_cos (theta : R) : R := cos theta.
Definition circle_sin (theta : R) : R := sin theta.

Lemma circle_identity : forall theta, (cos theta)^2 + (sin theta)^2 = 1.
Proof.
  intro theta.
  apply cos2_sin2.
Qed.

(** ** Section 4: Hypertorus Definition *)

(** The hypertorus is the product S^1 × S^(n-1) *)
Definition hypertorus (n : nat) : Type :=
  unit_circle * unit_sphere n.

(** Parametrization of the hypertorus in R^(n+1)
    
    Φ_t(θ, u) = ((R(1-t) + r(1-t)cos θ)u, r(1-t)sin θ)
*)
Section HypertorusParametrization.
  Context {kp : KakeyaParams}.
  
  Variable t : R.
  Hypothesis t_valid : contraction_param t.
  
  Definition radial_scale (theta : R) : R :=
    (R_param * scale_factor t + r_param * scale_factor t * cos theta).
  
  Definition Phi_t {n : nat} (theta : R) (u : unit_sphere n) : Rvec (S n) :=
    fun i =>
      match i with
      | 0 => r_param * scale_factor t * sin theta
      | S j => radial_scale theta * (proj1_sig u j)
      end.
  
  (** The radial scale is always positive when R > r *)
  Lemma radial_scale_positive : forall theta,
    radial_scale theta > 0.
  Proof.
    intro theta.
    unfold radial_scale, scale_factor.
    assert (H1: R_param * (1 - t) > 0).
    { apply Rmult_lt_0_compat; lra. }
    assert (H2: r_param * (1 - t) > 0).
    { apply Rmult_lt_0_compat; lra. }
    assert (H3: -1 <= cos theta <= 1).
    { split; apply cos_bound. }
    nra.
  Qed.
  
End HypertorusParametrization.

(** ** Section 5: Jacobian and Smoothness *)

(** The Jacobian determinant for the parametrization *)
Definition jacobian_det {n : nat} {kp : KakeyaParams} (t : R) (theta : R) : R :=
  (R_param * scale_factor t + r_param * scale_factor t * cos theta)^(n) * 
  r_param * scale_factor t.

Lemma jacobian_det_positive : 
  forall (n : nat) (kp : KakeyaParams) (t : R),
  contraction_param t ->
  forall theta, jacobian_det t theta > 0.
Proof.
  intros n kp t Ht theta.
  unfold jacobian_det, scale_factor.
  assert (H1: R_param * (1 - t) + r_param * (1 - t) * cos theta > 0).
  { 
    assert (Hcos: -1 <= cos theta <= 1) by (split; apply cos_bound).
    assert (Hpos: R_param * (1 - t) > 0).
    { apply Rmult_lt_0_compat; lra. }
    assert (Hpos2: r_param * (1 - t) > 0).
    { apply Rmult_lt_0_compat; lra. }
    nra.
  }
  assert (H2: r_param * (1 - t) > 0).
  { apply Rmult_lt_0_compat; lra. }
  apply pow_lt.
  lra.
Qed.

(** ** Section 6: Projection *)

(** Orthogonal projection π: R^(n+1) → R^n
    π(x_1, ..., x_n, x_{n+1}) = (x_1, ..., x_n) *)
Definition orth_projection {n : nat} (v : Rvec (S n)) : Rvec n :=
  fun i => v (S i).

(** ** Section 7: Line Segment Definition *)

(** A line segment in direction u with center x and half-length L *)
Definition line_segment {n : nat} (center : Rvec n) (direction : unit_sphere n) 
  (half_length : R) : Rvec n -> Prop :=
  fun p => exists s : R, -half_length <= s <= half_length /\
    p = vec_add center (vec_smul s (proj1_sig direction)).

(** Unit line segment: half-length = 1/2, so total length = 1 *)
Definition unit_line_segment {n : nat} (center : Rvec n) (direction : unit_sphere n) :=
  line_segment center direction (1/2).

(** ** Section 8: Kakeya Set Definition *)

(** A Kakeya set contains a unit line segment in every direction *)
Definition is_kakeya_set {n : nat} (E : Rvec n -> Prop) : Prop :=
  forall (u : unit_sphere n), exists (center : Rvec n),
    forall (p : Rvec n), unit_line_segment center u p -> E p.

(** ** Section 9: Helper Lemmas *)

(** Sum of squares for vector norm *)
Lemma vec_norm_sq_nonneg : forall {n : nat} (v : Rvec n),
  vec_norm_sq v >= 0.
Proof.
  intros n v.
  unfold vec_norm_sq, vec_dot.
  apply sum_f_R0_nonneg.
  intros i.
  apply Rle_0_sqr.
Qed.

Lemma vec_norm_nonneg : forall {n : nat} (v : Rvec n),
  vec_norm v >= 0.
Proof.
  intros n v.
  unfold vec_norm.
  apply sqrt_pos.
Qed.

(** Properties of unit sphere elements *)
Lemma unit_sphere_norm : forall {n : nat} (u : unit_sphere n),
  vec_norm_sq (proj1_sig u) = 1.
Proof.
  intros n u.
  exact (proj2_sig u).
Qed.

End KakeyaBase.
