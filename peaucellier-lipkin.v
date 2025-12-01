(******************************************************************************)
(*                                                                            *)
(*     Peaucellier-Lipkin Linkage: The First Exact Straight-Line Mechanism    *)
(*                                                                            *)
(*     Invented 1864 by Charles-Nicolas Peaucellier. The first planar         *)
(*     linkage capable of transforming rotary motion into perfect             *)
(*     straight-line motion via circle inversion geometry.                    *)
(*                                                                            *)
(*     "It is the most beautiful thing I have ever seen in my life."          *)
(*     - Lord Kelvin, upon seeing a model of the linkage (c. 1874)            *)
(*       (as recorded by J.J. Sylvester, Collected Works, Vol. 3)             *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 1, 2025                                                 *)
(*                                                                            *)
(******************************************************************************)

(** * Section 1: Imports and Foundational Setup *)

Require Import Reals.
Require Import Lra.
Require Import Psatz.
Open Scope R_scope.

(** * Section 2: Point Definitions and Basic Operations *)

(** A point in the Euclidean plane ℝ² *)
Definition Point : Type := R * R.

(** Projections *)
Definition px (P : Point) : R := fst P.
Definition py (P : Point) : R := snd P.

(** Point equality is decidable via real equality *)
Definition point_eq (P Q : Point) : Prop := px P = px Q /\ py P = py Q.

(** The origin *)
Definition origin : Point := (0, 0).

(** Point addition *)
Definition point_add (P Q : Point) : Point := (px P + px Q, py P + py Q).

(** Point subtraction *)
Definition point_sub (P Q : Point) : Point := (px P - px Q, py P - py Q).

(** Scalar multiplication *)
Definition point_scale (k : R) (P : Point) : Point := (k * px P, k * py P).

(** * Section 3: Distance Function and Properties *)

(** Squared distance - often easier to work with to avoid sqrt *)
Definition dist_sq (P Q : Point) : R :=
  (px Q - px P)² + (py Q - py P)².

(** Euclidean distance *)
Definition dist (P Q : Point) : R := sqrt (dist_sq P Q).

(** dist_sq is always non-negative *)
Lemma dist_sq_nonneg : forall P Q : Point, 0 <= dist_sq P Q.
Proof.
  intros P Q.
  unfold dist_sq.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(** dist is always non-negative *)
Lemma dist_nonneg : forall P Q : Point, 0 <= dist P Q.
Proof.
  intros P Q.
  unfold dist.
  apply sqrt_pos.
Qed.

(** dist_sq is symmetric *)
Lemma dist_sq_sym : forall P Q : Point, dist_sq P Q = dist_sq Q P.
Proof.
  intros P Q.
  unfold dist_sq.
  replace (px P - px Q) with (-(px Q - px P)) by lra.
  replace (py P - py Q) with (-(py Q - py P)) by lra.
  repeat rewrite <- Rsqr_neg.
  lra.
Qed.

(** dist is symmetric *)
Lemma dist_sym : forall P Q : Point, dist P Q = dist Q P.
Proof.
  intros P Q.
  unfold dist.
  rewrite dist_sq_sym.
  reflexivity.
Qed.

(** dist_sq P P = 0 *)
Lemma dist_sq_refl : forall P : Point, dist_sq P P = 0.
Proof.
  intros P.
  unfold dist_sq.
  replace (px P - px P) with 0 by lra.
  replace (py P - py P) with 0 by lra.
  unfold Rsqr. lra.
Qed.

(** dist P P = 0 *)
Lemma dist_refl : forall P : Point, dist P P = 0.
Proof.
  intros P.
  unfold dist.
  rewrite dist_sq_refl.
  apply sqrt_0.
Qed.

(** dist_sq = 0 implies points are equal *)
Lemma dist_sq_zero_iff : forall P Q : Point,
  dist_sq P Q = 0 <-> point_eq P Q.
Proof.
  intros P Q.
  unfold dist_sq, point_eq.
  split.
  - intros H.
    assert (Hsqr1_ge: (px Q - px P)² >= 0) by apply Rle_ge, Rle_0_sqr.
    assert (Hsqr2_ge: (py Q - py P)² >= 0) by apply Rle_ge, Rle_0_sqr.
    assert (Hsqr1: (px Q - px P)² = 0).
    { destruct Hsqr1_ge as [Hgt|Heq].
      - assert (0 < (px Q - px P)² + (py Q - py P)²).
        { apply Rplus_lt_le_0_compat.
          - lra.
          - apply Rle_0_sqr. }
        lra.
      - lra. }
    assert (Hsqr2: (py Q - py P)² = 0) by lra.
    apply Rsqr_eq_0 in Hsqr1.
    apply Rsqr_eq_0 in Hsqr2.
    lra.
  - intros [Hx Hy].
    rewrite Hx, Hy.
    replace (px Q - px Q) with 0 by lra.
    replace (py Q - py Q) with 0 by lra.
    unfold Rsqr. lra.
Qed.

(** dist = 0 iff points are equal *)
Lemma dist_zero_iff : forall P Q : Point,
  dist P Q = 0 <-> point_eq P Q.
Proof.
  intros P Q.
  unfold dist.
  split.
  - intros H.
    apply sqrt_eq_0 in H.
    + apply dist_sq_zero_iff. exact H.
    + apply dist_sq_nonneg.
  - intros H.
    apply dist_sq_zero_iff in H.
    rewrite H.
    apply sqrt_0.
Qed.

(** Squared distance from origin *)
Lemma dist_sq_from_origin : forall P : Point,
  dist_sq origin P = (px P)² + (py P)².
Proof.
  intros P.
  unfold dist_sq, origin, px, py. simpl.
  replace (fst P - 0) with (fst P) by lra.
  replace (snd P - 0) with (snd P) by lra.
  reflexivity.
Qed.

(** * Section 4: Collinearity *)

(** Three points are collinear if they lie on the same line.
    Equivalent to the cross product of vectors being zero:
    (Q - P) × (R - P) = 0 *)
Definition collinear (P Q R : Point) : Prop :=
  (px Q - px P) * (py R - py P) = (px R - px P) * (py Q - py P).

(** Collinearity is preserved under permutation *)
Lemma collinear_perm_12 : forall P Q R, collinear P Q R -> collinear Q P R.
Proof.
  intros P Q R H.
  unfold collinear in *.
  lra.
Qed.

Lemma collinear_perm_23 : forall P Q R, collinear P Q R -> collinear P R Q.
Proof.
  intros P Q R H.
  unfold collinear in *.
  lra.
Qed.

Lemma collinear_perm_cycle : forall P Q R, collinear P Q R -> collinear Q R P.
Proof.
  intros P Q R H.
  unfold collinear in *.
  lra.
Qed.

(** Any point is collinear with itself and another *)
Lemma collinear_refl_left : forall P Q, collinear P P Q.
Proof.
  intros P Q.
  unfold collinear.
  replace (px P - px P) with 0 by lra.
  replace (py P - py P) with 0 by lra.
  lra.
Qed.

Lemma collinear_refl_right : forall P Q, collinear P Q Q.
Proof.
  intros P Q.
  unfold collinear.
  lra.
Qed.

(** * Section 5: Lines *)

(** A line in implicit form: Ax + By + C = 0 with (A,B) ≠ (0,0) *)
Record Line : Type := mkLine {
  line_A : R;
  line_B : R;
  line_C : R
}.

(** A line is valid (non-degenerate) if A² + B² > 0 *)
Definition line_valid (L : Line) : Prop :=
  (line_A L)² + (line_B L)² > 0.

(** Point lies on line *)
Definition on_line (P : Point) (L : Line) : Prop :=
  line_A L * px P + line_B L * py P + line_C L = 0.

(** Construct a line through two distinct points *)
Definition line_through (P Q : Point) : Line :=
  mkLine (py Q - py P) (px P - px Q)
         ((py P - py Q) * px P + (px Q - px P) * py P).

(** Points on the line through them *)
Lemma point_on_line_through_left : forall P Q : Point,
  on_line P (line_through P Q).
Proof.
  intros P Q.
  unfold on_line, line_through, line_A, line_B, line_C, px, py. simpl.
  lra.
Qed.

Lemma point_on_line_through_right : forall P Q : Point,
  on_line Q (line_through P Q).
Proof.
  intros P Q.
  unfold on_line, line_through, line_A, line_B, line_C, px, py. simpl.
  lra.
Qed.

(** * Section 6: Circles *)

(** A circle with center and radius *)
Record Circle : Type := mkCircle {
  circle_center : Point;
  circle_radius : R
}.

(** Circle is valid (non-degenerate) if radius > 0 *)
Definition circle_valid (C : Circle) : Prop :=
  circle_radius C > 0.

(** Point lies on circle *)
Definition on_circle (P : Point) (C : Circle) : Prop :=
  dist P (circle_center C) = circle_radius C.

(** Point lies on circle (squared form, often easier) *)
Definition on_circle_sq (P : Point) (C : Circle) : Prop :=
  dist_sq P (circle_center C) = (circle_radius C)².

(** Equivalence of on_circle forms when radius >= 0 *)
Lemma on_circle_iff_sq : forall P C,
  circle_radius C >= 0 ->
  (on_circle P C <-> on_circle_sq P C).
Proof.
  intros P C Hradius.
  unfold on_circle, on_circle_sq, dist.
  split.
  - intros H.
    rewrite <- H.
    unfold Rsqr.
    rewrite sqrt_sqrt.
    + reflexivity.
    + apply dist_sq_nonneg.
  - intros H.
    rewrite H.
    apply sqrt_Rsqr.
    apply Rge_le. exact Hradius.
Qed.

(** Point inside circle *)
Definition inside_circle (P : Point) (C : Circle) : Prop :=
  dist P (circle_center C) < circle_radius C.

(** Point outside circle *)
Definition outside_circle (P : Point) (C : Circle) : Prop :=
  dist P (circle_center C) > circle_radius C.

(** Circle through a point with given center *)
Definition circle_through (center P : Point) : Circle :=
  mkCircle center (dist center P).

(** The defining point is on the circle *)
Lemma on_circle_through : forall center P,
  on_circle P (circle_through center P).
Proof.
  intros center P.
  unfold on_circle, circle_through, circle_center, circle_radius. simpl.
  apply dist_sym.
Qed.

(** * Section 7: Circle Inversion - Foundation *)

(** Circle inversion with center O and radius k:
    For a point P ≠ O, the inverse P' lies on ray OP such that |OP| * |OP'| = k².

    Explicitly: P' = O + (k² / |OP|²) * (P - O)

    This is well-defined when P ≠ O (i.e., dist O P > 0). *)

Definition invert_point (O : Point) (k : R) (P : Point) : Point :=
  let d_sq := dist_sq O P in
  let scale := (k * k) / d_sq in
  (px O + scale * (px P - px O), py O + scale * (py P - py O)).

(** * Section 7.1: Basic Helper Lemmas for Inversion *)

(** Helper: dist > 0 implies dist_sq > 0 *)
Lemma dist_pos_implies_dist_sq_pos : forall P Q : Point,
  dist P Q > 0 -> dist_sq P Q > 0.
Proof.
  intros P Q H.
  unfold dist in H.
  assert (Hnonneg: 0 <= dist_sq P Q) by apply dist_sq_nonneg.
  destruct (Rle_lt_or_eq_dec 0 (dist_sq P Q) Hnonneg) as [Hpos|Hzero].
  - exact Hpos.
  - rewrite <- Hzero in H.
    rewrite sqrt_0 in H.
    lra.
Qed.

(** Helper: dist_sq > 0 implies dist_sq ≠ 0 *)
Lemma dist_sq_pos_neq_0 : forall P Q : Point,
  dist_sq P Q > 0 -> dist_sq P Q <> 0.
Proof.
  intros P Q H.
  apply Rgt_not_eq. exact H.
Qed.

(** Helper: k > 0 implies k * k > 0 *)
Lemma k_pos_implies_ksq_pos : forall k : R,
  k > 0 -> k * k > 0.
Proof.
  intros k Hk.
  apply Rmult_lt_0_compat; exact Hk.
Qed.

(** Helper: a > 0 and b > 0 implies a / b > 0 *)
Lemma div_pos : forall a b : R,
  a > 0 -> b > 0 -> a / b > 0.
Proof.
  intros a b Ha Hb.
  apply Rdiv_lt_0_compat; assumption.
Qed.

(** Helper: dist_sq unfolds to raw form *)
Lemma dist_sq_unfold : forall O P : Point,
  dist_sq O P = (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O).
Proof.
  intros O P.
  unfold dist_sq, px, py, Rsqr.
  reflexivity.
Qed.

(** * Section 7.2: Inversion Product Lemmas *)

(** Key property: |OP|² * |OP'|² = k⁴ (squared version) *)
Lemma inversion_product_sq : forall O P k,
  dist O P > 0 -> k > 0 ->
  dist_sq O P * dist_sq O (invert_point O k P) = (k * k) * (k * k).
Proof.
  intros O P k Hdist Hk.
  assert (Hdsq_pos: dist_sq O P > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
  unfold invert_point, dist_sq, px, py, Rsqr. simpl.
  assert (Hdenom_neq: (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) <> 0).
  { apply Rgt_not_eq. exact Hdsq_pos. }
  field.
  exact Hdenom_neq.
Qed.

(** Key property: |OP| * |OP'| = k² *)
Lemma inversion_product : forall O P k,
  dist O P > 0 -> k > 0 ->
  dist O P * dist O (invert_point O k P) = k * k.
Proof.
  intros O P k Hdist Hk.
  assert (Hsq: dist_sq O P * dist_sq O (invert_point O k P) = (k * k) * (k * k))
    by (apply inversion_product_sq; assumption).
  assert (Hdsq_pos: dist_sq O P > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
  assert (Hdsq_inv_pos: dist_sq O (invert_point O k P) > 0).
  { assert (Hprod_pos: (k * k) * (k * k) > 0).
    { apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; exact Hk. }
    rewrite <- Hsq in Hprod_pos.
    destruct (Rle_lt_or_eq_dec 0 (dist_sq O (invert_point O k P))) as [H|H].
    - apply dist_sq_nonneg.
    - exact H.
    - rewrite <- H in Hprod_pos.
      rewrite Rmult_0_r in Hprod_pos.
      lra. }
  unfold dist.
  rewrite <- sqrt_mult.
  - rewrite Hsq.
    rewrite sqrt_mult.
    + rewrite sqrt_sqrt.
      * reflexivity.
      * apply Rmult_le_pos; left; exact Hk.
    + apply Rmult_le_pos; left; exact Hk.
    + apply Rmult_le_pos; left; exact Hk.
  - apply dist_sq_nonneg.
  - apply dist_sq_nonneg.
Qed.

(** * Section 7.3: Helper Lemmas for Involution Proof *)

(** The scale factor for inversion *)
Definition inversion_scale (O P : Point) (k : R) : R :=
  (k * k) / dist_sq O P.

(** Scale factor is positive when preconditions hold *)
Lemma inversion_scale_pos : forall O P k,
  dist O P > 0 -> k > 0 -> inversion_scale O P k > 0.
Proof.
  intros O P k Hdist Hk.
  unfold inversion_scale.
  apply div_pos.
  - apply k_pos_implies_ksq_pos. exact Hk.
  - apply dist_pos_implies_dist_sq_pos. exact Hdist.
Qed.

(** dist_sq of the inverted point in terms of scale *)
Lemma dist_sq_invert_scale : forall O P k,
  dist O P > 0 -> k > 0 ->
  dist_sq O (invert_point O k P) = (inversion_scale O P k) * (inversion_scale O P k) * dist_sq O P.
Proof.
  intros O P k Hdist Hk.
  assert (Hdsq_pos: dist_sq O P > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
  unfold invert_point, inversion_scale, dist_sq, px, py, Rsqr. simpl.
  assert (Hdenom_neq: (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) <> 0).
  { apply Rgt_not_eq. exact Hdsq_pos. }
  field.
  exact Hdenom_neq.
Qed.

(** Helper: the inverted point's squared distance simplifies *)
Lemma invert_dist_sq_form : forall O P k,
  dist O P > 0 -> k > 0 ->
  let denom := (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) in
  (fst O * denom + k * k * (fst P - fst O) - fst O * denom) *
  (fst O * denom + k * k * (fst P - fst O) - fst O * denom) +
  (snd O * denom + k * k * (snd P - snd O) - snd O * denom) *
  (snd O * denom + k * k * (snd P - snd O) - snd O * denom) =
  (k * k) * (k * k) * denom.
Proof.
  intros O P k Hdist Hk.
  simpl.
  ring.
Qed.

(** Helper: the inverted point's squared distance is nonzero *)
Lemma invert_dist_sq_neq_0 : forall O P k,
  dist O P > 0 -> k > 0 ->
  let denom := (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) in
  (fst O * denom + k * k * (fst P - fst O) - fst O * denom) *
  (fst O * denom + k * k * (fst P - fst O) - fst O * denom) +
  (snd O * denom + k * k * (snd P - snd O) - snd O * denom) *
  (snd O * denom + k * k * (snd P - snd O) - snd O * denom) <> 0.
Proof.
  intros O P k Hdist Hk.
  simpl.
  rewrite invert_dist_sq_form by assumption.
  assert (Hdsq_pos: dist_sq O P > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
  assert (Hdenom_pos: (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) > 0) by exact Hdsq_pos.
  assert (Hk4_pos: (k * k) * (k * k) > 0).
  { apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; exact Hk. }
  apply Rgt_not_eq.
  apply Rmult_lt_0_compat; [exact Hk4_pos | exact Hdenom_pos].
Qed.

(** The scale factor for double inversion *)
Lemma double_inversion_scale : forall O P k,
  dist O P > 0 -> k > 0 ->
  inversion_scale O (invert_point O k P) k * inversion_scale O P k = 1.
Proof.
  intros O P k Hdist Hk.
  assert (Hdsq_pos: dist_sq O P > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
  unfold inversion_scale, invert_point, dist_sq, px, py, Rsqr. simpl.
  assert (Hdenom_neq: (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) <> 0).
  { apply Rgt_not_eq. exact Hdsq_pos. }
  assert (Hdenom2_neq: (fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (fst P - fst O) -
                        fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) *
                       (fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (fst P - fst O) -
                        fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) +
                       (snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (snd P - snd O) -
                        snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) *
                       (snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (snd P - snd O) -
                        snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) <> 0).
  { apply (invert_dist_sq_neq_0 O P k Hdist Hk). }
  field.
  split; [exact Hdenom_neq | exact Hdenom2_neq].
Qed.

(** * Section 7.4: Involution Theorem *)

(** Inversion is an involution: inverting twice returns original point *)
Lemma inversion_involution : forall O P k,
  dist O P > 0 -> k > 0 ->
  point_eq (invert_point O k (invert_point O k P)) P.
Proof.
  intros O P k Hdist Hk.
  assert (Hdsq_pos: dist_sq O P > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
  unfold point_eq, invert_point, dist_sq, px, py, Rsqr. simpl.
  assert (Hdenom_neq: (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) <> 0).
  { apply Rgt_not_eq. exact Hdsq_pos. }
  assert (Hdenom2_neq: (fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (fst P - fst O) -
                        fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) *
                       (fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (fst P - fst O) -
                        fst O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) +
                       (snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (snd P - snd O) -
                        snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) *
                       (snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O)) +
                        k * k * (snd P - snd O) -
                        snd O * ((fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O))) <> 0).
  { apply (invert_dist_sq_neq_0 O P k Hdist Hk). }
  split.
  - field. split; [exact Hdenom_neq | exact Hdenom2_neq].
  - field. split; [exact Hdenom_neq | exact Hdenom2_neq].
Qed.

(** * Section 7.5: Collinearity of Inversion *)

(** P' lies on ray from O through P (collinearity) *)
Lemma inversion_collinear : forall O P k,
  dist O P > 0 -> k > 0 ->
  collinear O P (invert_point O k P).
Proof.
  intros O P k Hdist Hk.
  unfold collinear, invert_point, px, py. simpl.
  set (d_sq := dist_sq O P).
  set (scale := (k * k) / d_sq).
  replace (fst O + scale * (fst P - fst O) - fst O) with (scale * (fst P - fst O)) by lra.
  replace (snd O + scale * (snd P - snd O) - snd O) with (scale * (snd P - snd O)) by lra.
  ring.
Qed.

(** * Section 8: Circle Through Center Inverts to Line *)

(** This is the key theorem for the Peaucellier linkage:
    If a circle passes through the center of inversion O,
    then the image of that circle (minus O) under inversion is a straight line.

    Mathematical setup (using O at origin for clarity):
    - Circle with center M = (m, 0) and radius r = m (so O is on the circle)
    - Point P = (x, y) on circle satisfies: x² + y² = 2mx
    - Inverted point P' has x-coordinate: k²·x/(x²+y²) = k²·x/(2mx) = k²/(2m)
    - This is constant! So all P' lie on the vertical line x = k²/(2m)
*)

(** Circle passes through a point *)
Definition circle_passes_through (C : Circle) (P : Point) : Prop :=
  dist P (circle_center C) = circle_radius C.

(** A circle passes through O iff |center - O| = radius *)
Lemma circle_through_origin_char : forall C O,
  circle_passes_through C O <-> dist O (circle_center C) = circle_radius C.
Proof.
  intros C O.
  unfold circle_passes_through.
  rewrite dist_sym.
  tauto.
Qed.

(** Helper: squaring preserves equality for non-negative reals *)
Lemma sqrt_eq_implies_sq_eq : forall x y,
  0 <= x -> 0 <= y -> sqrt x = y -> x = y * y.
Proof.
  intros x y Hx Hy Heq.
  rewrite <- Heq.
  rewrite sqrt_sqrt; [reflexivity | exact Hx].
Qed.

(** Helper: For a point P on a circle through O, express |OP|² in terms of center *)
Lemma dist_sq_on_circle_through_origin : forall O M r P,
  let C := mkCircle M r in
  dist O M = r ->
  r > 0 ->
  circle_passes_through C P ->
  P <> O ->
  dist_sq O P = 2 * ((px M - px O) * (px P - px O) + (py M - py O) * (py P - py O)).
Proof.
  intros O M r P C HOM Hr HP HPneqO.
  unfold circle_passes_through in HP.
  simpl in HP.
  assert (Hdist_PM: dist P M = r) by exact HP.
  unfold dist in HOM, Hdist_PM.
  assert (Hrsq_OM: dist_sq O M = r * r).
  { apply sqrt_eq_implies_sq_eq.
    - apply dist_sq_nonneg.
    - left. exact Hr.
    - exact HOM. }
  assert (Hrsq_PM: dist_sq P M = r * r).
  { apply sqrt_eq_implies_sq_eq.
    - apply dist_sq_nonneg.
    - left. exact Hr.
    - exact Hdist_PM. }
  unfold dist_sq in *.
  unfold px, py in *.
  unfold Rsqr in *.
  lra.
Qed.

(** The key theorem: All points on a circle through O map to a common line.
    We state this as: the x-coordinate of P' is constant (determined by M and k).

    For the Peaucellier linkage, we'll use this result in a specialized form
    where we work with the specific linkage geometry. *)

(** For a circle through O with center on the positive x-axis from O,
    inverted points all have the same x-coordinate *)
Definition invert_target_x (O M : Point) (k : R) : R :=
  px O + (k * k) * (px M - px O) / (2 * ((px M - px O) * (px M - px O) + (py M - py O) * (py M - py O))).

(** The line that is the image of a circle through O *)
Definition inversion_image_line (O M : Point) (k : R) : Line :=
  let target_x := invert_target_x O M k in
  mkLine 1 0 (- target_x).

(** Points on the image line have constant x-coordinate *)
Lemma on_inversion_image_line_char : forall O M k P,
  on_line P (inversion_image_line O M k) <-> px P = invert_target_x O M k.
Proof.
  intros O M k P.
  unfold on_line, inversion_image_line, invert_target_x, line_A, line_B, line_C.
  simpl.
  unfold px, py.
  lra.
Qed.

(** * Section 8.1: The Circle-to-Line Theorem (Strengthened) *)

(** The key mathematical insight:
    For a circle C through O with center M, any point P on C satisfies:
      |OP|² = 2 * ((M-O) · (P-O))
    where · denotes dot product.

    For the inverted point P':
      (M-O) · (P'-O) = k²/2  (constant!)

    This means all P' lie on a LINE perpendicular to (M-O). *)

(** Dot product of two displacement vectors from a common origin *)
Definition dot_product_from (O P Q : Point) : R :=
  (px P - px O) * (px Q - px O) + (py P - py O) * (py Q - py O).

(** Dot product is symmetric *)
Lemma dot_product_from_sym : forall O P Q,
  dot_product_from O P Q = dot_product_from O Q P.
Proof.
  intros O P Q.
  unfold dot_product_from.
  ring.
Qed.

(** Dot product with self gives squared distance *)
Lemma dot_product_from_self : forall O P,
  dot_product_from O P P = dist_sq O P.
Proof.
  intros O P.
  unfold dot_product_from, dist_sq, px, py, Rsqr.
  ring.
Qed.

(** The line perpendicular to direction (M-O) at distance k²/(2|OM|²) projected *)
Definition circle_inversion_image_line (O M : Point) (k : R) : Line :=
  mkLine (px M - px O) (py M - py O)
         (- (px M - px O) * px O - (py M - py O) * py O - (k * k) / 2).

(** Helper: Check if a point is on the perpendicular line *)
Definition on_perp_line (O M : Point) (k : R) (P : Point) : Prop :=
  dot_product_from O M P = (k * k) / 2.

(** The perpendicular line characterization matches our definition *)
Lemma circle_inversion_image_line_char : forall O M k P,
  on_line P (circle_inversion_image_line O M k) <-> on_perp_line O M k P.
Proof.
  intros O M k P.
  unfold on_line, circle_inversion_image_line, on_perp_line, dot_product_from.
  unfold line_A, line_B, line_C, px, py. simpl.
  split; intros H; lra.
Qed.

(** Helper: Simplify the dot product of inverted point *)
Lemma invert_dot_product_formula : forall O M k P,
  dist_sq O P > 0 ->
  dist_sq O P = 2 * dot_product_from O M P ->
  dot_product_from O M (invert_point O k P) = k * k / 2.
Proof.
  intros O M k P Hdsq_pos Hdsq_eq.
  unfold dot_product_from, invert_point, dist_sq, px, py, Rsqr in *.
  simpl.
  assert (Hdenom_neq: (fst P - fst O) * (fst P - fst O) + (snd P - snd O) * (snd P - snd O) <> 0).
  { apply Rgt_not_eq. exact Hdsq_pos. }
  assert (Hdot_pos: (fst M - fst O) * (fst P - fst O) + (snd M - snd O) * (snd P - snd O) > 0).
  { lra. }
  assert (Hdot_neq: (fst M - fst O) * (fst P - fst O) + (snd M - snd O) * (snd P - snd O) <> 0).
  { lra. }
  rewrite Hdsq_eq.
  field.
  exact Hdot_neq.
Qed.

(** KEY LEMMA: Inverted point satisfies the perpendicular line condition *)
Lemma invert_on_perp_line : forall O M r k P,
  let C := mkCircle M r in
  dist O M = r ->
  r > 0 ->
  k > 0 ->
  circle_passes_through C P ->
  dist O P > 0 ->
  on_perp_line O M k (invert_point O k P).
Proof.
  intros O M r k P C HOM Hr Hk HP Hdist.
  unfold on_perp_line.
  assert (Hdsq_pos: dist_sq O P > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
  assert (HPneqO: P <> O).
  { intros Heq. rewrite Heq in Hdist. rewrite dist_refl in Hdist. lra. }
  assert (Hdsq_eq: dist_sq O P = 2 * dot_product_from O M P).
  { unfold dot_product_from.
    apply dist_sq_on_circle_through_origin with (r := r); assumption. }
  apply invert_dot_product_formula; assumption.
Qed.

(** MAIN THEOREM: Inverted point lies on the image line *)
Theorem circle_through_O_inverts_to_line : forall O M r k P,
  let C := mkCircle M r in
  dist O M = r ->
  r > 0 ->
  k > 0 ->
  circle_passes_through C P ->
  dist O P > 0 ->
  on_line (invert_point O k P) (circle_inversion_image_line O M k).
Proof.
  intros O M r k P C HOM Hr Hk HP Hdist.
  apply circle_inversion_image_line_char.
  apply invert_on_perp_line with (r := r); assumption.
Qed.

(** * Section 9: Rhombus Properties and the Peaucellier Inversor *)

(** The Peaucellier linkage uses a rhombus ABCD where:
    - All four sides have equal length s: |AB| = |BC| = |CD| = |DA| = s
    - Two arms connect pivot O to opposite vertices A and C: |OA| = |OC| = L
    - The symmetry (|OA| = |OC|) forces O, B, D to be collinear
    - B and D are the other pair of opposite vertices

    The key property is: |OB| * |OD| = L² - s²
    This makes the rhombus act as a circle inversor with radius k = sqrt(L² - s²)! *)

(** * Section 9.1: Basic Definitions *)

(** Midpoint of two points *)
Definition midpoint (P Q : Point) : Point :=
  ((px P + px Q) / 2, (py P + py Q) / 2).

(** Midpoint lemmas *)
Lemma midpoint_comm : forall P Q, midpoint P Q = midpoint Q P.
Proof.
  intros P Q.
  unfold midpoint, px, py.
  f_equal; lra.
Qed.

Lemma midpoint_px : forall P Q, px (midpoint P Q) = (px P + px Q) / 2.
Proof.
  intros P Q. unfold midpoint, px. simpl. reflexivity.
Qed.

Lemma midpoint_py : forall P Q, py (midpoint P Q) = (py P + py Q) / 2.
Proof.
  intros P Q. unfold midpoint, py. simpl. reflexivity.
Qed.

(** * Section 9.2: Rhombus Configuration *)

(** For the Peaucellier linkage, we define the configuration directly
    rather than abstractly. This makes the algebraic proofs cleaner.

    Configuration:
    - O: fixed pivot point
    - A, C: endpoints of long arms from O (opposite vertices of rhombus)
    - B, D: other opposite vertices of rhombus
    - L: length of arms OA and OC
    - s: side length of rhombus *)

Record PeaucellierLinkage : Type := mkPeaucellier {
  pl_O : Point;
  pl_A : Point;
  pl_B : Point;
  pl_C : Point;
  pl_D : Point;
  pl_L : R;
  pl_s : R
}.

(** The linkage is valid when all constraints are satisfied *)
Definition linkage_valid (P : PeaucellierLinkage) : Prop :=
  dist (pl_O P) (pl_A P) = pl_L P /\
  dist (pl_O P) (pl_C P) = pl_L P /\
  dist (pl_A P) (pl_B P) = pl_s P /\
  dist (pl_B P) (pl_C P) = pl_s P /\
  dist (pl_C P) (pl_D P) = pl_s P /\
  dist (pl_D P) (pl_A P) = pl_s P /\
  pl_L P > pl_s P /\
  pl_s P > 0.

(** Squared version - more useful for algebraic proofs *)
Definition linkage_valid_sq (P : PeaucellierLinkage) : Prop :=
  dist_sq (pl_O P) (pl_A P) = (pl_L P) * (pl_L P) /\
  dist_sq (pl_O P) (pl_C P) = (pl_L P) * (pl_L P) /\
  dist_sq (pl_A P) (pl_B P) = (pl_s P) * (pl_s P) /\
  dist_sq (pl_B P) (pl_C P) = (pl_s P) * (pl_s P) /\
  dist_sq (pl_C P) (pl_D P) = (pl_s P) * (pl_s P) /\
  dist_sq (pl_D P) (pl_A P) = (pl_s P) * (pl_s P) /\
  pl_L P > pl_s P /\
  pl_s P > 0.

(** Valid implies valid_sq *)
Lemma linkage_valid_implies_sq : forall P,
  linkage_valid P -> linkage_valid_sq P.
Proof.
  intros P [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  unfold linkage_valid_sq.
  repeat split; try assumption.
  - unfold dist in HOA.
    assert (H: sqrt (dist_sq (pl_O P) (pl_A P)) = pl_L P) by exact HOA.
    apply sqrt_eq_implies_sq_eq in H.
    + rewrite H. reflexivity.
    + apply dist_sq_nonneg.
    + left. lra.
  - unfold dist in HOC.
    assert (H: sqrt (dist_sq (pl_O P) (pl_C P)) = pl_L P) by exact HOC.
    apply sqrt_eq_implies_sq_eq in H.
    + rewrite H. reflexivity.
    + apply dist_sq_nonneg.
    + left. lra.
  - unfold dist in HAB.
    assert (H: sqrt (dist_sq (pl_A P) (pl_B P)) = pl_s P) by exact HAB.
    apply sqrt_eq_implies_sq_eq in H.
    + rewrite H. reflexivity.
    + apply dist_sq_nonneg.
    + left. exact Hs.
  - unfold dist in HBC.
    assert (H: sqrt (dist_sq (pl_B P) (pl_C P)) = pl_s P) by exact HBC.
    apply sqrt_eq_implies_sq_eq in H.
    + rewrite H. reflexivity.
    + apply dist_sq_nonneg.
    + left. exact Hs.
  - unfold dist in HCD.
    assert (H: sqrt (dist_sq (pl_C P) (pl_D P)) = pl_s P) by exact HCD.
    apply sqrt_eq_implies_sq_eq in H.
    + rewrite H. reflexivity.
    + apply dist_sq_nonneg.
    + left. exact Hs.
  - unfold dist in HDA.
    assert (H: sqrt (dist_sq (pl_D P) (pl_A P)) = pl_s P) by exact HDA.
    apply sqrt_eq_implies_sq_eq in H.
    + rewrite H. reflexivity.
    + apply dist_sq_nonneg.
    + left. exact Hs.
Qed.

(** * Section 9.3: Equal Arms Force Collinearity *)

(** When |OA| = |OC|, point O lies on the perpendicular bisector of segment AC.
    For a rhombus where A and C are opposite vertices, the perpendicular
    bisector of AC passes through B and D.
    Therefore O, B, D are collinear. *)

Lemma equal_arms_perpendicular : forall O A C,
  dist O A = dist O C ->
  (px A - px C) * (px O - (px A + px C)/2) +
  (py A - py C) * (py O - (py A + py C)/2) = 0.
Proof.
  intros O A C Heq.
  unfold dist in Heq.
  assert (Hsq: dist_sq O A = dist_sq O C).
  { apply sqrt_inj in Heq; [exact Heq | apply dist_sq_nonneg | apply dist_sq_nonneg]. }
  unfold dist_sq, px, py, Rsqr in *.
  lra.
Qed.

(** * Section 9.5: The Product Formula Setup *)

(** We'll prove the product formula |OB| * |OD| = L² - s² using coordinates.

    Key insight: In a valid Peaucellier configuration where O, B, D are collinear,
    we can place coordinates with:
    - O at origin
    - B and D on the positive x-axis
    - A and C symmetric about the x-axis

    The algebra then gives us the product formula directly. *)

(** For algebraic convenience, we work with the squared product formula:
    |OB|² * |OD|² = (L² - s²)²
    which factors as |OB| * |OD| = L² - s² when all quantities are positive *)

(** Helper: expand dist_sq in terms of coordinates *)
Lemma dist_sq_coords : forall P Q,
  dist_sq P Q = (fst Q - fst P) * (fst Q - fst P) + (snd Q - snd P) * (snd Q - snd P).
Proof.
  intros P Q.
  unfold dist_sq, px, py, Rsqr.
  reflexivity.
Qed.

(** * Section 9.6: The Collinearity Condition *)

(** O, B, D are collinear *)
Definition OBD_collinear (P : PeaucellierLinkage) : Prop :=
  collinear (pl_O P) (pl_B P) (pl_D P).

(** A and C are symmetric about line OBD.
    When O is at origin and B, D on x-axis, this means A and C have same
    x-coordinate and opposite y-coordinates. *)
Definition AC_symmetric (P : PeaucellierLinkage) : Prop :=
  px (pl_A P) = px (pl_C P) /\
  py (pl_A P) = - py (pl_C P).

(** The full geometric configuration we need *)
Definition linkage_geometric (P : PeaucellierLinkage) : Prop :=
  linkage_valid_sq P /\
  OBD_collinear P /\
  AC_symmetric P /\
  px (pl_O P) = 0 /\ py (pl_O P) = 0 /\
  py (pl_B P) = 0 /\ py (pl_D P) = 0 /\
  px (pl_B P) > 0 /\ px (pl_D P) > px (pl_B P).

(** * Section 9.7: The Product Formula - Coordinate Version *)

(** When the linkage is in standard position (O at origin, B and D on x-axis),
    we can compute the product directly. *)

(** Simplified product formula for standard position *)
Lemma product_formula_standard : forall O A B C D L s,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  fst B > 0 -> fst D > fst B ->
  fst A = fst C ->
  snd A = - snd C ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  fst B * fst D = L * L - s * s.
Proof.
  intros O A B C D L s.
  intros HO1 HO2 HB2 HD2 HBpos HDBord HAC1 HAC2.
  intros HOA HOC HAB HBC HCD HDA HLs Hs.
  unfold dist_sq, px, py, Rsqr in *.
  rewrite HO1, HO2, HB2, HD2 in *.
  assert (HAmid: fst A = (fst B + fst D) / 2).
  { assert (Heq1: (fst A - fst B) * (fst A - fst B) + snd A * snd A = s * s).
    { replace ((fst A - fst B) * (fst A - fst B)) with ((fst B - fst A) * (fst B - fst A)) by ring.
      nra. }
    assert (Heq2: (fst A - fst D) * (fst A - fst D) + snd A * snd A = s * s).
    { replace ((fst A - fst D) * (fst A - fst D)) with ((fst D - fst A) * (fst D - fst A)) by ring.
      nra. }
    assert (Hsides: (fst A - fst B) * (fst A - fst B) = (fst A - fst D) * (fst A - fst D)) by nra.
    assert (Hdiff: (fst A - fst B) = fst D - fst A \/ fst A - fst B = fst A - fst D).
    { apply Rsqr_eq in Hsides. unfold Rsqr in Hsides. lra. }
    destruct Hdiff as [H1 | H2].
    - lra.
    - assert (fst B = fst D) by lra. lra. }
  assert (Hp: (fst D - fst B) / 2 * ((fst D - fst B) / 2) + snd A * snd A = s * s).
  { replace (fst A) with ((fst B + fst D) / 2) in HAB by (symmetry; exact HAmid).
    nra. }
  assert (HOAexp: fst A * fst A + snd A * snd A = L * L).
  { nra. }
  rewrite HAmid in HOAexp.
  assert (Hprod: fst B * fst D =
                 ((fst B + fst D)/2) * ((fst B + fst D)/2) -
                 ((fst D - fst B)/2) * ((fst D - fst B)/2)).
  { field. }
  rewrite Hprod.
  assert (Hgoal: ((fst B + fst D) / 2) * ((fst B + fst D) / 2) + snd A * snd A -
                 (((fst D - fst B) / 2) * ((fst D - fst B) / 2) + snd A * snd A) =
                 L * L - s * s).
  { lra. }
  lra.
Qed.

(** * Section 9.8: Main Inversor Theorem *)

(** The main theorem: For a valid Peaucellier linkage in standard position,
    the product |OB| * |OD| equals L² - s². *)

Theorem peaucellier_product_formula : forall P,
  linkage_geometric P ->
  dist_sq (pl_O P) (pl_B P) * dist_sq (pl_O P) (pl_D P) =
  ((pl_L P) * (pl_L P) - (pl_s P) * (pl_s P)) *
  ((pl_L P) * (pl_L P) - (pl_s P) * (pl_s P)).
Proof.
  intros P [Hvalid [Hcol [Hsym [HO1 [HO2 [HB2 [HD2 [HBpos HDBord]]]]]]]].
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  destruct Hsym as [HACx HACy].
  assert (Hprod: fst (pl_B P) * fst (pl_D P) = pl_L P * pl_L P - pl_s P * pl_s P).
  { apply product_formula_standard with
      (O := pl_O P) (A := pl_A P) (B := pl_B P) (C := pl_C P) (D := pl_D P)
      (L := pl_L P) (s := pl_s P).
    - exact HO1.
    - exact HO2.
    - exact HB2.
    - exact HD2.
    - exact HBpos.
    - exact HDBord.
    - unfold px in HACx. exact HACx.
    - unfold py in HACy. exact HACy.
    - unfold dist_sq, px, py, Rsqr. exact HOA.
    - unfold dist_sq, px, py, Rsqr. exact HOC.
    - unfold dist_sq, px, py, Rsqr. exact HAB.
    - unfold dist_sq, px, py, Rsqr. exact HBC.
    - unfold dist_sq, px, py, Rsqr. exact HCD.
    - unfold dist_sq, px, py, Rsqr. exact HDA.
    - exact HLs.
    - exact Hs. }
  unfold dist_sq, px, py, Rsqr.
  unfold px, py in HO1, HO2, HB2, HD2.
  rewrite HO1, HO2, HB2, HD2.
  nra.
Qed.

(** * Section 10: The Main Theorem - Peaucellier Straight-Line Motion *)

(** The inversion radius squared for the linkage *)
Definition linkage_k_sq (P : PeaucellierLinkage) : R :=
  (pl_L P) * (pl_L P) - (pl_s P) * (pl_s P).

(** The inversion radius (assuming L > s) *)
Definition linkage_k (P : PeaucellierLinkage) : R :=
  sqrt (linkage_k_sq P).

(** k² > 0 when L > s and s > 0 *)
Lemma linkage_k_sq_pos : forall P,
  pl_L P > pl_s P -> pl_s P > 0 ->
  linkage_k_sq P > 0.
Proof.
  intros P HLs Hs.
  unfold linkage_k_sq.
  nra.
Qed.

(** k > 0 when L > s and s > 0 *)
Lemma linkage_k_pos : forall P,
  pl_L P > pl_s P -> pl_s P > 0 ->
  linkage_k P > 0.
Proof.
  intros P HLs Hs.
  unfold linkage_k.
  apply sqrt_lt_R0.
  apply linkage_k_sq_pos; assumption.
Qed.

(** The constraint that B lies on a circle through O *)
Definition B_on_circle_through_O (P : PeaucellierLinkage) (M : Point) (r : R) : Prop :=
  let C := mkCircle M r in
  dist (pl_O P) M = r /\
  r > 0 /\
  circle_passes_through C (pl_B P).

(** D satisfies the perpendicular line condition for the inversion image.
    This is the key fact that connects the product formula to the line theorem.

    The center M of the circle through O must satisfy: |BM| = |OM| (B is on circle).
    In standard position with O at origin and B on x-axis at (Bx, 0):
    - Circle through O with center M = (Mx, My) has radius |OM| = sqrt(Mx² + My²)
    - B on circle means |BM| = |OM|, so (Bx - Mx)² + My² = Mx² + My²
    - This gives Bx = 2Mx (taking the positive solution since Bx > 0)
    - So Mx = Bx/2 and the dot product (M-O)·(D-O) = Mx·Dx = (Bx/2)·Dx = k²/2 *)

Lemma linkage_D_on_perp_line : forall P M r,
  linkage_geometric P ->
  B_on_circle_through_O P M r ->
  dist (pl_O P) (pl_B P) > 0 ->
  on_perp_line (pl_O P) M (linkage_k P) (pl_D P).
Proof.
  intros P M r Hgeom HBcirc HdistB.
  destruct HBcirc as [HOM [Hr HBonC]].
  destruct Hgeom as [Hvalid [Hcol [Hsym [HO1 [HO2 [HB2 [HD2 [HBpos HDBord]]]]]]]].
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  destruct Hsym as [HACx HACy].
  unfold on_perp_line, dot_product_from, linkage_k, linkage_k_sq, px, py.
  unfold px, py in HO1, HO2, HD2, HBpos, HDBord.
  rewrite HO1, HO2, HD2.
  assert (Hprod: fst (pl_B P) * fst (pl_D P) = pl_L P * pl_L P - pl_s P * pl_s P).
  { apply product_formula_standard with
      (O := pl_O P) (A := pl_A P) (B := pl_B P) (C := pl_C P) (D := pl_D P)
      (L := pl_L P) (s := pl_s P).
    - exact HO1.
    - exact HO2.
    - unfold py in HB2. exact HB2.
    - exact HD2.
    - exact HBpos.
    - exact HDBord.
    - unfold px in HACx. exact HACx.
    - unfold py in HACy. exact HACy.
    - unfold dist_sq, px, py, Rsqr. exact HOA.
    - unfold dist_sq, px, py, Rsqr. exact HOC.
    - unfold dist_sq, px, py, Rsqr. exact HAB.
    - unfold dist_sq, px, py, Rsqr. exact HBC.
    - unfold dist_sq, px, py, Rsqr. exact HCD.
    - unfold dist_sq, px, py, Rsqr. exact HDA.
    - exact HLs.
    - exact Hs. }
  assert (Hksq_pos: pl_L P * pl_L P - pl_s P * pl_s P > 0) by nra.
  unfold circle_passes_through, dist in HBonC, HOM.
  unfold dist_sq, px, py, Rsqr in HBonC, HOM.
  rewrite HO1, HO2 in HOM.
  unfold py in HB2. rewrite HB2 in HBonC.
  simpl in HBonC.
  assert (Hr_sq: (fst M - 0) * (fst M - 0) + (snd M - 0) * (snd M - 0) = r * r).
  { apply sqrt_eq_implies_sq_eq.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    - left. exact Hr.
    - exact HOM. }
  assert (HBM_sq: (fst M - fst (pl_B P)) * (fst M - fst (pl_B P)) +
                 (snd M - 0) * (snd M - 0) = r * r).
  { apply sqrt_eq_implies_sq_eq.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    - left. exact Hr.
    - exact HBonC. }
  assert (HMx_eq: fst M - 0 = fst (pl_B P) / 2).
  { assert (Heq: (fst M - fst (pl_B P)) * (fst M - fst (pl_B P)) =
                 (fst M - 0) * (fst M - 0)).
    { nra. }
    apply Rsqr_eq in Heq. unfold Rsqr in Heq.
    destruct Heq as [Hpos | Hneg].
    - assert (fst (pl_B P) = 0) by lra. lra.
    - lra. }
  rewrite sqrt_sqrt by lra.
  rewrite HMx_eq.
  rewrite <- Hprod.
  field; lra.
Qed.

(** ========== THE MAIN THEOREM ========== *)
(**
    Peaucellier-Lipkin Linkage Straight-Line Theorem:

    If:
    - The linkage is in valid geometric configuration
    - B moves on a circle that passes through the pivot O
    - B is not at O (the mechanism is not at singularity)

    Then:
    - D lies on a straight line perpendicular to the line through O and
      the circle's center

    This is the first exact straight-line mechanism in history (1864).
*)

Theorem peaucellier_straight_line : forall P M r,
  linkage_geometric P ->
  B_on_circle_through_O P M r ->
  dist (pl_O P) (pl_B P) > 0 ->
  on_line (pl_D P) (circle_inversion_image_line (pl_O P) M (linkage_k P)).
Proof.
  intros P M r Hgeom HBcirc HdistB.
  apply circle_inversion_image_line_char.
  apply linkage_D_on_perp_line with (r := r); assumption.
Qed.

(** * Section 11: Generalization to Arbitrary Position *)

(** The previous sections proved the theorem for linkages in "standard position"
    (O at origin, B and D on x-axis). Here we generalize to arbitrary position
    by proving the key facts are coordinate-invariant.

    Strategy:
    1. Define a general validity condition without coordinate constraints
    2. Prove the product formula using purely distance-based reasoning
    3. The main theorem follows from the coordinate-free inversion theory *)

(** * Section 11.1: General Linkage Validity *)

(** A linkage is valid in general position when the distance constraints hold *)
Definition linkage_valid_general (P : PeaucellierLinkage) : Prop :=
  dist (pl_O P) (pl_A P) = pl_L P /\
  dist (pl_O P) (pl_C P) = pl_L P /\
  dist (pl_A P) (pl_B P) = pl_s P /\
  dist (pl_B P) (pl_C P) = pl_s P /\
  dist (pl_C P) (pl_D P) = pl_s P /\
  dist (pl_D P) (pl_A P) = pl_s P /\
  pl_L P > pl_s P /\
  pl_s P > 0.

(** Squared version for algebraic convenience *)
Definition linkage_valid_general_sq (P : PeaucellierLinkage) : Prop :=
  dist_sq (pl_O P) (pl_A P) = (pl_L P)² /\
  dist_sq (pl_O P) (pl_C P) = (pl_L P)² /\
  dist_sq (pl_A P) (pl_B P) = (pl_s P)² /\
  dist_sq (pl_B P) (pl_C P) = (pl_s P)² /\
  dist_sq (pl_C P) (pl_D P) = (pl_s P)² /\
  dist_sq (pl_D P) (pl_A P) = (pl_s P)² /\
  pl_L P > pl_s P /\
  pl_s P > 0.

(** Convert from general validity to squared form *)
Lemma linkage_valid_general_to_sq : forall P,
  linkage_valid_general P -> linkage_valid_general_sq P.
Proof.
  intros P [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  unfold linkage_valid_general_sq, Rsqr.
  repeat split; try assumption.
  - unfold dist in HOA.
    apply sqrt_eq_implies_sq_eq in HOA; [| apply dist_sq_nonneg | left; lra].
    exact HOA.
  - unfold dist in HOC.
    apply sqrt_eq_implies_sq_eq in HOC; [| apply dist_sq_nonneg | left; lra].
    exact HOC.
  - unfold dist in HAB.
    apply sqrt_eq_implies_sq_eq in HAB; [| apply dist_sq_nonneg | left; exact Hs].
    exact HAB.
  - unfold dist in HBC.
    apply sqrt_eq_implies_sq_eq in HBC; [| apply dist_sq_nonneg | left; exact Hs].
    exact HBC.
  - unfold dist in HCD.
    apply sqrt_eq_implies_sq_eq in HCD; [| apply dist_sq_nonneg | left; exact Hs].
    exact HCD.
  - unfold dist in HDA.
    apply sqrt_eq_implies_sq_eq in HDA; [| apply dist_sq_nonneg | left; exact Hs].
    exact HDA.
Qed.

(** * Section 11.2: Rhombus Diagonal Properties *)

(** In a rhombus ABCD, the diagonals bisect each other.
    Let M be the common midpoint. Key facts:
    - |AM|² + |BM|² = |AB|² (Pythagorean theorem, diagonals perpendicular)
    - For the Peaucellier linkage: A and C are opposite, B and D are opposite *)

(** The midpoint of two points *)
Definition diagonal_midpoint (A C : Point) : Point := midpoint A C.

(** Squared distance from midpoint to vertex *)
Lemma midpoint_dist_sq_half : forall A C : Point,
  dist_sq A (midpoint A C) = dist_sq A C / 4.
Proof.
  intros A C.
  unfold midpoint, dist_sq, px, py, Rsqr. simpl.
  field.
Qed.

(** For a rhombus, opposite vertices have their midpoints coincide.
    We express this as: if ABCD has |AB|=|BC|=|CD|=|DA|, then
    midpoint(A,C) = midpoint(B,D) *)

(** Helper: squared half-diagonal in terms of side and other half-diagonal *)
Lemma rhombus_pythagorean : forall A B C D s,
  dist_sq A B = s² ->
  dist_sq B C = s² ->
  dist_sq C D = s² ->
  dist_sq D A = s² ->
  let M := midpoint A C in
  midpoint B D = M ->
  dist_sq A M + dist_sq B M = s².
Proof.
  intros A B C D s HAB HBC HCD HDA M HMeq.
  unfold M, midpoint, dist_sq, px, py, Rsqr in *. simpl in *.
  injection HMeq as Hx Hy.
  nra.
Qed.

