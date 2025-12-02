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

(** The constraint that B lies on a circle through O.

    Physical interpretation: In the complete Peaucellier-Lipkin mechanism,
    there is a SECOND fixed pivot point M (in addition to O). A crank arm
    of length r = |MO| connects M to B. Since B is constrained to be
    distance r from M, and O is also distance r from M, point B traces
    a circle that passes through O.

    This second pivot is what converts rotary input (turning the crank)
    into the straight-line output at D. Without it, B could move freely
    and D would not trace a line.

    M = center of input circle (second fixed pivot)
    r = radius of input circle = |MO| = |MB|
*)
Definition B_on_circle_through_O (P : PeaucellierLinkage) (M : Point) (r : R) : Prop :=
  let C := mkCircle M r in
  dist (pl_O P) M = r /\
  r > 0 /\
  circle_passes_through C (pl_B P).

(** The second pivot as an explicit link constraint *)
Definition second_pivot_constraint (O B M : Point) (r : R) : Prop :=
  dist O M = r /\
  dist B M = r /\
  r > 0.

(** The second pivot constraint implies B is on a circle through O *)
Lemma second_pivot_implies_circle : forall O B M r,
  second_pivot_constraint O B M r ->
  let C := mkCircle M r in
  dist O M = r /\ r > 0 /\ circle_passes_through C B.
Proof.
  intros O B M r [HOM [HBM Hr]].
  split; [exact HOM |].
  split; [exact Hr |].
  unfold circle_passes_through, circle_center, circle_radius. simpl.
  rewrite dist_sym. rewrite dist_sym in HBM. exact HBM.
Qed.

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

(** Parallelogram midpoint theorem: In a parallelogram, diagonals bisect each other.
    A parallelogram has opposite sides equal: |AB| = |DC| and |AD| = |BC|.
    For a rhombus (all sides equal), this is automatically satisfied. *)

Lemma parallelogram_midpoints_coincide : forall A B C D : Point,
  px B - px A = px C - px D ->
  py B - py A = py C - py D ->
  midpoint A C = midpoint B D.
Proof.
  intros A B C D Hx Hy.
  unfold midpoint, px, py.
  unfold Point in *.
  destruct A as [ax ay], B as [bx b_y], C as [cx c_y], D as [dx d_y].
  simpl in *.
  f_equal; lra.
Qed.

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

(** Point lies on perpendicular bisector of segment iff equidistant from endpoints *)
Lemma on_perp_bisector_iff_equidistant : forall P A C : Point,
  dist P A = dist P C <-> dist_sq P A = dist_sq P C.
Proof.
  intros P A C.
  unfold dist.
  split.
  - intros H.
    apply sqrt_inj in H; [exact H | apply dist_sq_nonneg | apply dist_sq_nonneg].
  - intros H.
    rewrite H. reflexivity.
Qed.

(** In a rhombus ABCD, vertex B is equidistant from A and C *)
Lemma rhombus_B_equidistant_AC : forall A B C s,
  dist_sq A B = s² ->
  dist_sq B C = s² ->
  dist_sq B A = dist_sq B C.
Proof.
  intros A B C s HAB HBC.
  rewrite dist_sq_sym.
  rewrite HAB, HBC.
  reflexivity.
Qed.

(** In a rhombus ABCD, vertex D is equidistant from A and C *)
Lemma rhombus_D_equidistant_AC : forall A C D s,
  dist_sq C D = s² ->
  dist_sq D A = s² ->
  dist_sq D A = dist_sq D C.
Proof.
  intros A C D s HCD HDA.
  rewrite HDA.
  rewrite dist_sq_sym.
  rewrite HCD.
  reflexivity.
Qed.

(** Characterization of perpendicular bisector via equidistance (squared form) *)
Lemma on_perp_bisector_eq : forall P A C,
  dist_sq P A = dist_sq P C ->
  (px A - px C) * (px P - (px A + px C)/2) +
  (py A - py C) * (py P - (py A + py C)/2) = 0.
Proof.
  intros P A C Heq.
  unfold dist_sq, px, py, Rsqr in *.
  lra.
Qed.

(** Helper: points on the same line ax + by = c are collinear *)
Lemma points_on_line_collinear : forall P Q R a b,
  a <> 0 \/ b <> 0 ->
  a * fst P + b * snd P = a * fst Q + b * snd Q ->
  a * fst P + b * snd P = a * fst R + b * snd R ->
  (fst Q - fst P) * (snd R - snd P) = (fst R - fst P) * (snd Q - snd P).
Proof.
  intros P Q R a b Hab HPQ HPR.
  set (u := fst P - fst Q).
  set (v := snd P - snd Q).
  set (x := fst P - fst R).
  set (y := snd P - snd R).
  assert (Hline1: a * u + b * v = 0) by (unfold u, v; lra).
  assert (Hline2: a * x + b * y = 0) by (unfold x, y; lra).
  assert (Hkey_a: a * (u * y - x * v) = 0).
  { assert (Hau: a * u = - b * v) by lra.
    assert (Hax: a * x = - b * y) by lra.
    replace (a * (u * y - x * v)) with (a * u * y - a * x * v) by ring.
    rewrite Hau, Hax. ring. }
  assert (Hkey_b: b * (u * y - x * v) = 0).
  { assert (Hbv: b * v = - a * u) by lra.
    assert (Hby: b * y = - a * x) by lra.
    replace (b * (u * y - x * v)) with (u * (b * y) - (b * v) * x) by ring.
    rewrite Hbv, Hby. ring. }
  destruct Hab as [Ha | Hb].
  - assert (Hres: u * y - x * v = 0).
    { assert (Ha_sq: a * a > 0) by nra.
      assert (H: a * (a * (u * y - x * v)) = 0) by nra.
      nra. }
    unfold u, v, x, y in Hres.
    lra.
  - assert (Hres: u * y - x * v = 0).
    { assert (Hb_sq: b * b > 0) by nra.
      assert (H: b * (b * (u * y - x * v)) = 0) by nra.
      nra. }
    unfold u, v, x, y in Hres.
    lra.
Qed.

(** Three points equidistant from both A and C are collinear (on perp bisector).
    Proof: All such points satisfy the perpendicular bisector line equation.
    The perpendicular bisector is the line through midpoint(A,C) perpendicular to AC. *)
Lemma three_equidistant_points_collinear : forall P Q R A C,
  px A <> px C \/ py A <> py C ->
  dist_sq P A = dist_sq P C ->
  dist_sq Q A = dist_sq Q C ->
  dist_sq R A = dist_sq R C ->
  collinear P Q R.
Proof.
  intros P Q R A C HAC HP HQ HR.
  apply on_perp_bisector_eq in HP.
  apply on_perp_bisector_eq in HQ.
  apply on_perp_bisector_eq in HR.
  unfold collinear, px, py in *.
  set (a := fst A - fst C).
  set (b := snd A - snd C).
  set (mx := (fst A + fst C) / 2).
  set (my := (snd A + snd C) / 2).
  assert (HPline: a * fst P + b * snd P = a * mx + b * my).
  { unfold a, b, mx, my. lra. }
  assert (HQline: a * fst Q + b * snd Q = a * mx + b * my).
  { unfold a, b, mx, my. lra. }
  assert (HRline: a * fst R + b * snd R = a * mx + b * my).
  { unfold a, b, mx, my. lra. }
  apply points_on_line_collinear with (a := a) (b := b).
  - unfold a, b. destruct HAC; [left | right]; lra.
  - lra.
  - lra.
Qed.

(** * Section 11.3: Main Collinearity Theorem for Peaucellier Linkage *)

(** KEY THEOREM: In a valid Peaucellier linkage, O, B, D are collinear.

    Proof strategy:
    1. |OA| = |OC| implies O is equidistant from A and C
    2. |AB| = |BC| implies B is equidistant from A and C
    3. |DA| = |DC| implies D is equidistant from A and C
    4. Three points equidistant from A and C lie on the perpendicular bisector of AC
    5. Three points on a line are collinear *)

Theorem linkage_OBD_collinear : forall O A B C D L s,
  dist_sq O A = L² ->
  dist_sq O C = L² ->
  dist_sq A B = s² ->
  dist_sq B C = s² ->
  dist_sq C D = s² ->
  dist_sq D A = s² ->
  px A <> px C \/ py A <> py C ->
  collinear O B D.
Proof.
  intros O A B C D L s HOA HOC HAB HBC HCD HDA HAC.
  apply three_equidistant_points_collinear with (A := A) (C := C).
  - exact HAC.
  - rewrite HOA, HOC. reflexivity.
  - rewrite dist_sq_sym. rewrite HAB. rewrite HBC. reflexivity.
  - rewrite HDA. rewrite dist_sq_sym. rewrite HCD. reflexivity.
Qed.

(** Corollary for the linkage record type *)
Corollary linkage_OBD_collinear_record : forall P,
  linkage_valid_sq P ->
  pl_A P <> pl_C P ->
  OBD_collinear P.
Proof.
  intros P Hvalid HAneqC.
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  unfold OBD_collinear.
  apply linkage_OBD_collinear with (L := pl_L P) (s := pl_s P) (A := pl_A P) (C := pl_C P).
  - exact HOA.
  - exact HOC.
  - exact HAB.
  - exact HBC.
  - exact HCD.
  - exact HDA.
  - unfold px, py.
    destruct (pl_A P) as [ax ay], (pl_C P) as [cx cy].
    simpl.
    destruct (Req_dec ax cx) as [Hxeq | Hxneq].
    + right.
      intros Hyeq.
      apply HAneqC.
      rewrite Hxeq, Hyeq.
      reflexivity.
    + left. exact Hxneq.
Qed.

(** * Section 11.4: Connecting Collinearity to the Straight-Line Property *)

(** With `linkage_OBD_collinear` we've proven that O, B, D are collinear
    purely from the linkage distance constraints. This removes the need
    to assume collinearity in the standard-position theorem.

    The full straight-line theorem in general position would require proving
    that the product formula |OB|·|OD| = L² - s² holds in arbitrary coordinates.
    The standard-position proof (peaucellier_straight_line) establishes this
    when the linkage is oriented with O at origin and B, D on the x-axis.

    For a complete general-position proof, one would show that any valid
    linkage configuration can be rigidly transformed to standard position
    without changing the geometric relationships.

    Key results established:
    1. linkage_OBD_collinear: Distance constraints alone imply O,B,D collinear
    2. peaucellier_product_formula: |OB|²·|OD|² = (L²-s²)² in standard position
    3. circle_through_O_inverts_to_line: Circle through O inverts to a line
    4. peaucellier_straight_line: D lies on a line when B is on circle through O
*)

(** Corollary: The linkage forms a valid inversor when collinearity holds *)
Corollary linkage_is_inversor : forall P,
  linkage_geometric P ->
  dist_sq (pl_O P) (pl_B P) * dist_sq (pl_O P) (pl_D P) =
  (linkage_k_sq P) * (linkage_k_sq P).
Proof.
  intros P Hgeom.
  unfold linkage_k_sq.
  apply peaucellier_product_formula.
  exact Hgeom.
Qed.

(** * Section 11.5: Weakening Position Constraints *)

(** First weakening: Remove fst D > fst B, allow B and D on same side of O *)
Lemma product_formula_relaxed_order : forall O A B C D L s,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  fst B <> fst D ->
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
  intros HO1 HO2 HB2 HD2 HBneqD HAC1 HAC2.
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
    destruct Hdiff as [H1 | H2]; lra. }
  assert (Hp: (fst D - fst B) / 2 * ((fst D - fst B) / 2) + snd A * snd A = s * s).
  { replace (fst A) with ((fst B + fst D) / 2) in HAB by (symmetry; exact HAmid).
    nra. }
  assert (HOAexp: fst A * fst A + snd A * snd A = L * L) by nra.
  rewrite HAmid in HOAexp.
  assert (Hprod: fst B * fst D =
                 ((fst B + fst D)/2) * ((fst B + fst D)/2) -
                 ((fst D - fst B)/2) * ((fst D - fst B)/2)).
  { field. }
  rewrite Hprod.
  lra.
Qed.

(** Second weakening: Derive A,C symmetry from distance constraints *)
Lemma product_formula_derived_symmetry : forall O A B C D L s,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  fst B <> fst D ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  fst A = fst C /\ snd A = - snd C ->
  fst B * fst D = L * L - s * s.
Proof.
  intros O A B C D L s HO1 HO2 HB2 HD2 HBneqD HOA HOC HAB HBC HCD HDA HLs Hs [HAC1 HAC2].
  apply (product_formula_relaxed_order O A B C D L s); assumption.
Qed.

(** Key lemma: Equal distances from origin imply coordinate symmetry about x-axis *)
Lemma equal_dist_origin_symmetry : forall A C L,
  dist_sq (0, 0) A = L * L ->
  dist_sq (0, 0) C = L * L ->
  fst A = fst C ->
  snd A = snd C \/ snd A = - snd C.
Proof.
  intros A C L HA HC Hfst.
  unfold dist_sq, px, py, Rsqr in *.
  simpl in *.
  assert (snd A * snd A = snd C * snd C) by nra.
  apply Rsqr_eq in H. unfold Rsqr in H.
  exact H.
Qed.

(** AC symmetry forced: In standard position, the rhombus constraints force
    A and C to have the same x-coordinate (midpoint of B and D).
    Combined with |OA| = |OC|, this forces y-coordinate symmetry. *)
Lemma AC_x_coord_forced : forall A B C D s,
  snd B = 0 -> snd D = 0 ->
  fst B <> fst D ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  s > 0 ->
  fst A = fst C.
Proof.
  intros A B C D s HB2 HD2 HBneqD HAB HBC HCD HDA Hs.
  unfold dist_sq, px, py, Rsqr in *.
  rewrite HB2, HD2 in *.
  assert (HAeq: (fst A - fst B) * (fst A - fst B) + snd A * snd A = s * s) by nra.
  assert (HDeq: (fst A - fst D) * (fst A - fst D) + snd A * snd A = s * s) by nra.
  assert (HCBeq: (fst C - fst B) * (fst C - fst B) + snd C * snd C = s * s) by nra.
  assert (HCDeq: (fst C - fst D) * (fst C - fst D) + snd C * snd C = s * s) by nra.
  assert (HAB_eq_HAD: (fst A - fst B) * (fst A - fst B) = (fst A - fst D) * (fst A - fst D)) by nra.
  assert (HCB_eq_HCD: (fst C - fst B) * (fst C - fst B) = (fst C - fst D) * (fst C - fst D)) by nra.
  apply Rsqr_eq in HAB_eq_HAD. unfold Rsqr in HAB_eq_HAD.
  apply Rsqr_eq in HCB_eq_HCD. unfold Rsqr in HCB_eq_HCD.
  destruct HAB_eq_HAD as [HA1 | HA2].
  - assert (fst B = fst D) by lra. contradiction.
  - destruct HCB_eq_HCD as [HC1 | HC2].
    + assert (fst B = fst D) by lra. contradiction.
    + lra.
Qed.

(** Full AC symmetry: Both x-coord equality and y-coord symmetry.
    Requires non-degeneracy: A ≠ C (real rhombus, not collapsed). *)
Lemma AC_symmetry_forced : forall O A B C D L s,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  fst B <> fst D ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  A <> C ->
  fst A = fst C /\ snd A = - snd C.
Proof.
  intros O A B C D L s HO1 HO2 HB2 HD2 HBneqD HOA HOC HAB HBC HCD HDA HLs Hs HAneqC.
  assert (Hfst: fst A = fst C).
  { apply (AC_x_coord_forced A B C D s); assumption. }
  split.
  - exact Hfst.
  - assert (Hsym: snd A = snd C \/ snd A = - snd C).
    { unfold dist_sq, px, py, Rsqr in HOA, HOC.
      rewrite HO1, HO2 in HOA, HOC. simpl in HOA, HOC.
      apply (equal_dist_origin_symmetry A C L).
      - unfold dist_sq, px, py, Rsqr. simpl. nra.
      - unfold dist_sq, px, py, Rsqr. simpl. nra.
      - exact Hfst. }
    destruct Hsym as [Heq | Hneq].
    + exfalso. apply HAneqC.
      destruct A as [ax ay], C as [cx cy]. simpl in *.
      f_equal; [exact Hfst | exact Heq].
    + exact Hneq.
Qed.

(** Third weakening: Express in terms of dist_sq products *)
Lemma product_formula_dist_sq : forall O A B C D L s,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  fst B <> fst D ->
  fst A = fst C ->
  snd A = - snd C ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  dist_sq O B * dist_sq O D = (L * L - s * s) * (L * L - s * s).
Proof.
  intros O A B C D L s HO1 HO2 HB2 HD2 HBneqD HAC1 HAC2.
  intros HOA HOC HAB HBC HCD HDA HLs Hs.
  assert (Hprod: fst B * fst D = L * L - s * s).
  { apply (product_formula_relaxed_order O A B C D L s); assumption. }
  unfold dist_sq, px, py, Rsqr.
  rewrite HO1, HO2, HB2, HD2.
  simpl.
  nra.
Qed.

(** Fourth step: Collinearity on x-axis implies the coordinate constraints *)
Lemma collinear_on_xaxis_coords : forall O B D,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  collinear O B D.
Proof.
  intros O B D HO1 HO2 HB2 HD2.
  unfold collinear, px, py.
  rewrite HO1, HO2, HB2, HD2.
  ring.
Qed.

(** Fifth step: When on x-axis, B ≠ D implies coordinate inequality *)
Lemma xaxis_neq_implies_fst_neq : forall B D : Point,
  snd B = 0 -> snd D = 0 ->
  B <> D ->
  fst B <> fst D.
Proof.
  intros B D HB2 HD2 Hneq Heq.
  apply Hneq.
  destruct B as [bx b_y], D as [dx d_y].
  unfold fst, snd in *.
  rewrite Heq, HB2, HD2.
  reflexivity.
Qed.

(** Product formula using collinearity and B ≠ D *)
Lemma product_formula_collinear : forall O A B C D L s,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  B <> D ->
  fst A = fst C ->
  snd A = - snd C ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  dist_sq O B * dist_sq O D = (L * L - s * s) * (L * L - s * s).
Proof.
  intros O A B C D L s HO1 HO2 HB2 HD2 HBneqD HAC1 HAC2.
  intros HOA HOC HAB HBC HCD HDA HLs Hs.
  apply (product_formula_dist_sq O A B C D L s); try assumption.
  apply xaxis_neq_implies_fst_neq; assumption.
Qed.

(** * Section 11.6: Rigid Transformations and Coordinate Independence *)

(** A rigid transformation (rotation + translation) preserves distances.
    We define it as a function on points that preserves dist_sq. *)

Definition rigid_transform := Point -> Point.

Definition is_rigid (T : rigid_transform) : Prop :=
  forall P Q : Point, dist_sq (T P) (T Q) = dist_sq P Q.

(** Rigid transforms preserve dist_sq by definition *)
Lemma rigid_preserves_dist_sq : forall T P Q,
  is_rigid T -> dist_sq (T P) (T Q) = dist_sq P Q.
Proof.
  intros T P Q HT. apply HT.
Qed.

(** * Section 11.6.1: Concrete Rigid Transformations *)

(** Translation by a vector *)
Definition translate (v : Point) (P : Point) : Point :=
  (fst P + fst v, snd P + snd v).

(** Translation preserves distances *)
Lemma translate_is_rigid : forall v, is_rigid (translate v).
Proof.
  intros v P Q.
  unfold translate, dist_sq, px, py, Rsqr. simpl.
  ring.
Qed.

(** Translation moves origin to any point *)
Lemma translate_origin : forall P,
  translate (- fst P, - snd P) P = (0, 0).
Proof.
  intros P. unfold translate. simpl.
  f_equal; ring.
Qed.

(** Rotation about origin by angle with cosine c and sine s where c² + s² = 1 *)
Definition rotate (c s : R) (P : Point) : Point :=
  (c * fst P - s * snd P, s * fst P + c * snd P).

(** Rotation preserves distances when c² + s² = 1 *)
Lemma rotate_preserves_dist_sq : forall c s P Q,
  c * c + s * s = 1 ->
  dist_sq (rotate c s P) (rotate c s Q) = dist_sq P Q.
Proof.
  intros c s P Q Hunit.
  unfold rotate, dist_sq, px, py, Rsqr. simpl.
  set (px_ := fst P). set (py_ := snd P).
  set (qx := fst Q). set (qy := snd Q).
  replace ((c * qx - s * qy - (c * px_ - s * py_)) *
           (c * qx - s * qy - (c * px_ - s * py_)) +
           (s * qx + c * qy - (s * px_ + c * py_)) *
           (s * qx + c * qy - (s * px_ + c * py_)))
    with ((c*c + s*s) * ((qx - px_) * (qx - px_) + (qy - py_) * (qy - py_)))
    by ring.
  rewrite Hunit. ring.
Qed.

(** Rotation is rigid when c² + s² = 1 *)
Lemma rotate_is_rigid : forall c s,
  c * c + s * s = 1 -> is_rigid (rotate c s).
Proof.
  intros c s Hunit P Q.
  apply rotate_preserves_dist_sq. exact Hunit.
Qed.

(** Rotation maps point (r, 0) to (r*c, r*s) *)
Lemma rotate_xaxis : forall c s r,
  rotate c s (r, 0) = (r * c, r * s).
Proof.
  intros c s r. unfold rotate. simpl.
  f_equal; ring.
Qed.

(** Composition of rigid transforms is rigid *)
Lemma compose_rigid : forall T1 T2,
  is_rigid T1 -> is_rigid T2 -> is_rigid (fun P => T2 (T1 P)).
Proof.
  intros T1 T2 H1 H2 P Q.
  rewrite H2. rewrite H1. reflexivity.
Qed.

(** * Section 11.6.2: Constructing the Normalizing Transform *)

(** The normalizing transform:
    1. Translate O to origin
    2. Rotate so that B lies on the x-axis
    This puts collinear O, B, D into standard position. *)

Definition normalize_transform (O B : Point) (P : Point) : Point :=
  let v := (- fst O, - snd O) in
  let B' := translate v B in
  let r := sqrt (fst B' * fst B' + snd B' * snd B') in
  let c := fst B' / r in
  let s := - snd B' / r in
  rotate c s (translate v P).

(** After normalization, O maps to origin *)
Lemma normalize_O_at_origin : forall O B,
  normalize_transform O B O = (0, 0).
Proof.
  intros O B.
  unfold normalize_transform, translate, rotate. simpl.
  f_equal; ring.
Qed.

(** After normalization, B lies on x-axis (y-coordinate is 0) *)
Lemma normalize_B_on_xaxis : forall O B,
  dist O B > 0 ->
  snd (normalize_transform O B B) = 0.
Proof.
  intros O B Hdist.
  unfold normalize_transform, translate, rotate. simpl.
  assert (Hr_pos: sqrt ((fst B + - fst O) * (fst B + - fst O) +
                        (snd B + - snd O) * (snd B + - snd O)) > 0).
  { apply sqrt_lt_R0.
    assert (Hdsq: dist_sq O B > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
    unfold dist_sq, px, py, Rsqr in Hdsq.
    replace (fst B + - fst O) with (fst B - fst O) by ring.
    replace (snd B + - snd O) with (snd B - snd O) by ring.
    nra. }
  assert (Hr_neq: sqrt ((fst B + - fst O) * (fst B + - fst O) +
                        (snd B + - snd O) * (snd B + - snd O)) <> 0) by lra.
  field. exact Hr_neq.
Qed.

(** The normalizing transform is rigid when B ≠ O *)
Lemma normalize_is_rigid : forall O B,
  dist O B > 0 ->
  is_rigid (normalize_transform O B).
Proof.
  intros O B Hdist.
  unfold normalize_transform.
  set (v := (- fst O, - snd O)).
  set (B' := translate v B).
  set (r := sqrt (fst B' * fst B' + snd B' * snd B')).
  set (c := fst B' / r).
  set (s := - snd B' / r).
  assert (Hr_pos: r > 0).
  { unfold r, B', v, translate. simpl.
    apply sqrt_lt_R0.
    assert (Hdsq: dist_sq O B > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
    unfold dist_sq, px, py, Rsqr in Hdsq.
    replace (fst B + - fst O) with (fst B - fst O) by ring.
    replace (snd B + - snd O) with (snd B - snd O) by ring.
    exact Hdsq. }
  assert (Hunit: c * c + s * s = 1).
  { unfold c, s.
    assert (Hr_neq: r <> 0) by lra.
    unfold r, B', v, translate. simpl.
    set (bx := fst B + - fst O).
    set (by_ := snd B + - snd O).
    set (rsq := bx * bx + by_ * by_).
    assert (Hrsq_pos: rsq > 0).
    { unfold rsq, bx, by_.
      assert (Hdsq: dist_sq O B > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
      unfold dist_sq, px, py, Rsqr in Hdsq. nra. }
    assert (Hr_eq: sqrt rsq * sqrt rsq = rsq).
    { apply sqrt_sqrt. lra. }
    replace (bx / sqrt rsq * (bx / sqrt rsq) + - by_ / sqrt rsq * (- by_ / sqrt rsq))
      with ((bx * bx + by_ * by_) / (sqrt rsq * sqrt rsq)).
    2: { field. apply Rgt_not_eq. apply sqrt_lt_R0. exact Hrsq_pos. }
    rewrite Hr_eq. unfold rsq. field.
    unfold bx, by_. apply Rgt_not_eq.
    assert (Hdsq: dist_sq O B > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
    unfold dist_sq, px, py, Rsqr in Hdsq. nra. }
  apply compose_rigid.
  - apply translate_is_rigid.
  - apply rotate_is_rigid. exact Hunit.
Qed.

(** There exists a rigid transform taking any three collinear points to standard position *)
Definition standard_position (O B D : Point) : Prop :=
  fst O = 0 /\ snd O = 0 /\
  snd B = 0 /\ snd D = 0.

(** Product formula is invariant under rigid transformation *)
Theorem product_formula_rigid_invariant : forall T O A B C D L s,
  is_rigid T ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  dist_sq O B * dist_sq O D = dist_sq (T O) (T B) * dist_sq (T O) (T D).
Proof.
  intros T O A B C D L s HT HOA HOC HAB HBC HCD HDA HLs Hs.
  rewrite (rigid_preserves_dist_sq T O B HT).
  rewrite (rigid_preserves_dist_sq T O D HT).
  reflexivity.
Qed.

(** The product formula holds for any linkage configuration that can be
    rigidly transformed to standard position *)
Theorem product_formula_via_rigid_transform : forall O A B C D L s,
  (exists T : rigid_transform,
    is_rigid T /\
    standard_position (T O) (T B) (T D) /\
    fst (T A) = fst (T C) /\
    snd (T A) = - snd (T C) /\
    T B <> T D) ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  dist_sq O B * dist_sq O D = (L * L - s * s) * (L * L - s * s).
Proof.
  intros O A B C D L s [T [HT [Hstd [HAC1 [HAC2 HTneq]]]]].
  intros HOA HOC HAB HBC HCD HDA HLs Hs.
  destruct Hstd as [HO1 [HO2 [HB2 HD2]]].
  rewrite <- (rigid_preserves_dist_sq T O B HT).
  rewrite <- (rigid_preserves_dist_sq T O D HT).
  apply (product_formula_collinear (T O) (T A) (T B) (T C) (T D) L s).
  - exact HO1.
  - exact HO2.
  - exact HB2.
  - exact HD2.
  - exact HTneq.
  - exact HAC1.
  - exact HAC2.
  - rewrite (rigid_preserves_dist_sq T O A HT). exact HOA.
  - rewrite (rigid_preserves_dist_sq T O C HT). exact HOC.
  - rewrite (rigid_preserves_dist_sq T A B HT). exact HAB.
  - rewrite (rigid_preserves_dist_sq T B C HT). exact HBC.
  - rewrite (rigid_preserves_dist_sq T C D HT). exact HCD.
  - rewrite (rigid_preserves_dist_sq T D A HT). exact HDA.
  - exact HLs.
  - exact Hs.
Qed.

(** * Section 11.7: Building Toward a Unified Theorem *)

(** If O is at origin, B is on x-axis with fst B ≠ 0, collinearity of O,B,D implies D is on x-axis *)
Lemma collinear_origin_xaxis : forall O B D,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> fst B <> 0 ->
  collinear O B D ->
  snd D = 0.
Proof.
  intros O B D HO1 HO2 HB2 HBnz Hcol.
  unfold collinear, px, py in Hcol.
  rewrite HO1, HO2, HB2 in Hcol.
  simpl in Hcol.
  nra.
Qed.

(** After normalization, fst (T B) = dist O B > 0 *)
Lemma normalize_B_x_eq_dist : forall O B,
  dist O B > 0 ->
  fst (normalize_transform O B B) = dist O B.
Proof.
  intros O B Hdist.
  unfold normalize_transform, translate, rotate, dist, dist_sq, px, py, Rsqr. simpl.
  replace (fst B + - fst O) with (fst B - fst O) by ring.
  replace (snd B + - snd O) with (snd B - snd O) by ring.
  assert (Hdsq_pos: (fst B - fst O) * (fst B - fst O) + (snd B - snd O) * (snd B - snd O) > 0).
  { assert (H: dist_sq O B > 0) by (apply dist_pos_implies_dist_sq_pos; exact Hdist).
    unfold dist_sq, px, py, Rsqr in H. exact H. }
  assert (Hr_neq: sqrt ((fst B - fst O) * (fst B - fst O) + (snd B - snd O) * (snd B - snd O)) <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0. exact Hdsq_pos. }
  assert (Hsqrt_sq: sqrt ((fst B - fst O) * (fst B - fst O) + (snd B - snd O) * (snd B - snd O)) *
                    sqrt ((fst B - fst O) * (fst B - fst O) + (snd B - snd O) * (snd B - snd O)) =
                    (fst B - fst O) * (fst B - fst O) + (snd B - snd O) * (snd B - snd O)).
  { apply sqrt_sqrt. lra. }
  transitivity (((fst B - fst O) * (fst B - fst O) + (snd B - snd O) * (snd B - snd O)) /
                sqrt ((fst B - fst O) * (fst B - fst O) + (snd B - snd O) * (snd B - snd O))).
  - field. exact Hr_neq.
  - rewrite <- Hsqrt_sq at 1.
    field. exact Hr_neq.
Qed.

(** After normalization, fst (T B) > 0 *)
Lemma normalize_B_x_positive : forall O B,
  dist O B > 0 ->
  fst (normalize_transform O B B) > 0.
Proof.
  intros O B Hdist.
  rewrite normalize_B_x_eq_dist by exact Hdist.
  exact Hdist.
Qed.

(** Corollary: fst (T B) ≠ 0 *)
Lemma normalize_B_x_nonzero : forall O B,
  dist O B > 0 ->
  fst (normalize_transform O B B) <> 0.
Proof.
  intros O B Hdist.
  assert (H: fst (normalize_transform O B B) > 0) by (apply normalize_B_x_positive; exact Hdist).
  lra.
Qed.

(** * Section 12: Strengthened Theorems - Removing AC Symmetry Assumption *)

(** Product formula without assuming AC symmetry - derives it from constraints.
    This removes the need to assume fst A = fst C and snd A = -snd C. *)
Theorem product_formula_no_symmetry_assumption : forall O A B C D L s,
  fst O = 0 -> snd O = 0 ->
  snd B = 0 -> snd D = 0 ->
  B <> D ->
  A <> C ->
  dist_sq O A = L * L ->
  dist_sq O C = L * L ->
  dist_sq A B = s * s ->
  dist_sq B C = s * s ->
  dist_sq C D = s * s ->
  dist_sq D A = s * s ->
  L > s -> s > 0 ->
  dist_sq O B * dist_sq O D = (L * L - s * s) * (L * L - s * s).
Proof.
  intros O A B C D L s HO1 HO2 HB2 HD2 HBneqD HAneqC.
  intros HOA HOC HAB HBC HCD HDA HLs Hs.
  assert (HBDfst: fst B <> fst D).
  { apply xaxis_neq_implies_fst_neq; assumption. }
  assert (Hsym: fst A = fst C /\ snd A = - snd C).
  { apply (AC_symmetry_forced O A B C D L s); assumption. }
  destruct Hsym as [HAC1 HAC2].
  apply (product_formula_dist_sq O A B C D L s); assumption.
Qed.

(** Minimal geometric configuration - no AC symmetry assumed *)
Definition linkage_geometric_minimal (P : PeaucellierLinkage) : Prop :=
  linkage_valid_sq P /\
  OBD_collinear P /\
  pl_A P <> pl_C P /\
  px (pl_O P) = 0 /\ py (pl_O P) = 0 /\
  py (pl_B P) = 0 /\ py (pl_D P) = 0 /\
  pl_B P <> pl_D P.

(** Ultra-minimal: collinearity is DERIVED, not assumed *)
Definition linkage_geometric_derived (P : PeaucellierLinkage) : Prop :=
  linkage_valid_sq P /\
  pl_A P <> pl_C P /\
  px (pl_O P) = 0 /\ py (pl_O P) = 0 /\
  py (pl_B P) = 0 /\ py (pl_D P) = 0 /\
  pl_B P <> pl_D P.

(** The derived configuration implies the minimal one *)
Lemma derived_implies_minimal : forall P,
  linkage_geometric_derived P -> linkage_geometric_minimal P.
Proof.
  intros P [Hvalid [HAneqC [HO1 [HO2 [HB2 [HD2 HBneqD]]]]]].
  unfold linkage_geometric_minimal.
  split; [exact Hvalid |].
  split; [apply linkage_OBD_collinear_record; assumption |].
  split; [exact HAneqC |].
  split; [exact HO1 |].
  split; [exact HO2 |].
  split; [exact HB2 |].
  split; [exact HD2 |].
  exact HBneqD.
Qed.

(** The product formula for minimal configuration *)
Theorem peaucellier_product_formula_minimal : forall P,
  linkage_geometric_minimal P ->
  dist_sq (pl_O P) (pl_B P) * dist_sq (pl_O P) (pl_D P) =
  ((pl_L P) * (pl_L P) - (pl_s P) * (pl_s P)) *
  ((pl_L P) * (pl_L P) - (pl_s P) * (pl_s P)).
Proof.
  intros P [Hvalid [Hcol [HAneqC [HO1 [HO2 [HB2 [HD2 HBneqD]]]]]]].
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  unfold Rsqr in *.
  apply (product_formula_no_symmetry_assumption
           (pl_O P) (pl_A P) (pl_B P) (pl_C P) (pl_D P) (pl_L P) (pl_s P)).
  - unfold px in HO1. exact HO1.
  - unfold py in HO2. exact HO2.
  - unfold py in HB2. exact HB2.
  - unfold py in HD2. exact HD2.
  - exact HBneqD.
  - exact HAneqC.
  - exact HOA.
  - exact HOC.
  - exact HAB.
  - exact HBC.
  - exact HCD.
  - exact HDA.
  - exact HLs.
  - exact Hs.
Qed.

(** AC symmetry is derivable from minimal configuration *)
Lemma minimal_implies_AC_symmetry : forall P,
  linkage_geometric_minimal P ->
  px (pl_A P) = px (pl_C P) /\ py (pl_A P) = - py (pl_C P).
Proof.
  intros P [Hvalid [Hcol [HAneqC [HO1 [HO2 [HB2 [HD2 HBneqD]]]]]]].
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  unfold Rsqr in *.
  assert (HBDfst: fst (pl_B P) <> fst (pl_D P)).
  { apply xaxis_neq_implies_fst_neq; assumption. }
  apply (AC_symmetry_forced (pl_O P) (pl_A P) (pl_B P) (pl_C P) (pl_D P)
                            (pl_L P) (pl_s P)).
  - unfold px in HO1. exact HO1.
  - unfold py in HO2. exact HO2.
  - unfold py in HB2. exact HB2.
  - unfold py in HD2. exact HD2.
  - exact HBDfst.
  - exact HOA.
  - exact HOC.
  - exact HAB.
  - exact HBC.
  - exact HCD.
  - exact HDA.
  - exact HLs.
  - exact Hs.
  - exact HAneqC.
Qed.

(** D on perpendicular line - minimal version that derives AC symmetry *)
Lemma linkage_D_on_perp_line_minimal : forall P M r,
  linkage_geometric_minimal P ->
  B_on_circle_through_O P M r ->
  dist (pl_O P) (pl_B P) > 0 ->
  on_perp_line (pl_O P) M (linkage_k P) (pl_D P).
Proof.
  intros P M r Hgeom HBcirc HdistB.
  destruct HBcirc as [HOM [Hr HBonC]].
  destruct Hgeom as [Hvalid [Hcol [HAneqC [HO1 [HO2 [HB2 [HD2 HBneqD]]]]]]].
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs Hs]]]]]]].
  assert (Hsym: px (pl_A P) = px (pl_C P) /\ py (pl_A P) = - py (pl_C P)).
  { apply minimal_implies_AC_symmetry.
    unfold linkage_geometric_minimal, linkage_valid_sq, OBD_collinear.
    unfold Rsqr in *.
    repeat split; assumption. }
  destruct Hsym as [HACx HACy].
  assert (HBDfst: fst (pl_B P) <> fst (pl_D P)).
  { apply xaxis_neq_implies_fst_neq; assumption. }
  unfold on_perp_line, dot_product_from, linkage_k, linkage_k_sq, px, py.
  unfold px, py in HO1, HO2, HD2.
  rewrite HO1, HO2, HD2.
  unfold Rsqr in *.
  assert (Hprod: fst (pl_B P) * fst (pl_D P) = pl_L P * pl_L P - pl_s P * pl_s P).
  { apply (product_formula_relaxed_order (pl_O P) (pl_A P) (pl_B P) (pl_C P) (pl_D P)
                                         (pl_L P) (pl_s P)).
    - unfold px in HO1. exact HO1.
    - unfold py in HO2. exact HO2.
    - unfold py in HB2. exact HB2.
    - unfold py in HD2. exact HD2.
    - exact HBDfst.
    - unfold px in HACx. exact HACx.
    - unfold py in HACy. exact HACy.
    - exact HOA.
    - exact HOC.
    - exact HAB.
    - exact HBC.
    - exact HCD.
    - exact HDA.
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
    - assert (fst (pl_B P) = 0) by lra.
      assert (Hcontra: dist (pl_O P) (pl_B P) = 0).
      { unfold dist, dist_sq, px, py, Rsqr. rewrite HO1, HO2, HB2, H. simpl.
        replace ((0 - 0) * (0 - 0) + (0 - 0) * (0 - 0)) with 0 by ring.
        apply sqrt_0. }
      lra.
    - lra. }
  rewrite sqrt_sqrt by lra.
  rewrite HMx_eq.
  rewrite <- Hprod.
  field; lra.
Qed.

(** ========== STRENGTHENED MAIN THEOREM ========== *)
(**
    Peaucellier-Lipkin Linkage Straight-Line Theorem (Minimal Assumptions):

    If:
    - The linkage satisfies the distance constraints (rhombus + equal arms)
    - O, B, D are collinear (follows from equal arms)
    - A ≠ C (non-degenerate rhombus)
    - B ≠ D (non-collapsed configuration)
    - B moves on a circle that passes through the pivot O
    - B ≠ O (the mechanism is not at singularity)

    Then:
    - D lies on a straight line perpendicular to the line through O and
      the circle's center

    This version derives AC symmetry from the constraints rather than assuming it.
*)

Theorem peaucellier_straight_line_minimal : forall P M r,
  linkage_geometric_minimal P ->
  B_on_circle_through_O P M r ->
  dist (pl_O P) (pl_B P) > 0 ->
  on_line (pl_D P) (circle_inversion_image_line (pl_O P) M (linkage_k P)).
Proof.
  intros P M r Hgeom HBcirc HdistB.
  apply circle_inversion_image_line_char.
  apply linkage_D_on_perp_line_minimal with (r := r); assumption.
Qed.

(** ========== ULTIMATE THEOREM: COLLINEARITY DERIVED ========== *)
(**
    This is the strongest form of the theorem. Collinearity of O, B, D
    is NOT assumed - it is derived from the linkage constraints via
    linkage_OBD_collinear_record.
*)

Theorem peaucellier_straight_line_derived : forall P M r,
  linkage_geometric_derived P ->
  B_on_circle_through_O P M r ->
  dist (pl_O P) (pl_B P) > 0 ->
  on_line (pl_D P) (circle_inversion_image_line (pl_O P) M (linkage_k P)).
Proof.
  intros P M r Hderived HBcirc HdistB.
  apply peaucellier_straight_line_minimal with (r := r); try assumption.
  apply derived_implies_minimal. exact Hderived.
Qed.

(** * Section 13: Constructive Line Witness *)

(** Compute the straight line traced by D given linkage parameters and circle center.
    The line is perpendicular to (M - O) and passes through the point where
    the dot product with (M - O) equals k²/2.

    Line equation: (Mx - Ox)(x - Ox) + (My - Oy)(y - Oy) = k²/2
    In standard form Ax + By + C = 0:
      A = Mx - Ox
      B = My - Oy
      C = -A·Ox - B·Oy - k²/2
*)

Definition peaucellier_output_line (O M : Point) (L s : R) : Line :=
  let k_sq := L * L - s * s in
  circle_inversion_image_line O M (sqrt k_sq).

(** The line coefficients as explicit functions *)
Definition output_line_A (O M : Point) : R := px M - px O.
Definition output_line_B (O M : Point) : R := py M - py O.
Definition output_line_C (O M : Point) (L s : R) : R :=
  let k_sq := L * L - s * s in
  - (px M - px O) * px O - (py M - py O) * py O - k_sq / 2.

(** The explicit line matches our definition *)
Lemma peaucellier_output_line_explicit : forall O M L s,
  L > s -> s > 0 ->
  peaucellier_output_line O M L s =
  mkLine (output_line_A O M) (output_line_B O M) (output_line_C O M L s).
Proof.
  intros O M L s HLs Hs.
  unfold peaucellier_output_line, circle_inversion_image_line.
  unfold output_line_A, output_line_B, output_line_C.
  f_equal.
  assert (Hksq_pos: L * L - s * s > 0) by nra.
  rewrite sqrt_sqrt by lra.
  reflexivity.
Qed.

(** Final theorem with explicit line construction *)
Theorem peaucellier_explicit_line : forall P M r,
  linkage_geometric_minimal P ->
  B_on_circle_through_O P M r ->
  dist (pl_O P) (pl_B P) > 0 ->
  on_line (pl_D P) (peaucellier_output_line (pl_O P) M (pl_L P) (pl_s P)).
Proof.
  intros P M r Hgeom HBcirc HdistB.
  unfold peaucellier_output_line.
  assert (Hk_eq: sqrt (pl_L P * pl_L P - pl_s P * pl_s P) = linkage_k P).
  { unfold linkage_k, linkage_k_sq. reflexivity. }
  rewrite Hk_eq.
  apply peaucellier_straight_line_minimal with (r := r); assumption.
Qed.

(** Extraction-friendly version: compute line coefficients directly *)
Definition compute_line_coefficients (Ox Oy Mx My L s : R) : R * R * R :=
  let A := Mx - Ox in
  let B := My - Oy in
  let k_sq := L * L - s * s in
  let C := - A * Ox - B * Oy - k_sq / 2 in
  (A, B, C).

(** The computed coefficients match our line definition *)
Lemma compute_line_coefficients_correct : forall O M L s,
  L > s -> s > 0 ->
  let (AB, C) := compute_line_coefficients (px O) (py O) (px M) (py M) L s in
  let (A, B) := AB in
  peaucellier_output_line O M L s = mkLine A B C.
Proof.
  intros O M L s HLs Hs.
  unfold compute_line_coefficients.
  rewrite peaucellier_output_line_explicit by assumption.
  unfold output_line_A, output_line_B, output_line_C.
  reflexivity.
Qed.

(** * Section 14: General Position Theorem *)

(** The key insight: the perpendicular line condition dot_product_from O M D = k²/2
    is coordinate-invariant. We prove this by showing rigid transforms preserve
    dot products (up to the transform of the reference point). *)

(** Rigid transforms preserve dot products from a common origin *)
Lemma rigid_preserves_dot_product : forall T O P Q,
  is_rigid T ->
  dot_product_from (T O) (T P) (T Q) = dot_product_from O P Q.
Proof.
  intros T O P Q HT.
  unfold dot_product_from.
  assert (Hdist_OP: dist_sq (T O) (T P) = dist_sq O P) by apply HT.
  assert (Hdist_OQ: dist_sq (T O) (T Q) = dist_sq O Q) by apply HT.
  assert (Hdist_PQ: dist_sq (T P) (T Q) = dist_sq P Q) by apply HT.
  unfold dist_sq, px, py, Rsqr in *.
  set (ox := fst O). set (oy := snd O).
  set (px_ := fst P). set (py_ := snd P).
  set (qx := fst Q). set (qy := snd Q).
  set (tox := fst (T O)). set (toy := snd (T O)).
  set (tpx := fst (T P)). set (tpy := snd (T P)).
  set (tqx := fst (T Q)). set (tqy := snd (T Q)).
  assert (H1: (tpx - tox) * (tpx - tox) + (tpy - toy) * (tpy - toy) =
              (px_ - ox) * (px_ - ox) + (py_ - oy) * (py_ - oy)) by exact Hdist_OP.
  assert (H2: (tqx - tox) * (tqx - tox) + (tqy - toy) * (tqy - toy) =
              (qx - ox) * (qx - ox) + (qy - oy) * (qy - oy)) by exact Hdist_OQ.
  assert (H3: (tqx - tpx) * (tqx - tpx) + (tqy - tpy) * (tqy - tpy) =
              (qx - px_) * (qx - px_) + (qy - py_) * (qy - py_)) by exact Hdist_PQ.
  nra.
Qed.

(** General validity: only distance constraints, no coordinate assumptions *)
Definition linkage_valid_general_full (O A B C D : Point) (L s : R) : Prop :=
  dist_sq O A = L * L /\
  dist_sq O C = L * L /\
  dist_sq A B = s * s /\
  dist_sq B C = s * s /\
  dist_sq C D = s * s /\
  dist_sq D A = s * s /\
  L > s /\ s > 0 /\
  A <> C /\ B <> D /\
  dist O B > 0.

(** The perpendicular line condition in general position *)
Definition D_on_perp_line_general (O M D : Point) (k : R) : Prop :=
  dot_product_from O M D = k * k / 2.

(** Key theorem: The perpendicular line condition is preserved under rigid transforms *)
Lemma perp_line_rigid_invariant : forall T O M D k,
  is_rigid T ->
  D_on_perp_line_general O M D k <->
  D_on_perp_line_general (T O) (T M) (T D) k.
Proof.
  intros T O M D k HT.
  unfold D_on_perp_line_general.
  rewrite (rigid_preserves_dot_product T O M D HT).
  tauto.
Qed.

(** Rigid transforms reflect point inequality: T P = T Q implies P = Q *)
Lemma rigid_reflects_eq : forall T P Q,
  is_rigid T -> T P = T Q -> P = Q.
Proof.
  intros T P Q HT Heq.
  assert (Hdist: dist_sq (T P) (T Q) = dist_sq P Q) by apply HT.
  rewrite Heq in Hdist. rewrite dist_sq_refl in Hdist.
  symmetry in Hdist. apply dist_sq_zero_iff in Hdist.
  unfold point_eq in Hdist. destruct P, Q. simpl in *.
  f_equal; [exact (proj1 Hdist) | exact (proj2 Hdist)].
Qed.

(** Contrapositive: P ≠ Q implies T P ≠ T Q *)
Lemma rigid_preserves_neq : forall T P Q,
  is_rigid T -> P <> Q -> T P <> T Q.
Proof.
  intros T P Q HT Hneq Heq.
  apply Hneq. apply (rigid_reflects_eq T); assumption.
Qed.

(** Rigid transforms preserve dist *)
Lemma rigid_preserves_dist : forall T P Q,
  is_rigid T -> dist (T P) (T Q) = dist P Q.
Proof.
  intros T P Q HT.
  unfold dist. rewrite (rigid_preserves_dist_sq T P Q HT). reflexivity.
Qed.

(** * Section 15: Degenerate Case Analysis *)

(** L > s implies |OA| > |AB|, so A cannot coincide with B *)
Lemma L_gt_s_implies_A_neq_B : forall O A B L s,
  dist O A = L -> dist A B = s -> L > s -> s > 0 -> A <> B.
Proof.
  intros O A B L s HOA HAB HLs Hs Heq.
  rewrite Heq in HAB. rewrite dist_refl in HAB.
  lra.
Qed.

(** Non-zero arm length implies O ≠ A *)
Lemma L_pos_implies_O_neq_A : forall O A L,
  dist O A = L -> L > 0 -> O <> A.
Proof.
  intros O A L HOA HL Heq.
  rewrite Heq in HOA. rewrite dist_refl in HOA.
  lra.
Qed.

(** dist > 0 iff points are distinct *)
Lemma dist_pos_iff_neq : forall P Q,
  dist P Q > 0 <-> P <> Q.
Proof.
  intros P Q. split.
  - intros Hpos Heq. rewrite Heq in Hpos. rewrite dist_refl in Hpos. lra.
  - intros Hneq.
    assert (Hge: dist P Q >= 0) by (apply Rle_ge; apply dist_nonneg).
    destruct (Rle_lt_or_eq_dec 0 (dist P Q)) as [Hlt | Heq].
    + apply Rge_le. exact Hge.
    + exact Hlt.
    + exfalso. apply Hneq.
      assert (Hpeq: point_eq P Q) by (apply dist_zero_iff; lra).
      unfold point_eq in Hpeq. destruct P, Q. simpl in *.
      f_equal; [exact (proj1 Hpeq) | exact (proj2 Hpeq)].
Qed.

(** Linkage validity implies key non-degeneracy conditions *)
Lemma linkage_nondegen_basic : forall O A L s,
  dist O A = L -> L > s -> s > 0 -> O <> A.
Proof.
  intros O A L s HOA HLs Hs.
  apply L_pos_implies_O_neq_A with L; [exact HOA | lra].
Qed.

(** Rhombus side length s > 0 implies adjacent vertices distinct *)
Lemma rhombus_adjacent_neq : forall A B s,
  dist A B = s -> s > 0 -> A <> B.
Proof.
  intros A B s HAB Hs Heq.
  rewrite Heq in HAB. rewrite dist_refl in HAB. lra.
Qed.

(** * Section 16: General Position - Unified Theorem *)

(** This section builds the coordinate-free formulation incrementally. *)

(** Circle through O in general position *)
Definition B_on_circle_through_O_general (O B M : Point) (r : R) : Prop :=
  dist O M = r /\
  r > 0 /\
  dist B M = r.

(** The inversion radius from arm and side lengths *)
Definition inversion_radius (L s : R) : R := sqrt (L * L - s * s).

(** Cross product squared equals product of norms squared minus dot squared *)
Lemma cross_sq_identity : forall a b c d,
  (a * d - b * c) * (a * d - b * c) =
  (a * a + b * b) * (c * c + d * d) - (a * c + b * d) * (a * c + b * d).
Proof. intros. ring. Qed.

(** Collinearity restated: cross product is zero *)
Lemma collinear_cross_zero : forall P Q R,
  collinear P Q R <->
  (fst Q - fst P) * (snd R - snd P) - (snd Q - snd P) * (fst R - fst P) = 0.
Proof.
  intros P Q R. unfold collinear, px, py. lra.
Qed.

(** Rigid transforms preserve cross product squared *)
Lemma rigid_preserves_cross_sq : forall T P Q R,
  is_rigid T ->
  let a := fst Q - fst P in let b := snd Q - snd P in
  let c := fst R - fst P in let d := snd R - snd P in
  let a' := fst (T Q) - fst (T P) in let b' := snd (T Q) - snd (T P) in
  let c' := fst (T R) - fst (T P) in let d' := snd (T R) - snd (T P) in
  (a' * d' - b' * c') * (a' * d' - b' * c') = (a * d - b * c) * (a * d - b * c).
Proof.
  intros T P Q R HT a b c d a' b' c' d'.
  assert (Hdist_PQ: dist_sq (T P) (T Q) = dist_sq P Q) by apply HT.
  assert (Hdist_PR: dist_sq (T P) (T R) = dist_sq P R) by apply HT.
  assert (Hdist_QR: dist_sq (T Q) (T R) = dist_sq Q R) by apply HT.
  unfold dist_sq, px, py, Rsqr in *.
  assert (Ha2b2: a' * a' + b' * b' = a * a + b * b) by (unfold a', b', a, b; nra).
  assert (Hc2d2: c' * c' + d' * d' = c * c + d * d) by (unfold c', d', c, d; nra).
  assert (Hdot: a' * c' + b' * d' = a * c + b * d).
  { unfold a', b', c', d', a, b, c, d.
    assert (Hexp: (fst (T Q) - fst (T R)) * (fst (T Q) - fst (T R)) +
                  (snd (T Q) - snd (T R)) * (snd (T Q) - snd (T R)) =
                  (fst Q - fst R) * (fst Q - fst R) +
                  (snd Q - snd R) * (snd Q - snd R)) by nra.
    nra. }
  rewrite cross_sq_identity. rewrite cross_sq_identity.
  rewrite Ha2b2, Hc2d2, Hdot. reflexivity.
Qed.

(** Rigid transforms preserve collinearity *)
Lemma rigid_preserves_collinear : forall T P Q R,
  is_rigid T ->
  collinear P Q R <-> collinear (T P) (T Q) (T R).
Proof.
  intros T P Q R HT.
  rewrite collinear_cross_zero. rewrite collinear_cross_zero.
  pose proof (rigid_preserves_cross_sq T P Q R HT) as Hsq.
  simpl in Hsq.
  split; intros H.
  - assert (Hzero: (fst Q - fst P) * (snd R - snd P) - (snd Q - snd P) * (fst R - fst P) = 0) by lra.
    assert (Hsq_zero: 0 * 0 = 0) by ring.
    rewrite <- Hzero in Hsq_zero. rewrite <- Hsq in Hsq_zero. nra.
  - assert (Hzero: (fst (T Q) - fst (T P)) * (snd (T R) - snd (T P)) -
                   (snd (T Q) - snd (T P)) * (fst (T R) - fst (T P)) = 0) by lra.
    assert (Hsq_zero: 0 * 0 = 0) by ring.
    rewrite <- Hzero in Hsq_zero. rewrite Hsq in Hsq_zero. nra.
Qed.

(** If O,B,D are collinear, normalizing puts D on x-axis *)
Lemma normalize_D_on_xaxis : forall O B D,
  dist O B > 0 ->
  collinear O B D ->
  snd (normalize_transform O B D) = 0.
Proof.
  intros O B D Hdist Hcol.
  set (T := normalize_transform O B).
  assert (HTO: T O = (0, 0)) by apply normalize_O_at_origin.
  assert (HTB: snd (T B) = 0) by (apply normalize_B_on_xaxis; exact Hdist).
  assert (HTBx: fst (T B) <> 0) by (apply normalize_B_x_nonzero; exact Hdist).
  assert (Hrigid: is_rigid T) by (apply normalize_is_rigid; exact Hdist).
  assert (Hcol': collinear (T O) (T B) (T D)).
  { apply rigid_preserves_collinear; assumption. }
  apply collinear_origin_xaxis with (O := T O) (B := T B).
  - destruct (T O) as [ox oy]. simpl in HTO. injection HTO. intros. exact H0.
  - destruct (T O) as [ox oy]. simpl in HTO. injection HTO. intros. exact H.
  - exact HTB.
  - exact HTBx.
  - exact Hcol'.
Qed.

(** * Section 17: Coordinate-Free Validity *)

(** Coordinate-free linkage validity: only distance constraints *)
(** The same-side condition (B-O)·(D-O) > 0 ensures B and D are on the same
    side of O along their common line, which is the working configuration. *)
Definition linkage_valid_coord_free (O A B C D : Point) (L s : R) : Prop :=
  dist_sq O A = L * L /\
  dist_sq O C = L * L /\
  dist_sq A B = s * s /\
  dist_sq B C = s * s /\
  dist_sq C D = s * s /\
  dist_sq D A = s * s /\
  L > s /\ s > 0 /\
  A <> C /\ B <> D /\
  dot_product_from O B D > 0.

(** Rigid transforms preserve coordinate-free validity *)
Lemma rigid_preserves_validity : forall T O A B C D L s,
  is_rigid T ->
  linkage_valid_coord_free O A B C D L s ->
  linkage_valid_coord_free (T O) (T A) (T B) (T C) (T D) L s.
Proof.
  intros T O A B C D L s HT Hvalid.
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs [Hs [HAC [HBD Hdot]]]]]]]]]].
  unfold linkage_valid_coord_free.
  repeat split.
  - rewrite (rigid_preserves_dist_sq T O A HT). exact HOA.
  - rewrite (rigid_preserves_dist_sq T O C HT). exact HOC.
  - rewrite (rigid_preserves_dist_sq T A B HT). exact HAB.
  - rewrite (rigid_preserves_dist_sq T B C HT). exact HBC.
  - rewrite (rigid_preserves_dist_sq T C D HT). exact HCD.
  - rewrite (rigid_preserves_dist_sq T D A HT). exact HDA.
  - exact HLs.
  - exact Hs.
  - apply rigid_preserves_neq; assumption.
  - apply rigid_preserves_neq; assumption.
  - rewrite (rigid_preserves_dot_product T O B D HT). exact Hdot.
Qed.

(** Product formula is coordinate-invariant: reduction to standard position *)
Theorem product_formula_coord_free : forall O A B C D L s,
  linkage_valid_coord_free O A B C D L s ->
  dist O B > 0 ->
  dist_sq O B * dist_sq O D = (L * L - s * s) * (L * L - s * s).
Proof.
  intros O A B C D L s Hvalid HdistB.
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs [Hs [HAC [HBD Hdot]]]]]]]]]].
  set (T := normalize_transform O B).
  assert (Hrigid: is_rigid T) by (apply normalize_is_rigid; exact HdistB).
  assert (Hinv: dist_sq O B * dist_sq O D = dist_sq (T O) (T B) * dist_sq (T O) (T D)).
  { rewrite (rigid_preserves_dist_sq T O B Hrigid).
    rewrite (rigid_preserves_dist_sq T O D Hrigid). reflexivity. }
  rewrite Hinv.
  assert (HTO: T O = (0, 0)) by apply normalize_O_at_origin.
  assert (HTB_y: snd (T B) = 0) by (apply normalize_B_on_xaxis; exact HdistB).
  assert (Hcol: collinear O B D).
  { apply linkage_OBD_collinear with (L := L) (s := s) (A := A) (C := C); try assumption.
    unfold px, py. destruct A as [ax ay], C as [cx cy].
    destruct (Req_dec ax cx) as [Hxeq|Hxneq].
    - right. intros Hyeq. apply HAC. f_equal; assumption.
    - left. exact Hxneq. }
  assert (HTD_y: snd (T D) = 0) by (apply normalize_D_on_xaxis; assumption).
  assert (HTBneqTD: T B <> T D) by (apply rigid_preserves_neq; assumption).
  assert (HTAneqTC: T A <> T C) by (apply rigid_preserves_neq; assumption).
  apply (product_formula_no_symmetry_assumption (T O) (T A) (T B) (T C) (T D) L s).
  - destruct (T O). simpl in HTO. injection HTO. intros. exact H0.
  - destruct (T O). simpl in HTO. injection HTO. intros. exact H.
  - exact HTB_y.
  - exact HTD_y.
  - exact HTBneqTD.
  - exact HTAneqTC.
  - rewrite (rigid_preserves_dist_sq T O A Hrigid). exact HOA.
  - rewrite (rigid_preserves_dist_sq T O C Hrigid). exact HOC.
  - rewrite (rigid_preserves_dist_sq T A B Hrigid). exact HAB.
  - rewrite (rigid_preserves_dist_sq T B C Hrigid). exact HBC.
  - rewrite (rigid_preserves_dist_sq T C D Hrigid). exact HCD.
  - rewrite (rigid_preserves_dist_sq T D A Hrigid). exact HDA.
  - exact HLs.
  - exact Hs.
Qed.

(** ========== ULTIMATE COORDINATE-FREE THEOREM ========== *)
(**
    The Peaucellier-Lipkin Straight-Line Theorem in General Position:

    D satisfies the perpendicular line condition, which is coordinate-invariant.
    The condition dot_product_from O M D = k²/2 defines a line perpendicular
    to OM at distance k²/(2|OM|) from O.
*)

Theorem peaucellier_straight_line_general : forall O A B C D M L s r,
  linkage_valid_coord_free O A B C D L s ->
  dist O B > 0 ->
  B_on_circle_through_O_general O B M r ->
  D_on_perp_line_general O M D (inversion_radius L s).
Proof.
  intros O A B C D M L s r Hvalid HdistB HBcirc.
  destruct HBcirc as [HOM [Hr HBM]].
  destruct Hvalid as [HOA [HOC [HAB [HBC [HCD [HDA [HLs [Hs [HAC [HBD Hdot_BD]]]]]]]]]].
  unfold D_on_perp_line_general, inversion_radius.
  assert (Hksq_pos: L * L - s * s > 0) by nra.
  rewrite sqrt_sqrt by lra.
  assert (Hprod: dist_sq O B * dist_sq O D = (L * L - s * s) * (L * L - s * s)).
  { apply product_formula_coord_free with (A := A) (C := C).
    - unfold linkage_valid_coord_free. repeat split; assumption.
    - exact HdistB. }
  assert (Hcol: collinear O B D).
  { apply linkage_OBD_collinear with (L := L) (s := s) (A := A) (C := C); try assumption.
    unfold px, py. destruct A as [ax ay], C as [cx cy].
    destruct (Req_dec ax cx) as [Hxeq|Hxneq].
    - right. intros Hyeq. apply HAC. simpl in *. rewrite Hxeq, Hyeq. reflexivity.
    - left. exact Hxneq. }
  assert (HBM': dist M B = r) by (rewrite dist_sym; exact HBM).
  unfold dot_product_from, dist, dist_sq, px, py, Rsqr in *.
  set (Mx := fst M - fst O). set (My := snd M - snd O).
  set (Bx := fst B - fst O). set (By := snd B - snd O).
  set (Dx := fst D - fst O). set (Dy := snd D - snd O).
  assert (HOM_sq: Mx * Mx + My * My = r * r).
  { unfold Mx, My. apply sqrt_eq_implies_sq_eq.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    - left; exact Hr.
    - exact HOM. }
  assert (HBM_sq: (Mx - Bx) * (Mx - Bx) + (My - By) * (My - By) = r * r).
  { unfold Mx, My, Bx, By.
    replace (fst M - fst O - (fst B - fst O)) with (fst M - fst B) by ring.
    replace (snd M - snd O - (snd B - snd O)) with (snd M - snd B) by ring.
    apply sqrt_eq_implies_sq_eq.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    - left; exact Hr.
    - replace ((fst M - fst B) * (fst M - fst B)) with ((fst B - fst M) * (fst B - fst M)) by ring.
      replace ((snd M - snd B) * (snd M - snd B)) with ((snd B - snd M) * (snd B - snd M)) by ring.
      exact HBM'. }
  assert (HdotMB: Mx * Bx + My * By = (Bx * Bx + By * By) / 2).
  { assert (Hexp: (Mx - Bx)*(Mx - Bx) + (My - By)*(My - By) =
                  Mx*Mx + My*My + Bx*Bx + By*By - 2*(Mx*Bx + My*By)) by ring.
    rewrite HBM_sq, HOM_sq in Hexp. lra. }
  assert (HBsq_pos: Bx * Bx + By * By > 0).
  { assert (H: dist_sq O B > 0) by (apply dist_pos_implies_dist_sq_pos; exact HdistB).
    unfold dist_sq, px, py, Rsqr, Bx, By in *. exact H. }
  unfold collinear, px, py in Hcol. fold Bx By Dx Dy in Hcol.
  assert (Hprod': (Bx*Bx + By*By) * (Dx*Dx + Dy*Dy) = (L*L - s*s) * (L*L - s*s)).
  { unfold dist_sq, px, py, Rsqr, Bx, By, Dx, Dy in Hprod. exact Hprod. }
  assert (Hgoal: Mx * Dx + My * Dy = (L * L - s * s) / 2).
  assert (Hdot_pos: Bx * Dx + By * Dy > 0).
  { unfold dot_product_from, Bx, By, Dx, Dy in Hdot_BD. exact Hdot_BD. }
  { destruct (Req_dec Bx 0) as [HBx0|HBx_nz].
    - assert (By_nz: By <> 0) by (rewrite HBx0 in HBsq_pos; nra).
      assert (HDx0: Dx = 0) by (rewrite HBx0 in Hcol; nra).
      assert (HByDy_pos: By * Dy > 0) by (rewrite HBx0, HDx0 in Hdot_pos; nra).
      assert (HDyprod: By * Dy = L*L - s*s).
      { rewrite HBx0, HDx0 in Hprod'.
        assert (H: By * By * (Dy * Dy) = (L*L - s*s) * (L*L - s*s)) by nra.
        assert (Habs: Rabs (By * Dy) = Rabs (L*L - s*s)).
        { apply Rsqr_eq_abs_0. unfold Rsqr. nra. }
        rewrite Rabs_right in Habs by lra.
        rewrite Rabs_right in Habs by lra.
        exact Habs. }
      assert (HMy_half: My = By / 2) by (rewrite HBx0 in HdotMB; nra).
      rewrite HDx0, HMy_half. field_simplify. rewrite HDyprod. lra.
    - destruct (Req_dec By 0) as [HBy0|HBy_nz].
      + assert (HDy0: Dy = 0) by (rewrite HBy0 in Hcol; nra).
        assert (HBxDx_pos: Bx * Dx > 0) by (rewrite HBy0, HDy0 in Hdot_pos; nra).
        assert (HDxprod: Bx * Dx = L*L - s*s).
        { rewrite HBy0, HDy0 in Hprod'.
          assert (H: Bx * Bx * (Dx * Dx) = (L*L - s*s) * (L*L - s*s)) by nra.
          assert (Habs: Rabs (Bx * Dx) = Rabs (L*L - s*s)).
          { apply Rsqr_eq_abs_0. unfold Rsqr. nra. }
          rewrite Rabs_right in Habs by lra.
          rewrite Rabs_right in Habs by lra.
          exact Habs. }
        assert (HMx_half: Mx = Bx / 2) by (rewrite HBy0 in HdotMB; nra).
        rewrite HDy0, HMx_half. field_simplify. rewrite HDxprod. lra.
      + assert (Hratio: Dx / Bx = Dy / By).
        { assert (Hcross: Bx * Dy = By * Dx) by lra.
          apply Rmult_eq_reg_r with (r := Bx); [|exact HBx_nz].
          apply Rmult_eq_reg_r with (r := By); [|exact HBy_nz].
          field_simplify; [|exact HBy_nz|exact HBx_nz]. lra. }
        set (k := Dx / Bx).
        assert (HDx_k: Dx = k * Bx) by (unfold k; field; exact HBx_nz).
        assert (HDy_k: Dy = k * By).
        { unfold k.
          assert (H: Dy / By * By = Dx / Bx * By).
          { rewrite Hratio. reflexivity. }
          field_simplify in H; [|exact HBx_nz|exact HBy_nz].
          replace (Dx / Bx * By) with (By * Dx / Bx) by (field; exact HBx_nz).
          exact H. }
        assert (Hk2: k * k = (L*L - s*s) * (L*L - s*s) / ((Bx*Bx + By*By) * (Bx*Bx + By*By))).
        { rewrite HDx_k, HDy_k in Hprod'.
          replace ((k*Bx)*(k*Bx) + (k*By)*(k*By)) with (k*k*(Bx*Bx + By*By)) in Hprod' by ring.
          assert (HBsq_nz: Bx*Bx + By*By <> 0) by lra.
          assert (HBsq2_nz: (Bx*Bx + By*By) * (Bx*Bx + By*By) <> 0) by nra.
          assert (HBsq2_pos: (Bx*Bx + By*By) * (Bx*Bx + By*By) > 0) by nra.
          assert (Hprod'': k*k * ((Bx*Bx + By*By) * (Bx*Bx + By*By)) = (L*L - s*s) * (L*L - s*s)).
          { nra. }
          apply Rmult_eq_reg_r with (r := (Bx*Bx + By*By) * (Bx*Bx + By*By)); try assumption.
          field_simplify; nra. }
        assert (Hk_val: k = (L*L - s*s) / (Bx*Bx + By*By) \/ k = -(L*L - s*s) / (Bx*Bx + By*By)).
        { assert (Hk2': k² = ((L*L - s*s) / (Bx*Bx + By*By))²).
          { unfold Rsqr. rewrite Hk2.
            assert (HBsq_nz: Bx*Bx + By*By <> 0) by lra.
            field. nra. }
          apply Rsqr_eq in Hk2'.
          destruct Hk2'; [left|right]; lra. }
        rewrite HDx_k, HDy_k.
        replace (Mx * (k * Bx) + My * (k * By)) with (k * (Mx * Bx + My * By)) by ring.
        rewrite HdotMB.
        destruct Hk_val as [Hk_pos|Hk_neg].
        * rewrite Hk_pos. field. lra.
        * rewrite Hk_neg. field_simplify; [|lra].
          exfalso.
          assert (HBDsame_side: Bx * Dx + By * Dy > 0 \/ Bx * Dx + By * Dy < 0 \/ Bx * Dx + By * Dy = 0).
          { lra. }
          rewrite HDx_k, HDy_k in HBDsame_side.
          replace (Bx * (k * Bx) + By * (k * By)) with (k * (Bx*Bx + By*By)) in HBDsame_side by ring.
          rewrite Hk_neg in HBDsame_side.
          assert (Hneg: -(L*L - s*s) / (Bx*Bx + By*By) * (Bx*Bx + By*By) < 0).
          { field_simplify; [|lra]. nra. }
          nra. }
  exact Hgoal.
Qed.

(** * Future Work and Known Gaps

    1. SINGULARITY ANALYSIS (B = O):
       - Prove: B on circle through O with r > 0 implies B ≠ O (isolated singularity)
       - Prove: As |OB| → 0, |OD| → ∞ (D escapes to infinity)
       - Physical interpretation: rigid bars cannot extend infinitely

    2. SURJECTIVITY (Circle-Tracing):
       - Current theorem: D lies ON the output line
       - Missing: D traces the ENTIRE line as B traverses its circle
       - Requires: showing the map B ↦ D is surjective onto the line

    3. INTRINSIC PRODUCT FORMULA:
       - Current: product_formula_standard uses O at origin, B/D on x-axis
       - Improvement: purely inner-product proof without coordinates
       - Approach: use |OB|²|OD|² = (⟨OB,OD⟩/|OB||OD|)² · |OB|²|OD|² with collinearity

    4. MECHANISM RANGE:
       - Prove: valid configurations require |L-s| < |OB| < L+s
       - Prove: D's range on line is bounded by these constraints

    5. INVERSE KINEMATICS:
       - Given D on output line, compute corresponding B position
       - Prove uniqueness (up to reflection) of the inverse

    6. ORGANIZATIONAL REFACTOR:
       - Extract rigid transformation library
       - Consolidate scattered helper lemmas (e.g., sqrt properties, Rsqr lemmas)
       - Unify linkage validity definitions (linkage_valid, linkage_valid_sq,
         linkage_valid_general, linkage_geometric, linkage_geometric_minimal, etc.)
       - Group product formula variants together
*)
