import DynamicsCore
import CRTFamily
import ABCOrders
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The bounded-frame and subsequence step in the final proof

This file follows the final paragraph of Dang--Gargava--Li: root estimates
give a uniformly bounded determinant-one family of logarithmic unit bases,
and compactness supplies a convergent subsequence.  It intentionally does
not identify the limit.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCBoundedFrames

open Filter Set Topology
open ABCOrders

/-- The explicit CRT pair chosen at level `N+1` in the final proof. -/
def parameters (N : ℕ) : Parameters where
  a₁ := localAOne (N + 1)
  a₂ := localATwo (N + 1)
  three_le := by exact_mod_cast (local_parameters_ordered N).1
  lt := by exact_mod_cast (local_parameters_ordered N).2

def scale (N : ℕ) : ℝ := crtModulus (N + 1)

lemma scale_nat (N : ℕ) : scale N = (crtModulus (N + 1) : ℕ) := rfl

lemma scale_ge_thirty (N : ℕ) : 30 ≤ scale N := by
  change (30 : ℝ) ≤ (crtModulus (N + 1) : ℕ)
  rw [crtModulus_eq, pow_succ]
  have hp : 1 ≤ 30 ^ N := Nat.one_le_pow N 30 (by norm_num)
  have hmul := Nat.mul_le_mul_left 30 hp
  simpa [mul_comm] using (show (30 : ℝ) * 1 ≤ 30 * (30 ^ N : ℕ) by
    exact_mod_cast hmul)

lemma scale_pos (N : ℕ) : 0 < scale N := lt_of_lt_of_le (by norm_num) (scale_ge_thirty N)

lemma scale_one_lt (N : ℕ) : 1 < scale N := lt_of_lt_of_le (by norm_num) (scale_ge_thirty N)

lemma log_scale_pos (N : ℕ) : 0 < Real.log (scale N) :=
  Real.log_pos (scale_one_lt N)

private lemma exp_ten_lt_three_pow_ten : Real.exp 10 < (3 : ℝ) ^ 10 := by
  have hpow : Real.exp 1 ^ 10 < (3 : ℝ) ^ 10 :=
    pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
      (by norm_num : 10 ≠ 0)
  have hexp : Real.exp 10 = Real.exp 1 ^ 10 := by
    simpa using Real.exp_nat_mul 1 10
  rwa [hexp]

lemma exp_ten_lt_scale_sq (N : ℕ) (hN : 1 ≤ N) :
    Real.exp 10 < scale N ^ 2 := by
  have hscale : (30 : ℝ) ^ 2 ≤ scale N := by
    rw [scale, crtModulus_eq]
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 30)
      (show 2 ≤ N + 1 by omega))
  calc
    Real.exp 10 < (3 : ℝ) ^ 10 := exp_ten_lt_three_pow_ten
    _ < ((30 : ℝ) ^ 2) ^ 2 := by norm_num
    _ ≤ scale N ^ 2 := by nlinarith

private lemma a₁_lower (N : ℕ) : scale N ^ 2 ≤ (parameters N).a₁ := by
  change (scale N : ℝ) ^ 2 ≤ (localAOne (N + 1) : ℕ)
  rw [scale_nat]
  exact_mod_cast (localAOne_bounds (N + 1)).1

private lemma a₁_upper (N : ℕ) : ((parameters N).a₁ : ℝ) ≤ scale N ^ 2 + scale N := by
  have hnat : localAOne (N + 1) ≤
      crtModulus (N + 1) ^ 2 + crtModulus (N + 1) :=
    Nat.le_of_lt (localAOne_bounds (N + 1)).2
  change (localAOne (N + 1) : ℕ) ≤ scale N ^ 2 + scale N
  rw [scale_nat]
  exact_mod_cast hnat

private lemma a₂_lower (N : ℕ) : 3 * scale N ^ 2 ≤ (parameters N).a₂ := by
  change (3 : ℝ) * scale N ^ 2 ≤ (localATwo (N + 1) : ℕ)
  rw [scale_nat]
  exact_mod_cast (localATwo_bounds (N + 1)).1

private lemma a₂_upper (N : ℕ) : ((parameters N).a₂ : ℝ) ≤
    3 * scale N ^ 2 + scale N := by
  have hnat : localATwo (N + 1) ≤
      3 * crtModulus (N + 1) ^ 2 + crtModulus (N + 1) :=
    Nat.le_of_lt (localATwo_bounds (N + 1)).2
  change (localATwo (N + 1) : ℕ) ≤ 3 * scale N ^ 2 + scale N
  rw [scale_nat]
  exact_mod_cast hnat

/-- The explicit CRT coefficients eventually meet the separation threshold
used in Proposition 3.4 of the paper. -/
lemma parameters_logs_gt_ten (N : ℕ) (hN : 1 ≤ N) :
    10 < Real.log ((parameters N).a₁ : ℝ) ∧
      10 < Real.log (((parameters N).a₂ : ℝ) - (parameters N).a₁) := by
  have hexp := exp_ten_lt_scale_sq N hN
  have ha := a₁_lower N
  have hM := scale_ge_thirty N
  have hgap : scale N ^ 2 ≤
      ((parameters N).a₂ : ℝ) - (parameters N).a₁ := by
    nlinarith [a₂_lower N, a₁_upper N]
  constructor
  · rw [Real.lt_log_iff_exp_lt]
    · exact hexp.trans_le ha
    · exact lt_trans (Real.exp_pos 10) (hexp.trans_le ha)
  · rw [Real.lt_log_iff_exp_lt]
    · exact hexp.trans_le hgap
    · exact lt_trans (Real.exp_pos 10) (hexp.trans_le hgap)

private lemma scale_sq_sub_one_ge_scale (N : ℕ) :
    scale N ≤ scale N ^ 2 - 1 := by
  have h := scale_ge_thirty N
  nlinarith

private lemma three_scale_sq_add_scale_le_cube (N : ℕ) :
    3 * scale N ^ 2 + scale N ≤ scale N ^ 3 := by
  have h := scale_ge_thirty N
  nlinarith [sq_nonneg (scale N - 4)]

private lemma two_scale_sq_sub_scale_ge_scale (N : ℕ) :
    scale N ≤ 2 * scale N ^ 2 - scale N := by
  have h := scale_ge_thirty N
  nlinarith

def A (N : ℕ) : ℝ :=
  Real.log (((parameters N).a₁ : ℝ) - root0 (parameters N))

def B (N : ℕ) : ℝ :=
  Real.log (((parameters N).a₂ : ℝ) - root0 (parameters N))

def C (N : ℕ) : ℝ := Real.log (root1 (parameters N))

def D (N : ℕ) : ℝ :=
  Real.log (((parameters N).a₂ : ℝ) - root1 (parameters N))

private lemma A_argument_bounds (N : ℕ) :
    scale N ≤ ((parameters N).a₁ : ℝ) - root0 (parameters N) ∧
      ((parameters N).a₁ : ℝ) - root0 (parameters N) ≤ scale N ^ 3 := by
  have hr0 := root0_strictBounds (parameters N)
  constructor
  · calc
      scale N ≤ scale N ^ 2 - 1 := scale_sq_sub_one_ge_scale N
      _ ≤ ((parameters N).a₁ : ℝ) - root0 (parameters N) := by
        linarith [a₁_lower N]
  · calc
      ((parameters N).a₁ : ℝ) - root0 (parameters N) ≤
          scale N ^ 2 + scale N := by linarith [a₁_upper N]
      _ ≤ 3 * scale N ^ 2 + scale N := by nlinarith [sq_nonneg (scale N)]
      _ ≤ scale N ^ 3 := three_scale_sq_add_scale_le_cube N

private lemma B_argument_bounds (N : ℕ) :
    scale N ≤ ((parameters N).a₂ : ℝ) - root0 (parameters N) ∧
      ((parameters N).a₂ : ℝ) - root0 (parameters N) ≤ scale N ^ 3 := by
  have hr0 := root0_strictBounds (parameters N)
  constructor
  · calc
      scale N ≤ scale N ^ 2 - 1 := scale_sq_sub_one_ge_scale N
      _ ≤ ((parameters N).a₂ : ℝ) - root0 (parameters N) := by
        linarith [a₂_lower N, sq_nonneg (scale N)]
  · calc
      ((parameters N).a₂ : ℝ) - root0 (parameters N) ≤
          3 * scale N ^ 2 + scale N := by linarith [a₂_upper N]
      _ ≤ scale N ^ 3 := three_scale_sq_add_scale_le_cube N

private lemma C_argument_bounds (N : ℕ) :
    scale N ≤ root1 (parameters N) ∧
      root1 (parameters N) ≤ scale N ^ 3 := by
  have hr1 := root1_strictBounds (parameters N)
  constructor
  · calc
      scale N ≤ scale N ^ 2 - 1 := scale_sq_sub_one_ge_scale N
      _ ≤ root1 (parameters N) := by linarith [a₁_lower N]
  · calc
      root1 (parameters N) ≤ ((parameters N).a₁ : ℝ) := hr1.2.le
      _ ≤ scale N ^ 2 + scale N := a₁_upper N
      _ ≤ 3 * scale N ^ 2 + scale N := by nlinarith [sq_nonneg (scale N)]
      _ ≤ scale N ^ 3 := three_scale_sq_add_scale_le_cube N

private lemma D_argument_bounds (N : ℕ) :
    scale N ≤ ((parameters N).a₂ : ℝ) - root1 (parameters N) ∧
      ((parameters N).a₂ : ℝ) - root1 (parameters N) ≤ scale N ^ 3 := by
  have hr1 := root1_strictBounds (parameters N)
  have hgap : 2 * scale N ^ 2 - scale N ≤
      ((parameters N).a₂ : ℝ) - (parameters N).a₁ := by
    linarith [a₂_lower N, a₁_upper N]
  constructor
  · calc
      scale N ≤ 2 * scale N ^ 2 - scale N := two_scale_sq_sub_scale_ge_scale N
      _ ≤ ((parameters N).a₂ : ℝ) - (parameters N).a₁ := hgap
      _ ≤ ((parameters N).a₂ : ℝ) - root1 (parameters N) := by linarith
  · calc
      ((parameters N).a₂ : ℝ) - root1 (parameters N) ≤
          ((parameters N).a₂ : ℝ) := by
            have hpos : 0 < root1 (parameters N) := by
              have ha : (3 : ℝ) ≤ ((parameters N).a₁ : ℝ) := by
                exact_mod_cast (parameters N).three_le
              linarith [hr1.1]
            linarith
      _ ≤ 3 * scale N ^ 2 + scale N := a₂_upper N
      _ ≤ scale N ^ 3 := three_scale_sq_add_scale_le_cube N

private lemma log_bounds_of_scale_le_of_le_cube (N : ℕ) {x : ℝ}
    (hx : scale N ≤ x) (hx' : x ≤ scale N ^ 3) :
    Real.log (scale N) ≤ Real.log x ∧
      Real.log x ≤ 3 * Real.log (scale N) := by
  have hs := scale_pos N
  have hxpos := lt_of_lt_of_le hs hx
  constructor
  · exact Real.strictMonoOn_log.monotoneOn hs hxpos hx
  · calc
      Real.log x ≤ Real.log (scale N ^ 3) :=
        Real.strictMonoOn_log.monotoneOn hxpos (pow_pos hs 3) hx'
      _ = 3 * Real.log (scale N) := by rw [Real.log_pow]; norm_num

lemma A_bounds (N : ℕ) :
    Real.log (scale N) ≤ A N ∧ A N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (A_argument_bounds N).1 (A_argument_bounds N).2

lemma B_bounds (N : ℕ) :
    Real.log (scale N) ≤ B N ∧ B N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (B_argument_bounds N).1 (B_argument_bounds N).2

lemma C_bounds (N : ℕ) :
    Real.log (scale N) ≤ C N ∧ C N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (C_argument_bounds N).1 (C_argument_bounds N).2

lemma D_bounds (N : ℕ) :
    Real.log (scale N) ≤ D N ∧ D N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (D_argument_bounds N).1 (D_argument_bounds N).2

private lemma root0_product (N : ℕ) :
    root0 (parameters N) *
        (((parameters N).a₁ : ℝ) - root0 (parameters N)) *
        (((parameters N).a₂ : ℝ) - root0 (parameters N)) = 1 := by
  have h := realRoot_root (parameters N) (0 : Fin 3)
  rw [Polynomial.IsRoot, abcPolynomialR_eval] at h
  change root0 (parameters N) *
      (root0 (parameters N) - (parameters N).a₁) *
      (root0 (parameters N) - (parameters N).a₂) - 1 = 0 at h
  nlinarith

private lemma root1_product (N : ℕ) :
    root1 (parameters N) *
        (((parameters N).a₁ : ℝ) - root1 (parameters N)) *
        (((parameters N).a₂ : ℝ) - root1 (parameters N)) = 1 := by
  have h := realRoot_root (parameters N) (1 : Fin 3)
  rw [Polynomial.IsRoot, abcPolynomialR_eval] at h
  change root1 (parameters N) *
      (root1 (parameters N) - (parameters N).a₁) *
      (root1 (parameters N) - (parameters N).a₂) - 1 = 0 at h
  nlinarith

private lemma root0_log (N : ℕ) :
    Real.log (root0 (parameters N)) = -(A N + B N) := by
  have hr : 0 < root0 (parameters N) := (root0_strictBounds _).1
  have ha : 0 < ((parameters N).a₁ : ℝ) - root0 (parameters N) := by
    linarith [(root0_strictBounds (parameters N)).2,
      (show (3 : ℝ) ≤ (parameters N).a₁ by
        exact_mod_cast (parameters N).three_le)]
  have hb : 0 < ((parameters N).a₂ : ℝ) - root0 (parameters N) := by
    have hp : ((parameters N).a₁ : ℝ) < (parameters N).a₂ := by
      exact_mod_cast (parameters N).lt
    linarith
  have hlog := congrArg Real.log (root0_product N)
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hr) (ne_of_gt ha)) (ne_of_gt hb),
    Real.log_mul (ne_of_gt hr) (ne_of_gt ha)] at hlog
  simp only [Real.log_one] at hlog
  change Real.log (root0 (parameters N)) + A N + B N = 0 at hlog
  linarith

private lemma root1_sub_log (N : ℕ) :
    Real.log (((parameters N).a₁ : ℝ) - root1 (parameters N)) =
      -(C N + D N) := by
  have hr : 0 < root1 (parameters N) := by
    have ha : (3 : ℝ) ≤ (parameters N).a₁ := by
      exact_mod_cast (parameters N).three_le
    linarith [(root1_strictBounds (parameters N)).1]
  have ha : 0 < ((parameters N).a₁ : ℝ) - root1 (parameters N) :=
    sub_pos.mpr (root1_strictBounds _).2
  have hb : 0 < ((parameters N).a₂ : ℝ) - root1 (parameters N) := by
    have hp : ((parameters N).a₁ : ℝ) < (parameters N).a₂ := by
      exact_mod_cast (parameters N).lt
    linarith [(root1_strictBounds (parameters N)).2]
  have hlog := congrArg Real.log (root1_product N)
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hr) (ne_of_gt ha)) (ne_of_gt hb),
    Real.log_mul (ne_of_gt hr) (ne_of_gt ha)] at hlog
  simp only [Real.log_one] at hlog
  change C N + Real.log (((parameters N).a₁ : ℝ) - root1 (parameters N)) +
    D N = 0 at hlog
  linarith

/-- The logarithmic basis of the two ABC units, with the first two real
places as coordinates, exactly as in Lemmas 3.2 and 3.5 of the paper. -/
def unitLogBasis (N : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.log (root0 (parameters N)), A N;
     C N, Real.log (((parameters N).a₁ : ℝ) - root1 (parameters N))]

lemma unitLogBasis_eq (N : ℕ) :
    unitLogBasis N = !![-(A N + B N), A N; C N, -(C N + D N)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change Real.log (root0 (parameters N)) = -(A N + B N)
    exact root0_log N
  · rfl
  · rfl
  · change Real.log (((parameters N).a₁ : ℝ) - root1 (parameters N)) =
      -(C N + D N)
    exact root1_sub_log N

lemma unitLogBasis_det (N : ℕ) :
    (unitLogBasis N).det = A N * D N + B N * C N + B N * D N := by
  rw [unitLogBasis_eq, Matrix.det_fin_two]
  simp
  ring

lemma unitLogBasis_det_lower (N : ℕ) :
    Real.log (scale N) ^ 2 ≤ (unitLogBasis N).det := by
  rw [unitLogBasis_det]
  have hL : 0 ≤ Real.log (scale N) := (log_scale_pos N).le
  have hA := A_bounds N
  have hB := B_bounds N
  have hC := C_bounds N
  have hD := D_bounds N
  have hAD : Real.log (scale N) ^ 2 ≤ A N * D N := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA.1) (sub_nonneg.mpr hD.1)]
  have hBC : 0 ≤ B N * C N := mul_nonneg (hL.trans hB.1) (hL.trans hC.1)
  have hBD : 0 ≤ B N * D N := mul_nonneg (hL.trans hB.1) (hL.trans hD.1)
  linarith

lemma unitLogBasis_det_pos (N : ℕ) : 0 < (unitLogBasis N).det := by
  have hL := log_scale_pos N
  have hsq : 0 < Real.log (scale N) ^ 2 := sq_pos_of_pos hL
  exact lt_of_lt_of_le hsq (unitLogBasis_det_lower N)

lemma unitLogBasis_entry_abs_le (N : ℕ) (i j : Fin 2) :
    |unitLogBasis N i j| ≤ 6 * Real.log (scale N) := by
  rw [unitLogBasis_eq]
  have hL := log_scale_pos N
  have hA := A_bounds N
  have hB := B_bounds N
  have hC := C_bounds N
  have hD := D_bounds N
  fin_cases i <;> fin_cases j
  · change |-(A N + B N)| ≤ 6 * Real.log (scale N)
    rw [abs_of_nonpos]
    · linarith
    · linarith
  · change |A N| ≤ 6 * Real.log (scale N)
    rw [abs_of_nonneg]
    · linarith
    · linarith
  · change |C N| ≤ 6 * Real.log (scale N)
    rw [abs_of_nonneg]
    · linarith
    · linarith
  · change |-(C N + D N)| ≤ 6 * Real.log (scale N)
    rw [abs_of_nonpos]
    · linarith
    · linarith

/-- The determinant-one representative of the logarithmic unit basis. -/
def baseFrame (N : ℕ) : SL2R :=
  normalizeBasis (unitLogBasis N) (unitLogBasis_det_pos N)

private lemma log_scale_le_sqrt_det (N : ℕ) :
    Real.log (scale N) ≤ Real.sqrt (unitLogBasis N).det := by
  calc
    Real.log (scale N) = Real.sqrt (Real.log (scale N) ^ 2) := by
      rw [Real.sqrt_sq (log_scale_pos N).le]
    _ ≤ Real.sqrt (unitLogBasis N).det :=
      Real.sqrt_le_sqrt (unitLogBasis_det_lower N)

/-- Uniform coordinate boundedness asserted in the paper's compactness step. -/
lemma baseFrame_entry_abs_le (N : ℕ) (i j : Fin 2) :
    |(baseFrame N : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 6 := by
  let s := Real.sqrt (unitLogBasis N).det
  have hs : 0 < s := Real.sqrt_pos.2 (unitLogBasis_det_pos N)
  have hLs : Real.log (scale N) ≤ s := log_scale_le_sqrt_det N
  have he := unitLogBasis_entry_abs_le N i j
  change |s⁻¹ * unitLogBasis N i j| ≤ 6
  rw [abs_mul, abs_inv, abs_of_nonneg hs.le]
  calc
    s⁻¹ * |unitLogBasis N i j| ≤
        s⁻¹ * (6 * Real.log (scale N)) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hs.le)
    _ ≤ 6 := by
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ hs).2 (by nlinarith)

end ABCBoundedFrames
end CubicPeriodicTori
