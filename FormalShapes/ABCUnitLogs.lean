import OrderPeriods
import ABCOrders
import ABCBoundedFrames

/-!
# Logarithms of the canonical ABC units

Elementary logarithmic identities used to turn the exponent-lattice basis
of Proposition 4.4 into the actual period basis in Lemma 2.6.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCUnitLogs

open ABCOrders ABCBoundedFrames

variable {A : Type*} [CommRing A]

lemma unitLog_mul (σ : Fin 3 → A →+* ℝ) (x y : Aˣ) :
    OrderPeriods.unitLog σ (x * y) =
      OrderPeriods.unitLog σ x + OrderPeriods.unitLog σ y := by
  funext i
  fin_cases i
  · change Real.log |σ 0 ((x * y : Aˣ) : A)| =
      Real.log |σ 0 (x : A)| + Real.log |σ 0 (y : A)|
    rw [Units.val_mul, map_mul, abs_mul,
      Real.log_mul
        (abs_ne_zero.mpr (OrderPeriods.unit_embedding_ne_zero (σ 0) x))
        (abs_ne_zero.mpr (OrderPeriods.unit_embedding_ne_zero (σ 0) y))]
  · change Real.log |σ 1 ((x * y : Aˣ) : A)| =
      Real.log |σ 1 (x : A)| + Real.log |σ 1 (y : A)|
    rw [Units.val_mul, map_mul, abs_mul,
      Real.log_mul
        (abs_ne_zero.mpr (OrderPeriods.unit_embedding_ne_zero (σ 1) x))
        (abs_ne_zero.mpr (OrderPeriods.unit_embedding_ne_zero (σ 1) y))]

lemma unitLog_inv (σ : Fin 3 → A →+* ℝ) (x : Aˣ) :
    OrderPeriods.unitLog σ x⁻¹ = -OrderPeriods.unitLog σ x := by
  have h := unitLog_mul σ x x⁻¹
  have hone : OrderPeriods.unitLog σ (1 : Aˣ) = 0 := by
    funext i
    fin_cases i <;> simp [OrderPeriods.unitLog]
  rw [mul_inv_cancel, hone] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma unitLog_zpow (σ : Fin 3 → A →+* ℝ) (x : Aˣ) (n : ℤ) :
    OrderPeriods.unitLog σ (x ^ n) = n • OrderPeriods.unitLog σ x := by
  induction n using Int.induction_on with
  | zero => simp [OrderPeriods.unitLog]
  | succ n hn =>
      rw [zpow_add_one (x : Aˣ) (n : ℤ), unitLog_mul, hn,
        add_zsmul, one_zsmul]
  | pred n hn =>
      rw [zpow_sub_one (x : Aˣ) (-(n : ℤ)), unitLog_mul, unitLog_inv, hn,
        sub_zsmul, one_zsmul]

lemma unitLog_canonical_product (P : Parameters) (m n : ℤ) :
    OrderPeriods.unitLog (orderEmbedding P)
        ((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n) =
      m • OrderPeriods.unitLog (orderEmbedding P) (alphaUnit P) +
        n • OrderPeriods.unitLog (orderEmbedding P) (alphaSubOneUnit P) := by
  rw [unitLog_mul, unitLog_zpow, unitLog_zpow]

lemma unitLog_alpha_eq_column_zero (N : ℕ) :
    OrderPeriods.unitLog (orderEmbedding (parameters N))
        (alphaUnit (parameters N)) =
      fun i ↦ unitLogBasis N i 0 := by
  funext i
  fin_cases i
  · simp only [OrderPeriods.unitLog, Matrix.cons_val_zero, coe_alphaUnit,
      orderEmbedding_orderAlpha]
    change Real.log |root0 (parameters N)| = Real.log (root0 (parameters N))
    rw [abs_of_pos (root0_strictBounds _).1]
  · simp only [OrderPeriods.unitLog, Matrix.cons_val_one, coe_alphaUnit,
      orderEmbedding_orderAlpha]
    change Real.log |root1 (parameters N)| = C N
    rw [abs_of_pos]
    · rfl
    · have ha : (3 : ℝ) ≤ (parameters N).a₁ := by
        exact_mod_cast (parameters N).three_le
      linarith [(root1_strictBounds (parameters N)).1]

lemma unitLog_alphaSubOne_eq_column_one (N : ℕ) :
    OrderPeriods.unitLog (orderEmbedding (parameters N))
        (alphaSubOneUnit (parameters N)) =
      fun i ↦ unitLogBasis N i 1 := by
  funext i
  fin_cases i
  · change Real.log |orderEmbedding (parameters N) 0
        (orderAlphaSubOne (parameters N))| = unitLogBasis N 0 1
    rw [orderAlphaSubOne, map_sub, orderEmbedding_orderAlpha]
    have hcast : orderEmbedding (parameters N) 0
        (algebraMap ℤ (orderCarrier (parameters N)) (parameters N).a₁) =
        ((parameters N).a₁ : ℝ) :=
      map_intCast (orderEmbedding (parameters N) 0) (parameters N).a₁
    rw [hcast]
    change Real.log |root0 (parameters N) - (parameters N).a₁| = A N
    rw [abs_of_neg]
    · simp only [neg_sub]
      rfl
    · have ha : (3 : ℝ) ≤ (parameters N).a₁ := by
        exact_mod_cast (parameters N).three_le
      linarith [(root0_strictBounds (parameters N)).2]
  · change Real.log |orderEmbedding (parameters N) 1
        (orderAlphaSubOne (parameters N))| = unitLogBasis N 1 1
    rw [orderAlphaSubOne, map_sub, orderEmbedding_orderAlpha]
    have hcast : orderEmbedding (parameters N) 1
        (algebraMap ℤ (orderCarrier (parameters N)) (parameters N).a₁) =
        ((parameters N).a₁ : ℝ) :=
      map_intCast (orderEmbedding (parameters N) 1) (parameters N).a₁
    rw [hcast]
    change Real.log |root1 (parameters N) - (parameters N).a₁| =
      Real.log (((parameters N).a₁ : ℝ) - root1 (parameters N))
    rw [abs_of_neg (sub_neg.mpr (root1_strictBounds _).2), neg_sub]

lemma unitLog_canonical_product_eq_mulVec (N : ℕ) (m n : ℤ) :
    OrderPeriods.unitLog (orderEmbedding (parameters N))
        ((alphaUnit (parameters N)) ^ m *
          (alphaSubOneUnit (parameters N)) ^ n) =
      (unitLogBasis N).mulVec ![(m : ℝ), (n : ℝ)] := by
  rw [unitLog_canonical_product,
    unitLog_alpha_eq_column_zero, unitLog_alphaSubOne_eq_column_one]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end ABCUnitLogs
end CubicPeriodicTori
