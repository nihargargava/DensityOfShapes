import ABCOrders
import SuborderUnits
import ArithmeticConstruction
import Mathlib.Tactic.FinCases

/-!
# The concrete local unit calculation for the ABC orders

This file formalizes Proposition 4.4 of Dang--Gargava--Li for the primes
`(2,3,5)`.  The proof follows the paper: reduce the three canonical units
locally, use `b₁ b₂ b₃ = 1`, and apply the prime-power calculation of
Lemma 4.2 for the odd primes and Lemma 4.3 at `2`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCLocalUnits

open ABCOrders ArithmeticConstruction

/-- The six congruences in Proposition 4.4, specialized to `(2,3,5)`.
The coefficients of an `ABCOrders.Parameters` object are integers, so this
is the integral version of the predicate used by the final CRT construction. -/
def SatisfiesLocalConditions (c d r : ℕ) (a₁ a₂ : ℤ) : Prop :=
  a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c] ∧ a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c] ∧
  a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d] ∧ a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d] ∧
  a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r] ∧ a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]

/-- Reduction modulo `q` of the matrix of multiplication by `x` in the
power basis `(1,α,α²)`. -/
def reducedLeftMulMatrix (P : Parameters) (q : ℕ) (x : orderCarrier P) :
    Matrix (Fin 3) (Fin 3) (ZMod q) :=
  (Algebra.leftMulMatrix (orderBasis P) x).map
    (Int.castRingHom (ZMod q))

/-- Membership in `ℤ + qO` is exactly scalarity of multiplication by the
element after reduction modulo `q`. -/
lemma mem_scalarSuborder_iff_isScalar_reduced
    (P : Parameters) (q : ℕ) (x : orderCarrier P) :
    x ∈ scalarSuborder P q ↔
      SuborderUnits.IsScalar (reducedLeftMulMatrix P q x) := by
  rw [mem_scalarSuborder_iff_repr_dvd]
  change (_ ∣ _ ∧ _ ∣ _) ↔ SuborderUnits.IsScalar
    ((Algebra.leftMulMatrix (orderBasis P) x).map
      (Int.castRingHom (ZMod q)))
  rw [← SuborderUnits.inScalarOrder_matrix_iff_isScalar_map]
  simp [SuborderUnits.InScalarOrder, SuborderUnits.matrixTail,
    Algebra.leftMulMatrix_eq_repr_mul]

/-- Multiplication by the second canonical unit `α-a₁`. -/
lemma leftMulMatrix_orderAlphaSubOne (P : Parameters) :
    Algebra.leftMulMatrix (orderBasis P) (orderAlphaSubOne P) =
      SuborderUnits.shiftedCompanion ℤ (P.a₁ + P.a₂)
        (P.a₁ * P.a₂) P.a₁ := by
  rw [orderAlphaSubOne, map_sub, leftMulMatrix_orderAlpha]
  unfold SuborderUnits.shiftedCompanion
  rw [AlgHom.commutes]
  rw [Algebra.algebraMap_eq_smul_one]

/-- Multiplication by the third canonical unit `α-a₂`. -/
lemma leftMulMatrix_orderAlphaSubTwo (P : Parameters) :
    Algebra.leftMulMatrix (orderBasis P) (orderAlphaSubTwo P) =
      SuborderUnits.shiftedCompanion ℤ (P.a₁ + P.a₂)
        (P.a₁ * P.a₂) P.a₂ := by
  rw [orderAlphaSubTwo, map_sub, leftMulMatrix_orderAlpha]
  unfold SuborderUnits.shiftedCompanion
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

/-- Multiplication matrices, bundled on units. -/
def leftMulUnitHom (P : Parameters) :
    (orderCarrier P)ˣ →* (Matrix (Fin 3) (Fin 3) ℤ)ˣ :=
  Units.map (Algebra.leftMulMatrix (orderBasis P)).toRingHom.toMonoidHom

/-- Entrywise reduction modulo `q`, bundled on matrix units. -/
def reduceMatrixUnitHom (q : ℕ) :
    (Matrix (Fin 3) (Fin 3) ℤ)ˣ →*
      (Matrix (Fin 3) (Fin 3) (ZMod q))ˣ :=
  Units.map (RingHom.mapMatrix (Int.castRingHom (ZMod q))).toMonoidHom

/-- The local multiplication matrix of an ABC unit. -/
def reducedUnitMatrix (P : Parameters) (q : ℕ) (u : (orderCarrier P)ˣ) :
    (Matrix (Fin 3) (Fin 3) (ZMod q))ˣ :=
  reduceMatrixUnitHom q (leftMulUnitHom P u)

@[simp] lemma coe_reducedUnitMatrix (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) :
    (reducedUnitMatrix P q u : Matrix (Fin 3) (Fin 3) (ZMod q)) =
      reducedLeftMulMatrix P q (u : orderCarrier P) := by
  simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom,
    reducedLeftMulMatrix]

/-- Scalar-suborder membership for a unit can be read from its local
multiplication matrix. -/
lemma unit_mem_scalarSuborder_iff (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) :
    (u : orderCarrier P) ∈ scalarSuborder P q ↔
      SuborderUnits.IsScalar
        (reducedUnitMatrix P q u : Matrix (Fin 3) (Fin 3) (ZMod q)) := by
  rw [coe_reducedUnitMatrix]
  exact mem_scalarSuborder_iff_isScalar_reduced P q u

private lemma zmod_eq_of_modEq (q : ℕ) {a b : ℤ}
    (h : a ≡ b [ZMOD (q : ℤ)]) : (a : ZMod q) = (b : ZMod q) := by
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).2
    (Int.modEq_iff_dvd.mp h)

lemma reduced_orderAlpha_eq_common_of_zero_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (orderAlpha P) =
      SuborderUnits.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderAlpha,
    SuborderUnits.map_companion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 0 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

lemma reduced_orderAlpha_eq_common_of_one_zero
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (orderAlpha P) =
      SuborderUnits.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderAlpha,
    SuborderUnits.map_companion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 0 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

lemma reduced_orderAlphaSubOne_eq_five_of_one_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (orderAlphaSubOne P) =
      SuborderUnits.shiftedCompanion (ZMod q) 2 1 1 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderAlphaSubOne,
    SuborderUnits.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

lemma reduced_orderAlphaSubOne_eq_common_of_zero_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (orderAlphaSubOne P) =
      SuborderUnits.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderAlphaSubOne,
    SuborderUnits.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 0 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  simp [SuborderUnits.shiftedCompanion]

lemma reduced_orderAlphaSubTwo_eq_common_of_one_zero
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (orderAlphaSubTwo P) =
      SuborderUnits.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderAlphaSubTwo,
    SuborderUnits.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 0 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  simp [SuborderUnits.shiftedCompanion]

lemma reduced_orderAlphaSubTwo_eq_five_of_one_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (orderAlphaSubTwo P) =
      SuborderUnits.shiftedCompanion (ZMod q) 2 1 1 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderAlphaSubTwo,
    SuborderUnits.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

private lemma common_two_isScalar_pow_iff (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    SuborderUnits.IsScalar
        (SuborderUnits.companion (ZMod (2 ^ c)) 1 0 ^ n) ↔
      7 * 2 ^ (c - 1) ∣ n := by
  have h := SuborderUnits.integerTwo_power_law c hc n
  rw [SuborderUnits.inScalarOrder_matrix_iff_isScalar_map,
    Matrix.map_pow, SuborderUnits.map_integerCommonMatrix] at h
  exact h

private lemma common_three_isScalar_pow_iff (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    SuborderUnits.IsScalar
        (SuborderUnits.companion (ZMod (3 ^ d)) 1 0 ^ n) ↔
      8 * 3 ^ (d - 1) ∣ n := by
  have h := SuborderUnits.integerThree_power_law d hd n
  rw [SuborderUnits.inScalarOrder_matrix_iff_isScalar_map,
    Matrix.map_pow, SuborderUnits.map_integerCommonMatrix] at h
  exact h

private lemma five_isScalar_pow_iff (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    SuborderUnits.IsScalar
        (SuborderUnits.shiftedCompanion (ZMod (5 ^ r)) 2 1 1 ^ n) ↔
      24 * 5 ^ (r - 1) ∣ n := by
  have h := SuborderUnits.integerFive_power_law r hr n
  rw [SuborderUnits.inScalarOrder_matrix_iff_isScalar_map,
    Matrix.map_pow, SuborderUnits.map_integerFiveMatrix] at h
  exact h

/-- The `2`-primary instance of Lemma 4.3 for `b₁=α`. -/
theorem alpha_nat_power_law_two (P : Parameters) (c : ℕ) (hc : 1 ≤ c)
    (h₁ : P.a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c])
    (h₂ : P.a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c]) (n : ℕ) :
    (((alphaUnit P) ^ n : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (2 ^ c) ↔
      7 * 2 ^ (c - 1) ∣ n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 0 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₂
  have hred := reduced_orderAlpha_eq_common_of_zero_one P (2 ^ c) h₁' h₂'
  change SuborderUnits.IsScalar
      (reducedUnitMatrix P (2 ^ c) ((alphaUnit P) ^ n)).val ↔ _
  rw [show reducedUnitMatrix P (2 ^ c) ((alphaUnit P) ^ n) =
      (reducedUnitMatrix P (2 ^ c) (alphaUnit P)) ^ n by
        simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]]
  rw [Units.val_pow_eq_pow_val, coe_reducedUnitMatrix,
    coe_alphaUnit, hred]
  exact common_two_isScalar_pow_iff c hc n

/-- The `3`-primary instance of Lemma 4.2 for `b₁=α`. -/
theorem alpha_nat_power_law_three (P : Parameters) (d : ℕ) (hd : 1 ≤ d)
    (h₁ : P.a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d])
    (h₂ : P.a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d]) (n : ℕ) :
    (((alphaUnit P) ^ n : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (3 ^ d) ↔
      8 * 3 ^ (d - 1) ∣ n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 0 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₂
  have hred := reduced_orderAlpha_eq_common_of_one_zero P (3 ^ d) h₁' h₂'
  change SuborderUnits.IsScalar
      (reducedUnitMatrix P (3 ^ d) ((alphaUnit P) ^ n)).val ↔ _
  rw [show reducedUnitMatrix P (3 ^ d) ((alphaUnit P) ^ n) =
      (reducedUnitMatrix P (3 ^ d) (alphaUnit P)) ^ n by
        simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]]
  rw [Units.val_pow_eq_pow_val, coe_reducedUnitMatrix,
    coe_alphaUnit, hred]
  exact common_three_isScalar_pow_iff d hd n

/-- The `5`-primary instance of Lemma 4.2 for `b₂=α-a₁`. -/
theorem alphaSubOne_nat_power_law_five (P : Parameters) (r : ℕ)
    (hr : 1 ≤ r)
    (h₁ : P.a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r])
    (h₂ : P.a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]) (n : ℕ) :
    (((alphaSubOneUnit P) ^ n : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (5 ^ r) ↔
      24 * 5 ^ (r - 1) ∣ n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₂
  have hred := reduced_orderAlphaSubOne_eq_five_of_one_one
    P (5 ^ r) h₁' h₂'
  change SuborderUnits.IsScalar
      (reducedUnitMatrix P (5 ^ r) ((alphaSubOneUnit P) ^ n)).val ↔ _
  rw [show reducedUnitMatrix P (5 ^ r) ((alphaSubOneUnit P) ^ n) =
      (reducedUnitMatrix P (5 ^ r) (alphaSubOneUnit P)) ^ n by
        simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]]
  rw [Units.val_pow_eq_pow_val, coe_reducedUnitMatrix,
    coe_alphaSubOneUnit, hred]
  exact five_isScalar_pow_iff r hr n

/-!
The paper uses integral exponents.  The following is the omitted elementary
justification that scalar-suborder membership is invariant under inversion
for an ambient unit.  In coordinates, if `u = a + qy`, the equation
`u u⁻¹ = 1` says that `a` is coprime to `q`; hence the two tail
coordinates of `u⁻¹` are divisible by `q`.
-/

private lemma unit_inv_mem_of_mem (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ)
    (hu : (u : orderCarrier P) ∈ scalarSuborder P q) :
    ((u⁻¹ : (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q := by
  rcases hu with ⟨a, y, huy⟩
  let v : orderCarrier P := ((u⁻¹ : (orderCarrier P)ˣ) : orderCarrier P)
  have huv : (u : orderCarrier P) * v = 1 := Units.val_inv u
  have huv' : (algebraMap ℤ (orderCarrier P) a + q • y) * v = 1 := by
    rw [← huy]
    exact huv
  have huv'' :
      algebraMap ℤ (orderCarrier P) a * v +
        algebraMap ℤ (orderCarrier P) (q : ℤ) * (y * v) = 1 := by
    calc
      _ = (algebraMap ℤ (orderCarrier P) a + q • y) * v := by
        simp only [nsmul_eq_mul]
        push_cast
        ring
      _ = 1 := huv'
  have hrepr (z : ℤ) (w : orderCarrier P) (i : Fin 3) :
      (orderBasis P).repr (algebraMap ℤ (orderCarrier P) z * w) i =
        z * (orderBasis P).repr w i := by
    rw [← Algebra.smul_def]
    exact DFunLike.congr_fun ((orderBasis P).repr.map_smul z w) i
  have hone (i : Fin 3) :
      (orderBasis P).repr (1 : orderCarrier P) i =
        if i = 0 then 1 else 0 := by
    rw [← orderBasis_zero P]
    simp only [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hcoord (i : Fin 3) :
      a * (orderBasis P).repr v i +
          (q : ℤ) * (orderBasis P).repr (y * v) i =
        if i = 0 then 1 else 0 := by
    have hi := congrArg (fun z : orderCarrier P => (orderBasis P).repr z i) huv''
    rw [map_add, Finsupp.add_apply, hrepr, hrepr, hone] at hi
    exact hi
  have hcop : IsCoprime (q : ℤ) a := by
    refine ⟨(orderBasis P).repr (y * v) 0, (orderBasis P).repr v 0, ?_⟩
    have hzero := hcoord 0
    norm_num at hzero ⊢
    linarith
  rw [mem_scalarSuborder_iff_repr_dvd]
  constructor
  · have hone := hcoord 1
    simp only [if_neg (by decide : (1 : Fin 3) ≠ 0)] at hone
    apply hcop.dvd_of_dvd_mul_left
    exact ⟨-(orderBasis P).repr (y * v) 1, by linarith⟩
  · have htwo := hcoord 2
    simp only [if_neg (by decide : (2 : Fin 3) ≠ 0)] at htwo
    apply hcop.dvd_of_dvd_mul_left
    exact ⟨-(orderBasis P).repr (y * v) 2, by linarith⟩

lemma unit_inv_mem_scalarSuborder_iff (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) :
    (((u⁻¹ : (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) ↔
      ((u : orderCarrier P) ∈ scalarSuborder P q) := by
  constructor
  · intro h
    have hi := unit_inv_mem_of_mem P q (u⁻¹) h
    simpa using hi
  · exact unit_inv_mem_of_mem P q u

lemma unit_neg_pow_mem_scalarSuborder_iff (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) (n : ℕ) :
    (((u ^ (-(n : ℤ)) : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P q) ↔
      (((u ^ n : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P q) := by
  rw [zpow_neg, unit_inv_mem_scalarSuborder_iff]
  simp only [zpow_natCast]

private def UnitPowerMembership (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) (z : ℤ) : Prop :=
  (((u ^ z : (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q)

private theorem int_power_law_of_nat
    (P : Parameters) (q N : ℕ) (u : (orderCarrier P)ˣ)
    (hnat : ∀ n : ℕ,
      UnitPowerMembership P q u n ↔ N ∣ n) (z : ℤ) :
    UnitPowerMembership P q u z ↔ (N : ℤ) ∣ z := by
  apply SuborderUnits.int_power_law_of_nat_of_neg
    (UnitPowerMembership P q u) N hnat
  intro n
  exact unit_neg_pow_mem_scalarSuborder_iff P q u n

/-- Integral-exponent `2`-power law, as used in Proposition 4.4. -/
theorem alpha_int_power_law_two (P : Parameters) (c : ℕ) (hc : 1 ≤ c)
    (h₁ : P.a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c])
    (h₂ : P.a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c]) (z : ℤ) :
    UnitPowerMembership P (2 ^ c) (alphaUnit P) z ↔
      (7 * 2 ^ (c - 1) : ℤ) ∣ z := by
  exact int_power_law_of_nat P (2 ^ c) (7 * 2 ^ (c - 1))
    (alphaUnit P) (alpha_nat_power_law_two P c hc h₁ h₂) z

/-- Integral-exponent `3`-power law, as used in Proposition 4.4. -/
theorem alpha_int_power_law_three (P : Parameters) (d : ℕ) (hd : 1 ≤ d)
    (h₁ : P.a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d])
    (h₂ : P.a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d]) (z : ℤ) :
    UnitPowerMembership P (3 ^ d) (alphaUnit P) z ↔
      (8 * 3 ^ (d - 1) : ℤ) ∣ z := by
  exact int_power_law_of_nat P (3 ^ d) (8 * 3 ^ (d - 1))
    (alphaUnit P) (alpha_nat_power_law_three P d hd h₁ h₂) z

/-- Integral-exponent `5`-power law, as used in Proposition 4.4. -/
theorem alphaSubOne_int_power_law_five (P : Parameters) (r : ℕ)
    (hr : 1 ≤ r)
    (h₁ : P.a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r])
    (h₂ : P.a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]) (z : ℤ) :
    UnitPowerMembership P (5 ^ r) (alphaSubOneUnit P) z ↔
      (24 * 5 ^ (r - 1) : ℤ) ∣ z := by
  exact int_power_law_of_nat P (5 ^ r) (24 * 5 ^ (r - 1))
    (alphaSubOneUnit P) (alphaSubOne_nat_power_law_five P r hr h₁ h₂) z

/-! ### The three local reductions in the proof of Proposition 4.4 -/

private lemma alpha_units_product (P : Parameters) :
    alphaUnit P * alphaSubOneUnit P * alphaSubTwoUnit P = 1 := by
  apply Units.val_injective
  simpa using order_generators_mul P

private lemma alphaSubTwoUnit_eq_inv_mul_inv (P : Parameters) :
    alphaSubTwoUnit P = (alphaUnit P)⁻¹ * (alphaSubOneUnit P)⁻¹ := by
  have h := alpha_units_product P
  have hc : alphaSubTwoUnit P =
      (alphaUnit P * alphaSubOneUnit P)⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  rw [hc, mul_inv_rev, mul_comm]

private lemma scalarSuborder.unit_mul_mem_iff_left
    (P : Parameters) (q : ℕ) (u v : (orderCarrier P)ˣ)
    (hv : (v : orderCarrier P) ∈ scalarSuborder P q) :
    (((u * v : (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) ↔
      ((u : orderCarrier P) ∈ scalarSuborder P q) := by
  constructor
  · intro huv
    have hvinv := unit_inv_mem_of_mem P q v hv
    have hmul := (scalarSuborder P q).mul_mem huv hvinv
    simpa [mul_assoc] using hmul
  · intro hu
    exact (scalarSuborder P q).mul_mem hu hv

private lemma scalarSuborder.unit_mul_mem_iff_right
    (P : Parameters) (q : ℕ) (u v : (orderCarrier P)ˣ)
    (hu : (u : orderCarrier P) ∈ scalarSuborder P q) :
    (((u * v : (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) ↔
      ((v : orderCarrier P) ∈ scalarSuborder P q) := by
  rw [mul_comm]
  exact scalarSuborder.unit_mul_mem_iff_left P q v u hu

private lemma reduced_alpha_eq_alphaSubOne_of_zero_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (alphaUnit P) =
      reducedUnitMatrix P q (alphaSubOneUnit P) := by
  apply Units.val_injective
  rw [coe_reducedUnitMatrix, coe_reducedUnitMatrix,
    coe_alphaUnit, coe_alphaSubOneUnit,
    reduced_orderAlpha_eq_common_of_zero_one P q h₁ h₂,
    reduced_orderAlphaSubOne_eq_common_of_zero_one P q h₁ h₂]

private lemma reduced_alpha_eq_alphaSubTwo_of_one_zero
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (alphaUnit P) =
      reducedUnitMatrix P q (alphaSubTwoUnit P) := by
  apply Units.val_injective
  rw [coe_reducedUnitMatrix, coe_reducedUnitMatrix,
    coe_alphaUnit, coe_alphaSubTwoUnit,
    reduced_orderAlpha_eq_common_of_one_zero P q h₁ h₂,
    reduced_orderAlphaSubTwo_eq_common_of_one_zero P q h₁ h₂]

private lemma reduced_alphaSubOne_eq_alphaSubTwo_of_one_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (alphaSubOneUnit P) =
      reducedUnitMatrix P q (alphaSubTwoUnit P) := by
  apply Units.val_injective
  rw [coe_reducedUnitMatrix, coe_reducedUnitMatrix,
    coe_alphaSubOneUnit, coe_alphaSubTwoUnit,
    reduced_orderAlphaSubOne_eq_five_of_one_one P q h₁ h₂,
    reduced_orderAlphaSubTwo_eq_five_of_one_one P q h₁ h₂]

private lemma reducedUnitMatrix_map_mul (P : Parameters) (q : ℕ)
    (u v : (orderCarrier P)ˣ) :
    reducedUnitMatrix P q (u * v) =
      reducedUnitMatrix P q u * reducedUnitMatrix P q v := by
  simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]

private lemma reducedUnitMatrix_map_zpow (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) (z : ℤ) :
    reducedUnitMatrix P q (u ^ z) = (reducedUnitMatrix P q u) ^ z := by
  simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]

private lemma reducedUnitMatrix_map_one (P : Parameters) (q : ℕ) :
    reducedUnitMatrix P q 1 = 1 := by
  simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]

private lemma reduced_product_two
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) (m n : ℤ) :
    reducedUnitMatrix P q ((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n) =
      reducedUnitMatrix P q ((alphaUnit P) ^ (m + n)) := by
  rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_zpow,
    reducedUnitMatrix_map_zpow, reducedUnitMatrix_map_zpow,
    ← reduced_alpha_eq_alphaSubOne_of_zero_one P q h₁ h₂,
    zpow_add]

private lemma reduced_alphaSubOne_eq_alpha_neg_two
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (alphaSubOneUnit P) =
      (reducedUnitMatrix P q (alphaUnit P)) ^ (-2 : ℤ) := by
  let A := reducedUnitMatrix P q (alphaUnit P)
  let B := reducedUnitMatrix P q (alphaSubOneUnit P)
  let C := reducedUnitMatrix P q (alphaSubTwoUnit P)
  have hAC : A = C := reduced_alpha_eq_alphaSubTwo_of_one_zero P q h₁ h₂
  have hprod : A * B * C = 1 := by
    have h := congrArg (fun u => reducedUnitMatrix P q u)
      (alpha_units_product P)
    rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_mul,
      reducedUnitMatrix_map_one] at h
    exact h
  rw [← hAC] at hprod
  have hAB : A * B = A⁻¹ := eq_inv_of_mul_eq_one_left hprod
  calc
    B = A⁻¹ * (A * B) := by simp
    _ = A⁻¹ * A⁻¹ := by rw [hAB]
    _ = A ^ (-2 : ℤ) := by
      rw [show (-2 : ℤ) = (-1 : ℤ) + (-1 : ℤ) by omega, zpow_add]
      simp

private lemma reduced_product_three
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) (m n : ℤ) :
    reducedUnitMatrix P q ((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n) =
      reducedUnitMatrix P q ((alphaUnit P) ^ (m - 2 * n)) := by
  rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_zpow,
    reducedUnitMatrix_map_zpow, reducedUnitMatrix_map_zpow,
    reduced_alphaSubOne_eq_alpha_neg_two P q h₁ h₂]
  rw [← zpow_mul, ← zpow_add]
  congr 2
  ring

private lemma reduced_alpha_eq_alphaSubOne_neg_two
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (alphaUnit P) =
      (reducedUnitMatrix P q (alphaSubOneUnit P)) ^ (-2 : ℤ) := by
  let A := reducedUnitMatrix P q (alphaUnit P)
  let B := reducedUnitMatrix P q (alphaSubOneUnit P)
  let C := reducedUnitMatrix P q (alphaSubTwoUnit P)
  have hBC : B = C := reduced_alphaSubOne_eq_alphaSubTwo_of_one_one P q h₁ h₂
  have hprod : A * B * C = 1 := by
    have h := congrArg (fun u => reducedUnitMatrix P q u)
      (alpha_units_product P)
    rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_mul,
      reducedUnitMatrix_map_one] at h
    exact h
  rw [← hBC] at hprod
  have hAB : A * B = B⁻¹ := eq_inv_of_mul_eq_one_left hprod
  calc
    A = (A * B) * B⁻¹ := by simp
    _ = B⁻¹ * B⁻¹ := by rw [hAB]
    _ = B ^ (-2 : ℤ) := by
      rw [show (-2 : ℤ) = (-1 : ℤ) + (-1 : ℤ) by omega, zpow_add]
      simp

private lemma reduced_product_five
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) (m n : ℤ) :
    reducedUnitMatrix P q ((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n) =
      reducedUnitMatrix P q ((alphaSubOneUnit P) ^ (n - 2 * m)) := by
  rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_zpow,
    reducedUnitMatrix_map_zpow, reducedUnitMatrix_map_zpow,
    reduced_alpha_eq_alphaSubOne_neg_two P q h₁ h₂]
  rw [← zpow_mul, ← zpow_add]
  congr 1
  ring

/-- First local line of the `3 × 2` matrix congruence: at `2`, the
congruence `b₁ ≡ b₂` changes `b₁^m b₂^n` into `b₁^(m+n)`. -/
theorem canonical_product_mem_two_iff
    (P : Parameters) (c : ℕ) (hc : 1 ≤ c)
    (h₁ : P.a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c])
    (h₂ : P.a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c]) (m n : ℤ) :
    ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P (2 ^ c)) ↔
      (7 * 2 ^ (c - 1) : ℤ) ∣ m + n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 0 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₂
  have heq := congrArg Units.val
    (reduced_product_two P (2 ^ c) h₁' h₂' m n)
  rw [heq, ← unit_mem_scalarSuborder_iff]
  exact alpha_int_power_law_two P c hc h₁ h₂ (m + n)

/-- Second local line of the `3 × 2` matrix congruence.  This is the
paper's use of `b₃=b₁⁻¹b₂⁻¹` together with `b₁ ≡ b₃` at `3`. -/
theorem canonical_product_mem_three_iff
    (P : Parameters) (d : ℕ) (hd : 1 ≤ d)
    (h₁ : P.a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d])
    (h₂ : P.a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d]) (m n : ℤ) :
    ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P (3 ^ d)) ↔
      (8 * 3 ^ (d - 1) : ℤ) ∣ m - 2 * n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 0 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₂
  have heq := congrArg Units.val
    (reduced_product_three P (3 ^ d) h₁' h₂' m n)
  rw [heq, ← unit_mem_scalarSuborder_iff]
  exact alpha_int_power_law_three P d hd h₁ h₂ (m - 2 * n)

/-- Third local line of the `3 × 2` matrix congruence.  This is the
paper's use of `b₃=b₁⁻¹b₂⁻¹` together with `b₂ ≡ b₃` at `5`. -/
theorem canonical_product_mem_five_iff
    (P : Parameters) (r : ℕ) (hr : 1 ≤ r)
    (h₁ : P.a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r])
    (h₂ : P.a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]) (m n : ℤ) :
    ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P (5 ^ r)) ↔
      (24 * 5 ^ (r - 1) : ℤ) ∣ n - 2 * m := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₂
  have heq := congrArg Units.val
    (reduced_product_five P (5 ^ r) h₁' h₂' m n)
  rw [heq, ← unit_mem_scalarSuborder_iff]
  exact alphaSubOne_int_power_law_five P r hr h₁ h₂ (n - 2 * m)

/-- Lemma 4.1 for the concrete conductors `2^c,3^d,5^r`. -/
theorem mem_scalarSuborder_product_iff (P : Parameters)
    (c d r : ℕ) (x : orderCarrier P) :
    x ∈ scalarSuborder P (2 ^ c * 3 ^ d * 5 ^ r) ↔
      x ∈ scalarSuborder P (2 ^ c) ∧
      x ∈ scalarSuborder P (3 ^ d) ∧
      x ∈ scalarSuborder P (5 ^ r) := by
  simp only [mem_scalarSuborder_iff_repr_dvd]
  change SuborderUnits.InScalarSuborder
      (((2 ^ c * 3 ^ d * 5 ^ r : ℕ) : ℤ)) ((orderBasis P).repr x) ↔
    SuborderUnits.InScalarSuborder (((2 ^ c : ℕ) : ℤ)) ((orderBasis P).repr x) ∧
    SuborderUnits.InScalarSuborder (((3 ^ d : ℕ) : ℤ)) ((orderBasis P).repr x) ∧
    SuborderUnits.InScalarSuborder (((5 ^ r : ℕ) : ℤ)) ((orderBasis P).repr x)
  have h₂₃ : IsCoprime (((2 ^ c : ℕ) : ℤ)) (((3 ^ d : ℕ) : ℤ)) :=
    ((by decide : Nat.Coprime 2 3).pow c d).isCoprime
  have h₂₅ : IsCoprime (((2 ^ c : ℕ) : ℤ)) (((5 ^ r : ℕ) : ℤ)) :=
    ((by decide : Nat.Coprime 2 5).pow c r).isCoprime
  have h₃₅ : IsCoprime (((3 ^ d : ℕ) : ℤ)) (((5 ^ r : ℕ) : ℤ)) :=
    ((by decide : Nat.Coprime 3 5).pow d r).isCoprime
  simpa only [Nat.cast_mul] using
    (SuborderUnits.inScalarSuborder_mul_three_iff h₂₃ h₂₅ h₃₅
      ((orderBasis P).repr x))

/-- Proposition 4.4 specialized to `(p₁,p₂,p₃)=(2,3,5)` and to the
canonical ABC units.  It identifies membership in the product-conductor
suborder with exactly the three exponent congruences in the paper. -/
theorem canonical_product_mem_iff_exponentConditions
    (P : Parameters) (c d r : ℕ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (hlocal : SatisfiesLocalConditions c d r P.a₁ P.a₂)
    (m n : ℤ) :
    ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (2 ^ c * 3 ^ d * 5 ^ r)) ↔
      (m, n) ∈ SuborderUnits.ExponentConditions c d r := by
  rcases hlocal with ⟨h₂₁, h₂₂, h₃₁, h₃₂, h₅₁, h₅₂⟩
  rw [mem_scalarSuborder_product_iff,
    canonical_product_mem_two_iff P c hc h₂₁ h₂₂,
    canonical_product_mem_three_iff P d hd h₃₁ h₃₂,
    canonical_product_mem_five_iff P r hr h₅₁ h₅₂]
  simp only [SuborderUnits.ExponentConditions, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h₂, h₃, h₅⟩
    exact ⟨h₂, h₃, by simpa [neg_sub] using h₅.neg_right⟩
  · rintro ⟨h₂, h₃, h₅⟩
    exact ⟨h₂, h₃, by simpa [neg_sub] using h₅.neg_right⟩

/-! ### From a fundamental family to all order units -/

private def abcUnitMap (P : Parameters) :
    (orderCarrier P)ˣ →* (NumberField.RingOfIntegers (ABCField P))ˣ :=
  Units.map (orderCarrier P).val.toRingHom.toMonoidHom

private lemma cubicOrder_unitMap_eq_abcUnitMap (P : Parameters) :
    (cubicOrder P).unitMap = abcUnitMap P := rfl

private lemma abcUnitMap_injective (P : Parameters) :
    Function.Injective (abcUnitMap P) :=
  Units.map_injective Subtype.val_injective

@[simp] private lemma abcUnitMap_neg_one (P : Parameters) :
    abcUnitMap P (-1) = -1 := by
  apply Units.val_injective
  rfl

@[simp] private lemma coe_abcUnitMap (P : Parameters)
    (u : (orderCarrier P)ˣ) :
    ((abcUnitMap P u :
      (NumberField.RingOfIntegers (ABCField P))ˣ) :
        NumberField.RingOfIntegers (ABCField P)) =
      (u : orderCarrier P) := rfl

@[simp] private lemma coe_abcUnitMap_zpow (P : Parameters)
    (u : (orderCarrier P)ˣ) (z : ℤ) :
    (((abcUnitMap P u) ^ z :
      (NumberField.RingOfIntegers (ABCField P))ˣ) :
        NumberField.RingOfIntegers (ABCField P)) =
      ((u ^ z : (orderCarrier P)ˣ) : orderCarrier P) := by
  exact (congrArg Units.val (map_zpow (abcUnitMap P) u z).symm).trans
    (coe_abcUnitMap P (u ^ z))

private def canonicalImageSubgroup (P : Parameters) :
    Subgroup (NumberField.RingOfIntegers (ABCField P))ˣ where
  carrier := {x | ∃ m n : ℤ,
    x = (abcUnitMap P (alphaUnit P)) ^ m *
      (abcUnitMap P (alphaSubOneUnit P)) ^ n}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    refine ⟨m + m', n + n', ?_⟩
    simp only [zpow_add]
    ac_rfl
  inv_mem' := by
    rintro x ⟨m, n, rfl⟩
    refine ⟨-m, -n, ?_⟩
    simp [mul_inv_rev, zpow_neg, mul_comm]

private lemma closure_candidate_le_canonicalImageSubgroup (P : Parameters) :
    Subgroup.closure
        (Set.range ((cubicOrder P).mapUnitFamily (candidateUnitFamily P))) ≤
      canonicalImageSubgroup P := by
  apply (Subgroup.closure_le (canonicalImageSubgroup P)).2
  rintro x ⟨i, rfl⟩
  rw [Cusick.CubicOrder.mapUnitFamily, cubicOrder_unitMap_eq_abcUnitMap]
  let e := finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))
  have hj : e i = 0 ∨ e i = 1 := by omega
  rcases hj with hj | hj
  · have hi : i = e.symm 0 := by
      apply e.injective
      simpa using hj
    rw [hi]
    refine ⟨1, 0, ?_⟩
    rw [candidateUnitFamily_zero]
    simp
    rfl
  · have hi : i = e.symm 1 := by
      apply e.injective
      simpa using hj
    rw [hi]
    refine ⟨0, 1, ?_⟩
    rw [candidateUnitFamily_one]
    simp
    rfl

/-- Proposition 3.4 supplies the hypothesis of this lemma.  It says exactly
that every ambient ABC-order unit is a sign times an integral power product
of the two canonical units, the representation invoked at the start of the
proof of Proposition 4.4. -/
theorem exists_sign_mul_canonical_of_fundamental
    (P : Parameters)
    (hfund : (cubicOrder P).IsFundamentalFamily (candidateUnitFamily P))
    (x : (orderCarrier P)ˣ) :
    ∃ ε : (orderCarrier P)ˣ, (ε = 1 ∨ ε = -1) ∧
      ∃ m n : ℤ,
        x = ε * (alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n := by
  have hxsub : (cubicOrder P).unitMap x ∈ (cubicOrder P).unitSubgroup :=
    ⟨x, rfl⟩
  have hxsup : (cubicOrder P).unitMap x ∈
      Subgroup.closure (Set.range
        ((cubicOrder P).mapUnitFamily (candidateUnitFamily P))) ⊔
        NumberField.Units.torsion (ABCField P) := by
    rw [hfund]
    exact hxsub
  rcases Subgroup.mem_sup.mp hxsup with ⟨y, hy, z, hz, hyz⟩
  have hy' := closure_candidate_le_canonicalImageSubgroup P hy
  rcases hy' with ⟨m, n, rfl⟩
  have hz' := NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
    (Cusick.CubicOrder.degree_odd (K := ABCField P)) ⟨z, hz⟩
  have hzval : z = 1 ∨ z = -1 := by simpa using hz'
  rw [cubicOrder_unitMap_eq_abcUnitMap] at hyz
  rcases hzval with hzval | hzval
  · refine ⟨1, Or.inl rfl, m, n, ?_⟩
    apply Units.ext
    apply Subtype.ext
    have hv := congrArg Units.val hyz.symm
    change (((x : orderCarrier P) :
      NumberField.RingOfIntegers (ABCField P))) = _ at hv
    simpa [hzval, mul_assoc] using hv
  · refine ⟨-1, Or.inr rfl, m, n, ?_⟩
    apply Units.ext
    apply Subtype.ext
    have hv := congrArg Units.val hyz.symm
    change (((x : orderCarrier P) :
      NumberField.RingOfIntegers (ABCField P))) = _ at hv
    simpa [hzval, mul_comm, mul_left_comm, mul_assoc] using hv

/-- Full unit classification in Proposition 4.4.  Under Proposition 3.4's
fundamentality hypothesis, the units whose values lie in the scalar suborder
are exactly the signed canonical power products with exponent pair in the
three-congruence lattice. -/
theorem unit_mem_scalarSuborder_iff_exists_sign_exponents
    (P : Parameters) (c d r : ℕ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (hfund : (cubicOrder P).IsFundamentalFamily (candidateUnitFamily P))
    (hlocal : SatisfiesLocalConditions c d r P.a₁ P.a₂)
    (x : (orderCarrier P)ˣ) :
    ((x : orderCarrier P) ∈
        scalarSuborder P (2 ^ c * 3 ^ d * 5 ^ r)) ↔
      ∃ ε : (orderCarrier P)ˣ, (ε = 1 ∨ ε = -1) ∧
        ∃ m n : ℤ, (m, n) ∈ SuborderUnits.ExponentConditions c d r ∧
          x = ε * (alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n := by
  let q := 2 ^ c * 3 ^ d * 5 ^ r
  constructor
  · intro hx
    obtain ⟨ε, hε, m, n, hxrep⟩ :=
      exists_sign_mul_canonical_of_fundamental P hfund x
    have hεmem : (ε : orderCarrier P) ∈ scalarSuborder P q := by
      rcases hε with hε | hε <;> rw [hε] <;> simp
    have hproduct :
        ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
          (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) := by
      apply (scalarSuborder.unit_mul_mem_iff_right P q ε
        ((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n) hεmem).mp
      rw [hxrep] at hx
      simpa [q, mul_assoc] using hx
    have hexponents : (m, n) ∈ SuborderUnits.ExponentConditions c d r :=
      (canonical_product_mem_iff_exponentConditions P c d r hc hd hr
        hlocal m n).mp hproduct
    exact ⟨ε, hε, m, n, hexponents, hxrep⟩
  · rintro ⟨ε, hε, m, n, hexponents, rfl⟩
    have hεmem : (ε : orderCarrier P) ∈ scalarSuborder P q := by
      rcases hε with hε | hε <;> rw [hε] <;> simp
    have hproduct :
        ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
          (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) :=
      (canonical_product_mem_iff_exponentConditions P c d r hc hd hr
        hlocal m n).mpr hexponents
    simpa [q, mul_assoc] using (scalarSuborder P q).mul_mem hεmem hproduct


end ABCLocalUnits
end CubicPeriodicTori
