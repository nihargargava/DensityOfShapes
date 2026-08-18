import main
import OrderPeriods
import ABCFundamentalUnits
import ArithmeticConstruction
import ABCLocalUnitsBridge
import ABCUnitLogs
import ABCMovingFrames

/-!
# The arithmetic realization bridge (scratch)

This file spells out the final application of Lemma 2.6 in the proof of
Dang--Gargava--Li.  The order is `ℤ + q O`, its units are classified by
Propositions 3.4 and 4.4, and Lemma 5.1 supplies the displayed basis of the
exponent lattice.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCRealizesScratch

open ABCOrders ArithmeticConstruction ABCBoundedFrames ABCMovingFrames
open Proposition52

def conductor (C D R : ℕ) : ℕ :=
  2 ^ (C + 4) * 3 ^ (D + 2) * 5 ^ (R + 1)

def ambientUnitMap (P : Parameters) (q : ℕ) :
    (scalarSuborder P q)ˣ →* (orderCarrier P)ˣ :=
  Units.map (scalarSuborder P q).val.toRingHom.toMonoidHom

@[simp] lemma coe_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    ((ambientUnitMap P q x : (orderCarrier P)ˣ) : orderCarrier P) =
      (x : scalarSuborder P q) := rfl

/-- An ambient unit whose value lies in `ℤ + qO` restricts to a unit of that
suborder.  The inverse lies there by the elementary inverse-membership lemma
used in Proposition 4.4. -/
def restrictUnit (P : Parameters) (q : ℕ) (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    (scalarSuborder P q)ˣ where
  val := ⟨x, hx⟩
  inv := ⟨(x⁻¹ : (orderCarrier P)ˣ),
    (ABCLocalUnits.unit_inv_mem_scalarSuborder_iff P q x).2 hx⟩
  val_inv := by
    apply Subtype.ext
    exact x.val_inv
  inv_val := by
    apply Subtype.ext
    exact x.inv_val

@[simp] lemma coe_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    ((restrictUnit P q x hx : (scalarSuborder P q)ˣ) :
      scalarSuborder P q) = ⟨x, hx⟩ := rfl

lemma unitLog_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    OrderPeriods.unitLog (scalarSuborderEmbedding P q) x =
      OrderPeriods.unitLog (orderEmbedding P) (ambientUnitMap P q x) := by
  rfl

lemma unitLog_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    OrderPeriods.unitLog (scalarSuborderEmbedding P q)
        (restrictUnit P q x hx) =
      OrderPeriods.unitLog (orderEmbedding P) x := by
  rfl

lemma unitLog_sign (P : Parameters) (ε : (orderCarrier P)ˣ)
    (hε : ε = 1 ∨ ε = -1) :
    OrderPeriods.unitLog (orderEmbedding P) ε = 0 := by
  rcases hε with rfl | rfl
  · funext i
    fin_cases i <;> simp [OrderPeriods.unitLog]
  · funext i
    fin_cases i <;> simp [OrderPeriods.unitLog]

/-- The real matrix in Lemma 5.1 is the scalar extension of its integral
exponent-basis matrix. -/
lemma exponentBasis_cast_eq (C D R : ℕ) :
    (exponentBasis C D R).map (Int.castRingHom ℝ) =
      exponentChangeReal * lambdaBasis C D R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentBasis_apply, exponentChangeReal, lambdaBasis,
      Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring

lemma cast_exponentBasis_mulVec (C D R : ℕ) (z : Fin 2 → ℤ) :
    (fun i ↦ (((exponentBasis C D R).mulVec z i : ℤ) : ℝ)) =
      (exponentChangeReal * lambdaBasis C D R).mulVec
        (fun i ↦ (z i : ℝ)) := by
  rw [← exponentBasis_cast_eq]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def periodMatrix (N C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  unitLogBasis N * exponentChangeReal * lambdaBasis C D R

lemma periodMatrix_det_pos (N C D R : ℕ) :
    0 < (periodMatrix N C D R).det := by
  simp only [periodMatrix, Matrix.det_mul]
  exact mul_pos (mul_pos (unitLogBasis_det_pos N)
    exponentChangeReal_det_pos) (lambdaBasis_det_pos C D R)

lemma periodMatrix_mulVec (N C D R : ℕ) (z : Fin 2 → ℤ) :
    (periodMatrix N C D R).mulVec (fun i ↦ (z i : ℝ)) =
      (unitLogBasis N).mulVec
        (fun i ↦ (((exponentBasis C D R).mulVec z i : ℤ) : ℝ)) := by
  rw [periodMatrix, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← cast_exponentBasis_mulVec]

lemma scalarSuborderBasis_zero (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    scalarSuborderBasis P q hq 0 = 1 := by
  rw [scalarSuborderBasis_apply]
  rfl

lemma scalarSuborderEmbedding_zero_injective (P : Parameters) (q : ℕ) :
    Function.Injective (scalarSuborderEmbedding P q 0) := by
  intro x y hxy
  apply Subtype.ext
  apply (orderEmbedding_zero_injective P)
  exact hxy

lemma ambientUnitMap_mem (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    ((ambientUnitMap P q x : (orderCarrier P)ˣ) : orderCarrier P) ∈
      scalarSuborder P q := by
  exact (x : scalarSuborder P q).property

lemma ambientUnitMap_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    ambientUnitMap P q (restrictUnit P q x hx) = x := by
  apply Units.ext
  rfl

/-- Propositions 3.4 and 4.4, followed by Lemma 5.1, identify the complete
logarithmic unit lattice of the scalar order with the columns of
`periodMatrix`. -/
lemma unitLogs_iff_periodMatrix (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) (u : Fin 2 → ℝ) :
    (∃ x : (scalarSuborder (parameters N) (conductor C D R))ˣ,
        u = OrderPeriods.unitLog
          (scalarSuborderEmbedding (parameters N) (conductor C D R)) x) ↔
      ∃ z : Fin 2 → ℤ,
        u = (periodMatrix N C D R).mulVec (fun i ↦ (z i : ℝ)) := by
  let P := parameters N
  let q := conductor C D R
  constructor
  · rintro ⟨x, rfl⟩
    have hxmem :
        (((ambientUnitMap P q x : (orderCarrier P)ˣ) : orderCarrier P) ∈
          scalarSuborder P q) := ambientUnitMap_mem P q x
    have hclass :=
      (ABCLocalUnits.unit_mem_scalarSuborder_iff_exists_sign_exponentLattice
        P C D R hfund hlocal (ambientUnitMap P q x)).mp hxmem
    obtain ⟨ε, hε, m, n, hmn, hx⟩ := hclass
    rw [exponentLattice_eq_range_exponentBasis] at hmn
    obtain ⟨z, hz⟩ := hmn
    refine ⟨z, ?_⟩
    have hm : m = (exponentBasis C D R).mulVec z 0 :=
      (congrArg Prod.fst hz).symm
    have hn : n = (exponentBasis C D R).mulVec z 1 :=
      (congrArg Prod.snd hz).symm
    dsimp only [P, q] at *
    rw [unitLog_ambientUnitMap, hx, ABCUnitLogs.unitLog_mul,
      ABCUnitLogs.unitLog_mul,
      unitLog_sign (parameters N) ε hε, zero_add]
    rw [← ABCUnitLogs.unitLog_mul,
      ABCUnitLogs.unitLog_canonical_product_eq_mulVec,
      periodMatrix_mulVec]
    congr 1
    funext i
    fin_cases i
    · simpa [hm]
    · simpa [hn]
  · rintro ⟨z, rfl⟩
    let m : ℤ := (exponentBasis C D R).mulVec z 0
    let n : ℤ := (exponentBasis C D R).mulVec z 1
    have hmn : (m, n) ∈ exponentLattice C D R := by
      rw [exponentLattice_eq_range_exponentBasis]
      exact ⟨z, rfl⟩
    have hmem :
        ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
            (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) :=
      (ABCLocalUnits.canonical_product_mem_iff_exponentLattice
        P C D R hlocal m n).mpr hmn
    let x : (scalarSuborder P q)ˣ := restrictUnit P q
      ((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n) hmem
    refine ⟨x, ?_⟩
    rw [unitLog_restrictUnit,
      ABCUnitLogs.unitLog_canonical_product_eq_mulVec,
      periodMatrix_mulVec]
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Lemma 2.6 applied to the scalar ABC order. -/
theorem normalized_periodMatrix_mem (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    (normalizeBasis (periodMatrix N C D R)
      (periodMatrix_det_pos N C D R) : ShapeSpace) ∈
        periodicTorusShapes := by
  let q := conductor C D R
  have hq : q ≠ 0 := by
    simp [q, conductor]
  apply OrderPeriods.normalized_unit_log_shape_mem_periodicTorusShapes
    (scalarSuborderBasis (parameters N) q hq)
    (scalarSuborderEmbedding (parameters N) q)
    (scalarSuborderBasis_zero (parameters N) q hq)
    (scalarSuborderEmbedding_zero_injective (parameters N) q)
    (scalarSuborderEmbeddingMatrix_det_ne_zero (parameters N) q hq)
    (periodMatrix N C D R) (periodMatrix_det_pos N C D R)
  exact unitLogs_iff_periodMatrix N C D R hfund hlocal

lemma normalized_periodMatrix_eq_movingFrame_smul
    (N C D R : ℕ) :
    (normalizeBasis (periodMatrix N C D R)
        (periodMatrix_det_pos N C D R) : ShapeSpace) =
      movingFrame N • lambdaShape C D R := by
  have hUE : 0 < (unitLogBasis N * exponentChangeReal).det := by
    simpa only [Matrix.det_mul] using
      mul_pos (unitLogBasis_det_pos N) exponentChangeReal_det_pos
  change
    (normalizeBasis
      ((unitLogBasis N * exponentChangeReal) * lambdaBasis C D R)
      _ : ShapeSpace) = movingFrame N • lambdaShape C D R
  rw [normalizeBasis_mul (unitLogBasis N * exponentChangeReal)
    (lambdaBasis C D R) hUE (lambdaBasis_det_pos C D R)]
  rw [normalize_unitLog_mul_change]
  rfl

/-- The paper's realization statement, assuming the output of Proposition
3.4 and the local congruences entering Proposition 4.4. -/
theorem realizes_of_fundamental (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    movingFrame N • lambdaShape C D R ∈ periodicTorusShapes := by
  rw [← normalized_periodMatrix_eq_movingFrame_smul]
  exact normalized_periodMatrix_mem N C D R hfund hlocal

/-- For the CRT family, Proposition 3.4 follows from Cusick's regulator
inequality once `N ≥ 1`; hence the realization requires only the local
conditions. -/
theorem realizes (N C D R : ℕ) (hN : 1 ≤ N)
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    movingFrame N • lambdaShape C D R ∈ periodicTorusShapes := by
  have hlogs := parameters_logs_gt_ten N hN
  have hfund :=
    ABCOrders.FundamentalUnits.candidateUnitFamily_isFundamental_of_large
      (P := parameters N) hlogs.1 hlogs.2
  exact realizes_of_fundamental N C D R hfund hlocal

end ABCRealizesScratch
end CubicPeriodicTori
