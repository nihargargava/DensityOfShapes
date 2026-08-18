import ABCOrders
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-!
# Fundamental units in the ABC family

This file formalizes Proposition 3.4 of the paper.  Its proof follows the
paper's regulator-index argument: compute the regulator of the two canonical
units, compare it with Cusick's discriminant lower bound, and use integrality
of the lattice index.
-/

noncomputable section

namespace ABCOrders

open scoped NumberField
open NumberField NumberField.Units

namespace FundamentalUnits

variable (P : Parameters)

/-! ## Exact formulas -/

/-- The positive Vandermonde product of the three ordered roots. -/
def rootDiscriminant : ℝ :=
  (root1 P - root0 P) * (root2 P - root0 P) * (root2 P - root1 P)

lemma rootDiscriminant_pos : 0 < rootDiscriminant P := by
  unfold rootDiscriminant
  exact mul_pos
    (mul_pos (sub_pos.mpr (roots_strict_order P).1)
      (sub_pos.mpr (lt_trans (roots_strict_order P).1
        (roots_strict_order P).2)))
    (sub_pos.mpr (roots_strict_order P).2)

lemma rootDiscriminant_eq_embeddingMatrix_det :
    rootDiscriminant P = (orderEmbeddingMatrix P).det := by
  rw [orderEmbeddingMatrix_det]
  rfl

lemma rootPlace_embedding_alpha (i : Fin 3) :
    (rootPlace P i).embedding (alpha P) = (realRoot P i : ℂ) := by
  have h := NumberField.InfinitePlace.embedding_mk_eq_of_isReal
    (complexOfRealEmbedding (rootEmbedding P i)).property
  have hx := DFunLike.congr_fun h (alpha P)
  simpa [rootPlace, complexOfRealEmbedding, rootEmbedding] using hx

@[simp] lemma coe_alphaInteger_ABCField :
    algebraMap (NumberField.RingOfIntegers (ABCField P)) (ABCField P)
      (alphaInteger P) = alpha P := by
  unfold alphaInteger
  exact NumberField.RingOfIntegers.map_mk _ _

open scoped Classical in
/-- Exact discriminant formula for the power basis `1, α, α²`. -/
lemma powerBasis_discriminant_cast :
    ((Algebra.discr ℤ (fun i : Fin 3 ↦
        (alphaInteger P : NumberField.RingOfIntegers (ABCField P)) ^
          (i : ℕ))).natAbs : ℝ) =
      rootDiscriminant P ^ 2 := by
  let K := ABCField P
  let x : K := alpha P
  let e : Fin 3 ≃ (K →ₐ[ℚ] ℂ) :=
    (rootPlaceEquiv P).trans
      (Cusick.CubicOrder.placeAlgHomEquiv (K := K))
  have hdiscC := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two
    ℚ ℂ (fun i : Fin 3 ↦ x ^ (i : ℕ)) e
  have hentry (i j : Fin 3) :
      Algebra.embeddingsMatrixReindex ℚ ℂ
        (fun i : Fin 3 ↦ x ^ (i : ℕ)) e i j =
      ((realRoot P j : ℝ) : ℂ) ^ (i : ℕ) := by
    simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply,
      Matrix.submatrix_apply, Algebra.embeddingsMatrix_apply, map_pow]
    congr 1
    change (rootPlace P j).embedding x = _
    simpa [x] using rootPlace_embedding_alpha P j
  have hdet :
      (Algebra.embeddingsMatrixReindex ℚ ℂ
        (fun i : Fin 3 ↦ x ^ (i : ℕ)) e).det =
      ((rootDiscriminant P : ℝ) : ℂ) := by
    rw [Matrix.det_fin_three]
    simp_rw [hentry]
    norm_num
    unfold rootDiscriminant
    simp only [root0, root1, root2]
    push_cast
    ring
  have hdiscQ := Cusick.CubicOrder.map_discr_to_rat
    (K := ABCField P)
    (fun i : Fin 3 ↦
      (alphaInteger P : NumberField.RingOfIntegers (ABCField P)) ^ (i : ℕ))
  have hdiscR :
      ((Algebra.discr ℤ (fun i : Fin 3 ↦
        (alphaInteger P : NumberField.RingOfIntegers (ABCField P)) ^
          (i : ℕ)) : ℤ) : ℝ) =
      rootDiscriminant P ^ 2 := by
    apply Complex.ofReal_injective
    have hright :
        (((rootDiscriminant P ^ 2 : ℝ) : ℂ)) =
          (Algebra.embeddingsMatrixReindex ℚ ℂ
            (fun i : Fin 3 ↦ x ^ (i : ℕ)) e).det ^ 2 := by
      rw [hdet]
      push_cast
      rfl
    rw [hright, ← hdiscC]
    push_cast
    have hdiscQC := congrArg (algebraMap ℚ ℂ) hdiscQ
    simpa [K, x, map_pow] using hdiscQC
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs,
    abs_of_nonneg]
  · exact hdiscR
  · rw [hdiscR]
    positivity

open scoped Classical in
/-- The order discriminant is the square of the root Vandermonde product. -/
theorem cubicOrder_discriminant_cast :
    (((cubicOrder P).discriminant : ℕ) : ℝ) =
      rootDiscriminant P ^ 2 := by
  rw [Cusick.CubicOrder.discriminant_eq_natAbs_discr]
  have hb (i : Fin 3) :
      (((cubicOrder P).basis i : (cubicOrder P).carrier) :
          NumberField.RingOfIntegers (ABCField P)) =
        alphaInteger P ^ (i : ℕ) := by
    change ((orderBasis P i : orderCarrier P) :
      NumberField.RingOfIntegers (ABCField P)) = _
    rw [orderBasis_apply]
    rfl
  simp_rw [hb]
  exact powerBasis_discriminant_cast P

/-- The candidate units after inclusion in the maximal order. -/
def mappedCandidate :
    Fin (NumberField.Units.rank (ABCField P)) →
      (NumberField.RingOfIntegers (ABCField P))ˣ :=
  (cubicOrder P).mapUnitFamily (candidateUnitFamily P)

@[simp] lemma rootPlace_unitMap_alpha (i : Fin 3) :
    rootPlace P i
      (((cubicOrder P).unitMap (alphaUnit P) :
        NumberField.RingOfIntegers (ABCField P)) : ABCField P) =
      realRoot P i := by
  have hv :
      ((cubicOrder P).unitMap (alphaUnit P) :
        NumberField.RingOfIntegers (ABCField P)) = alphaInteger P := by
    rfl
  rw [hv]
  exact rootPlace_alpha P i

@[simp] lemma rootPlace_unitMap_alphaSubOne (i : Fin 3) :
    rootPlace P i
      (((cubicOrder P).unitMap (alphaSubOneUnit P) :
        NumberField.RingOfIntegers (ABCField P)) : ABCField P) =
      |realRoot P i - (P.a₁ : ℝ)| := by
  have hv :
      ((cubicOrder P).unitMap (alphaSubOneUnit P) :
        NumberField.RingOfIntegers (ABCField P)) =
      alphaInteger P - algebraMap ℤ
        (NumberField.RingOfIntegers (ABCField P)) P.a₁ := by
    rfl
  rw [hv]
  rw [rootPlace, NumberField.InfinitePlace.apply]
  rw [show ((alphaInteger P -
      algebraMap ℤ (NumberField.RingOfIntegers (ABCField P)) P.a₁ :
        NumberField.RingOfIntegers (ABCField P)) : ABCField P) =
      alpha P - algebraMap ℤ (ABCField P) P.a₁ by simp]
  simp only [complexOfRealEmbedding_apply]
  rw [map_sub]
  simp [rootEmbedding]
  convert Complex.norm_real (realRoot P i - (P.a₁ : ℝ)) using 1 <;> simp

/-- The four positive logarithms occurring in the paper's determinant. -/
def xLog : ℝ := Real.log ((P.a₁ : ℝ) - root0 P)
def yLog : ℝ := Real.log ((P.a₂ : ℝ) - root0 P)
def uLog : ℝ := Real.log (root1 P)
def vLog : ℝ := Real.log ((P.a₂ : ℝ) - root1 P)

/-- The exact regulator expression for `⟨α, α-a₁⟩`. -/
def candidateRegulatorExpression : ℝ :=
  xLog P * vLog P + yLog P * uLog P + yLog P * vLog P

lemma root0_product_eq_one :
    root0 P * ((P.a₁ : ℝ) - root0 P) *
      ((P.a₂ : ℝ) - root0 P) = 1 := by
  have h := realRoot_root P 0
  rw [Polynomial.IsRoot, abcPolynomialR_eval] at h
  change root0 P * (root0 P - (P.a₁ : ℝ)) *
    (root0 P - (P.a₂ : ℝ)) - 1 = 0 at h
  nlinarith

lemma root1_product_eq_one :
    root1 P * ((P.a₁ : ℝ) - root1 P) *
      ((P.a₂ : ℝ) - root1 P) = 1 := by
  have h := realRoot_root P 1
  rw [Polynomial.IsRoot, abcPolynomialR_eval] at h
  change root1 P * (root1 P - (P.a₁ : ℝ)) *
    (root1 P - (P.a₂ : ℝ)) - 1 = 0 at h
  nlinarith

lemma log_root0_eq :
    Real.log (root0 P) = -xLog P - yLog P := by
  have h0 := (root0_strictBounds P).1
  have hx : 0 < (P.a₁ : ℝ) - root0 P := by
    have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root0_strictBounds P).2]
  have hy : 0 < (P.a₂ : ℝ) - root0 P := by
    have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith
  have hlog := congrArg Real.log (root0_product_eq_one P)
  rw [Real.log_mul (mul_pos h0 hx).ne' hy.ne', Real.log_mul h0.ne' hx.ne',
    Real.log_one] at hlog
  change Real.log (root0 P) =
    -Real.log ((P.a₁ : ℝ) - root0 P) -
      Real.log ((P.a₂ : ℝ) - root0 P)
  linarith

lemma log_root1_sub_a₁_eq :
    Real.log |root1 P - (P.a₁ : ℝ)| = -uLog P - vLog P := by
  have hu : 0 < root1 P := by
    have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root1_strictBounds P).1]
  have hx : 0 < (P.a₁ : ℝ) - root1 P :=
    sub_pos.mpr (root1_strictBounds P).2
  have hv : 0 < (P.a₂ : ℝ) - root1 P := by
    have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith [(root1_strictBounds P).2]
  have hlog := congrArg Real.log (root1_product_eq_one P)
  rw [Real.log_mul (mul_pos hu hx).ne' hv.ne', Real.log_mul hu.ne' hx.ne',
    Real.log_one] at hlog
  rw [abs_of_neg (sub_neg.mpr (root1_strictBounds P).2)]
  rw [neg_sub]
  change Real.log ((P.a₁ : ℝ) - root1 P) =
    -Real.log (root1 P) - Real.log ((P.a₂ : ℝ) - root1 P)
  linarith

open scoped Classical in
/-- Exact determinant formula for the regulator of the two candidate units.
This is the exact (pre-asymptotic) form of Lemma 3.2 in the paper. -/
theorem candidate_regulator_exact :
    NumberField.Units.regOfFamily (mappedCandidate P) =
      |candidateRegulatorExpression P| := by
  let eRank : Fin (NumberField.Units.rank (ABCField P)) ≃ Fin 2 :=
    finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))
  let ePlaces : {w : NumberField.InfinitePlace (ABCField P) //
      w ≠ rootPlace P 2} ≃ Fin (NumberField.Units.rank (ABCField P)) :=
    (firstTwoPlaces P).symm.trans eRank.symm
  rw [NumberField.Units.regOfFamily_eq_det (mappedCandidate P)
    (rootPlace P 2) ePlaces]
  congr 1
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j ↦
    (((firstTwoPlaces P) j).val.mult : ℝ) *
      Real.log (((firstTwoPlaces P) j).val
        ((mappedCandidate P (ePlaces ((firstTwoPlaces P) i)) :
          NumberField.RingOfIntegers (ABCField P)) : ABCField P))
  have hdet :
      (Matrix.of fun i w : {w : NumberField.InfinitePlace (ABCField P) //
        w ≠ rootPlace P 2} ↦ (w.val.mult : ℝ) *
          Real.log (w.val
            ((mappedCandidate P (ePlaces i) :
              NumberField.RingOfIntegers (ABCField P)) : ABCField P))).det =
      M.det := by
    rw [← Matrix.det_reindex_self (firstTwoPlaces P).symm]
    rfl
  rw [hdet, Matrix.det_fin_two]
  have he0 : ePlaces ((firstTwoPlaces P) 0) = eRank.symm 0 := by
    simp [ePlaces]
  have he1 : ePlaces ((firstTwoPlaces P) 1) = eRank.symm 1 := by
    simp [ePlaces]
  have her0 : eRank.symm 0 =
      (finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 0 := rfl
  have her1 : eRank.symm 1 =
      (finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 1 := rfl
  have hp0 : ((firstTwoPlaces P) 0).val = rootPlace P 0 := by rfl
  have hp1 : ((firstTwoPlaces P) 1).val = rootPlace P 1 := by rfl
  dsimp [M]
  rw [he0, he1, her0, her1, hp0, hp1]
  simp only [NumberField.IsTotallyReal.mult_eq]
  simp only [mappedCandidate, Cusick.CubicOrder.mapUnitFamily,
    candidateUnitFamily_zero, candidateUnitFamily_one,
    rootPlace_unitMap_alpha, rootPlace_unitMap_alphaSubOne]
  norm_num
  change Real.log (root0 P) *
      Real.log (root1 P - (P.a₁ : ℝ)) -
    Real.log (root1 P) *
      Real.log (root0 P - (P.a₁ : ℝ)) = _
  have hlog1 : Real.log (root1 P - (P.a₁ : ℝ)) =
      Real.log ((P.a₁ : ℝ) - root1 P) := by
    simpa only [neg_sub] using
      (Real.log_neg_eq_log (root1 P - (P.a₁ : ℝ))).symm
  have hlog0 : Real.log (root0 P - (P.a₁ : ℝ)) =
      Real.log ((P.a₁ : ℝ) - root0 P) := by
    simpa only [neg_sub] using
      (Real.log_neg_eq_log (root0 P - (P.a₁ : ℝ))).symm
  rw [hlog1, hlog0]
  rw [log_root0_eq P]
  have hsublog : Real.log ((P.a₁ : ℝ) - root1 P) =
      -uLog P - vLog P := by
    have h := log_root1_sub_a₁_eq P
    rw [abs_of_neg (sub_neg.mpr (root1_strictBounds P).2), neg_sub] at h
    exact h
  rw [hsublog]
  unfold candidateRegulatorExpression
  unfold xLog uLog
  ring

lemma candidateRegulatorExpression_pos :
    0 < candidateRegulatorExpression P := by
  have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hxArg : 1 < (P.a₁ : ℝ) - root0 P := by
    linarith [(root0_strictBounds P).2]
  have hyArg : 1 < (P.a₂ : ℝ) - root0 P := by
    linarith [(root0_strictBounds P).2]
  have huArg : 1 < root1 P := by
    linarith [(root1_strictBounds P).1]
  have hvArg : 1 < (P.a₂ : ℝ) - root1 P := by
    have hgapZ : P.a₁ + 1 ≤ P.a₂ := Int.add_one_le_iff.mpr P.lt
    have hgapR : (P.a₁ : ℝ) + 1 ≤ P.a₂ := by exact_mod_cast hgapZ
    have hgap : (1 : ℝ) ≤ (P.a₂ : ℝ) - P.a₁ := by linarith
    linarith [(root1_strictBounds P).2]
  have hx : 0 < xLog P := Real.log_pos hxArg
  have hy : 0 < yLog P := Real.log_pos hyArg
  have hu : 0 < uLog P := Real.log_pos huArg
  have hv : 0 < vLog P := Real.log_pos hvArg
  unfold candidateRegulatorExpression
  positivity

theorem mappedCandidate_isMaxRank :
    NumberField.Units.IsMaxRank (mappedCandidate P) := by
  rw [← NumberField.Units.regOfFamily_ne_zero_iff]
  rw [candidate_regulator_exact P,
    abs_of_pos (candidateRegulatorExpression_pos P)]
  exact (candidateRegulatorExpression_pos P).ne'

/-! ## The regulator-index argument -/

/-- The subgroup generated by the candidate units, together with torsion. -/
def candidateSubgroup : Subgroup
    (NumberField.RingOfIntegers (ABCField P))ˣ :=
  Subgroup.closure (Set.range (mappedCandidate P)) ⊔
    NumberField.Units.torsion (ABCField P)

lemma candidateSubgroup_le_orderUnits :
    candidateSubgroup P ≤ (cubicOrder P).unitSubgroup := by
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    rintro u ⟨i, rfl⟩
    exact ⟨candidateUnitFamily P i, rfl⟩
  · exact (cubicOrder P).torsion_le_unitSubgroup

/-- The integer which the paper denotes by `R(Θ)/R(ℴ)`. -/
def candidateIndex : ℕ :=
  (candidateSubgroup P).relIndex (cubicOrder P).unitSubgroup

theorem candidate_regulator_div_order_regulator :
    NumberField.Units.regOfFamily (mappedCandidate P) /
        (cubicOrder P).regulator = (candidateIndex P : ℝ) := by
  let U := candidateSubgroup P
  let V := (cubicOrder P).unitSubgroup
  have hV : V.FiniteIndex := inferInstance
  have hle : U ≤ V := candidateSubgroup_le_orderUnits P
  rw [Cusick.CubicOrder.regulator]
  have hreg0 : NumberField.Units.regulator (ABCField P) ≠ 0 :=
    (NumberField.Units.regulator_pos (ABCField P)).ne'
  calc
    NumberField.Units.regOfFamily (mappedCandidate P) /
        ((V.index : ℝ) * NumberField.Units.regulator (ABCField P)) =
        (NumberField.Units.regOfFamily (mappedCandidate P) /
          NumberField.Units.regulator (ABCField P)) / (V.index : ℝ) := by
            field_simp
    _ = (U.index : ℝ) / (V.index : ℝ) := by
      rw [NumberField.Units.regOfFamily_div_regulator]
      rfl
    _ = (candidateIndex P : ℝ) := by
      have hVind : (V.index : ℝ) ≠ 0 := by
        exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := V))
      rw [div_eq_iff hVind]
      exact_mod_cast (Subgroup.relIndex_mul_index hle).symm

/-- Cusick's inequality in the exact ABC discriminant variables. -/
theorem cusick_lower_bound_ABC :
    (1 / 16 : ℝ) *
        Real.log (rootDiscriminant P ^ 2 / 4) ^ 2 ≤
      (cubicOrder P).regulator := by
  have h := Cusick.CubicOrder.regulator_lower_bound (cubicOrder P)
  rw [cubicOrder_discriminant_cast P] at h
  exact h

/-! ## Quantitative comparison

The paper writes these estimates with `O(·)` notation.  We make the same
comparison explicit, using the harmless threshold `log a₁, log(a₂-a₁)>10`.
-/

def gap : ℝ := (P.a₂ : ℝ) - P.a₁
def aLog : ℝ := Real.log (P.a₁ : ℝ)
def bLog : ℝ := Real.log (P.a₂ : ℝ)
def gapLog : ℝ := Real.log (gap P)

lemma gap_one_le : 1 ≤ gap P := by
  have h : P.a₁ + 1 ≤ P.a₂ := Int.add_one_le_iff.mpr P.lt
  have hr : (P.a₁ : ℝ) + 1 ≤ P.a₂ := by exact_mod_cast h
  unfold gap
  linarith

lemma a_pos : 0 < (P.a₁ : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 3) P.three_le)

lemma b_pos : 0 < (P.a₂ : ℝ) := by
  exact lt_trans (a_pos P) (by exact_mod_cast P.lt)

lemma gap_pos : 0 < gap P := lt_of_lt_of_le zero_lt_one (gap_one_le P)

lemma xLog_le_aLog : xLog P ≤ aLog P := by
  unfold xLog aLog
  apply Real.log_le_log
  · have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root0_strictBounds P).2]
  · linarith [(root0_strictBounds P).1]

lemma yLog_le_bLog : yLog P ≤ bLog P := by
  unfold yLog bLog
  apply Real.log_le_log
  · have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith [(root0_strictBounds P).2]
  · linarith [(root0_strictBounds P).1]

lemma uLog_le_aLog : uLog P ≤ aLog P := by
  unfold uLog aLog
  exact Real.log_le_log (by
    have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root1_strictBounds P).1]) (root1_strictBounds P).2.le

lemma vLog_le_gapLog_add_log_two :
    vLog P ≤ gapLog P + Real.log 2 := by
  have hvpos : 0 < (P.a₂ : ℝ) - root1 P := by
    have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith [(root1_strictBounds P).2]
  have hvle : (P.a₂ : ℝ) - root1 P ≤ gap P + 1 := by
    unfold gap
    linarith [(root1_strictBounds P).1]
  have hg2 : gap P + 1 ≤ gap P * 2 := by
    linarith [gap_one_le P]
  calc
    vLog P = Real.log ((P.a₂ : ℝ) - root1 P) := rfl
    _ ≤ Real.log (gap P * 2) :=
      Real.log_le_log hvpos (hvle.trans hg2)
    _ = gapLog P + Real.log 2 := by
      rw [Real.log_mul (gap_pos P).ne' (by norm_num : (2 : ℝ) ≠ 0)]
      rfl

lemma aLog_lt_bLog : aLog P < bLog P := by
  unfold aLog bLog
  exact Real.log_lt_log (a_pos P) (by exact_mod_cast P.lt)

lemma candidateRegulatorExpression_le_logMajorant
    (ha : 10 < aLog P) (hg : 10 < gapLog P) :
    candidateRegulatorExpression P ≤
      aLog P * bLog P + aLog P * (gapLog P + Real.log 2) +
        bLog P * (gapLog P + Real.log 2) := by
  have hb : 10 < bLog P := ha.trans (aLog_lt_bLog P)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ xLog P := by
    have haR : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    change 0 ≤ Real.log ((P.a₁ : ℝ) - root0 P)
    exact (Real.log_pos (by
      linarith [(root0_strictBounds P).2])).le
  have hy0 : 0 ≤ yLog P := by
    have haR : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    change 0 ≤ Real.log ((P.a₂ : ℝ) - root0 P)
    exact (Real.log_pos (by
      linarith [(root0_strictBounds P).2])).le
  have hu0 : 0 ≤ uLog P := by
    have haR : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    change 0 ≤ Real.log (root1 P)
    exact (Real.log_pos (by
      linarith [(root1_strictBounds P).1])).le
  have hv0 : 0 ≤ vLog P := by
    have hgap := gap_one_le P
    unfold gap at hgap
    change 0 ≤ Real.log ((P.a₂ : ℝ) - root1 P)
    exact (Real.log_pos (by
      linarith [(root1_strictBounds P).2])).le
  have ha0 : 0 ≤ aLog P := le_trans (by norm_num) ha.le
  have hb0 : 0 ≤ bLog P := le_trans (by norm_num) hb.le
  have hq0 : 0 ≤ gapLog P + Real.log 2 := by linarith
  have hxv : xLog P * vLog P ≤
      aLog P * (gapLog P + Real.log 2) :=
    mul_le_mul (xLog_le_aLog P) (vLog_le_gapLog_add_log_two P)
      hv0 ha0
  have hyu : yLog P * uLog P ≤ bLog P * aLog P :=
    mul_le_mul (yLog_le_bLog P) (uLog_le_aLog P) hu0 hb0
  have hyv : yLog P * vLog P ≤
      bLog P * (gapLog P + Real.log 2) :=
    mul_le_mul (yLog_le_bLog P) (vLog_le_gapLog_add_log_two P)
      hv0 hb0
  unfold candidateRegulatorExpression
  nlinarith

lemma rootDiscriminant_gt_product_div_four
    (ha : 10 < aLog P) :
    (P.a₁ : ℝ) * P.a₂ * gap P / 4 < rootDiscriminant P := by
  have haPos := a_pos P
  have hbPos := b_pos P
  have hgPos := gap_pos P
  have hlogA : Real.log (P.a₁ : ℝ) ≤ (P.a₁ : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos haPos
  have haLarge : (4 : ℝ) ≤ P.a₁ := by
    unfold aLog at ha
    linarith
  have hbLarge : (2 : ℝ) ≤ P.a₂ := by
    have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith
  have hroot1 : (P.a₁ : ℝ) - 2 < root1 P - root0 P := by
    linarith [(root1_strictBounds P).1, (root0_strictBounds P).2]
  have hroot2 : (P.a₂ : ℝ) - 1 < root2 P - root0 P := by
    linarith [(root2_strictBounds P).1, (root0_strictBounds P).2]
  have hroot3 : gap P < root2 P - root1 P := by
    unfold gap
    linarith [(root2_strictBounds P).1, (root1_strictBounds P).2]
  have hAhalf : (P.a₁ : ℝ) / 2 ≤ P.a₁ - 2 := by linarith
  have hBhalf : (P.a₂ : ℝ) / 2 ≤ P.a₂ - 1 := by linarith
  have hleft1 : 0 < (P.a₁ : ℝ) - 2 := by linarith
  have hleft2 : 0 < (P.a₂ : ℝ) - 1 := by linarith
  have hpair :
      ((P.a₁ : ℝ) - 2) * ((P.a₂ : ℝ) - 1) <
        (root1 P - root0 P) * (root2 P - root0 P) := by
    exact mul_lt_mul hroot1 hroot2.le hleft2
      (by linarith [(root1_strictBounds P).1,
        (root0_strictBounds P).2])
  have hthree :
      ((P.a₁ : ℝ) - 2) * ((P.a₂ : ℝ) - 1) * gap P <
        rootDiscriminant P := by
    unfold rootDiscriminant
    exact mul_lt_mul hpair hroot3.le hgPos
      (mul_pos (sub_pos.mpr (roots_strict_order P).1)
        (sub_pos.mpr (lt_trans (roots_strict_order P).1
          (roots_strict_order P).2))).le
  have hminor :
      (P.a₁ : ℝ) / 2 * ((P.a₂ : ℝ) / 2) * gap P ≤
        ((P.a₁ : ℝ) - 2) * ((P.a₂ : ℝ) - 1) * gap P := by
    apply mul_le_mul_of_nonneg_right _ hgPos.le
    exact mul_le_mul hAhalf hBhalf
      (div_nonneg hbPos.le (by norm_num))
      (sub_nonneg.mpr (by linarith))
  calc
    (P.a₁ : ℝ) * P.a₂ * gap P / 4 =
        (P.a₁ : ℝ) / 2 * ((P.a₂ : ℝ) / 2) * gap P := by ring
    _ ≤ _ := hminor
    _ < _ := hthree

lemma log_discriminant_lower
    (ha : 10 < aLog P) :
    2 * (aLog P + bLog P + gapLog P - 3 * Real.log 2) <
      Real.log (rootDiscriminant P ^ 2 / 4) := by
  have hprod := rootDiscriminant_gt_product_div_four P ha
  have hqpos : 0 <
      (P.a₁ : ℝ) * P.a₂ * gap P / 8 := by
    exact div_pos (mul_pos (mul_pos (a_pos P) (b_pos P)) (gap_pos P))
      (by norm_num)
  have hhalf :
      (P.a₁ : ℝ) * P.a₂ * gap P / 8 <
        rootDiscriminant P / 2 := by
    nlinarith
  have hlog := Real.log_lt_log hqpos hhalf
  have hlogLeft :
      Real.log ((P.a₁ : ℝ) * P.a₂ * gap P / 8) =
        aLog P + bLog P + gapLog P - 3 * Real.log 2 := by
    rw [Real.log_div (mul_ne_zero
        (mul_ne_zero (a_pos P).ne' (b_pos P).ne') (gap_pos P).ne')
      (by norm_num : (8 : ℝ) ≠ 0)]
    rw [Real.log_mul (mul_ne_zero (a_pos P).ne' (b_pos P).ne')
      (gap_pos P).ne', Real.log_mul (a_pos P).ne' (b_pos P).ne']
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h8]
    rfl
  have hlogRight :
      Real.log (rootDiscriminant P ^ 2 / 4) =
        2 * Real.log (rootDiscriminant P / 2) := by
    rw [show rootDiscriminant P ^ 2 / 4 =
      (rootDiscriminant P / 2) ^ 2 by ring, Real.log_pow]
    norm_num
  rw [hlogLeft] at hlog
  rw [hlogRight]
  nlinarith

lemma logMajorant_lt_half_square
    (ha : 10 < aLog P) (hg : 10 < gapLog P) :
    2 * (aLog P * bLog P +
      aLog P * (gapLog P + Real.log 2) +
      bLog P * (gapLog P + Real.log 2)) <
        (aLog P + bLog P + gapLog P - 3 * Real.log 2) ^ 2 := by
  have hb : 10 < bLog P := ha.trans (aLog_lt_bLog P)
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have ha8 : 8 * Real.log 2 < aLog P := by nlinarith
  have hb8 : 8 * Real.log 2 < bLog P := by nlinarith
  have hg6 : 6 * Real.log 2 < gapLog P := by nlinarith
  have hapos : 0 < aLog P := by linarith
  have hbpos : 0 < bLog P := by linarith
  have hgpos : 0 < gapLog P := by linarith
  have haSq : 8 * Real.log 2 * aLog P < aLog P ^ 2 := by
    have := mul_pos (by linarith : 0 < aLog P - 8 * Real.log 2) hapos
    nlinarith
  have hbSq : 8 * Real.log 2 * bLog P < bLog P ^ 2 := by
    have := mul_pos (by linarith : 0 < bLog P - 8 * Real.log 2) hbpos
    nlinarith
  have hgSq : 6 * Real.log 2 * gapLog P < gapLog P ^ 2 := by
    have := mul_pos (by linarith : 0 < gapLog P - 6 * Real.log 2) hgpos
    nlinarith
  nlinarith [sq_nonneg (Real.log 2)]

theorem candidateExpression_lt_one_eighth_log_discriminant_sq
    (ha : 10 < aLog P) (hg : 10 < gapLog P) :
    candidateRegulatorExpression P <
      (1 / 8 : ℝ) * Real.log (rootDiscriminant P ^ 2 / 4) ^ 2 := by
  let s := aLog P + bLog P + gapLog P - 3 * Real.log 2
  let m := aLog P * bLog P +
    aLog P * (gapLog P + Real.log 2) +
    bLog P * (gapLog P + Real.log 2)
  let d := Real.log (rootDiscriminant P ^ 2 / 4)
  have hb : 10 < bLog P := ha.trans (aLog_lt_bLog P)
  have hL : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hs : 0 < s := by
    dsimp [s]
    nlinarith
  have hcm : candidateRegulatorExpression P ≤ m := by
    exact candidateRegulatorExpression_le_logMajorant P ha hg
  have hm : 2 * m < s ^ 2 := by
    exact logMajorant_lt_half_square P ha hg
  have hd : 2 * s < d := by
    exact log_discriminant_lower P ha
  have hsum : 0 < d + 2 * s := by nlinarith
  have hsquares : (2 * s) ^ 2 < d ^ 2 := by
    have := mul_pos (sub_pos.mpr hd) hsum
    nlinarith
  nlinarith

theorem candidate_regulator_lt_twice_order_regulator
    (ha : 10 < aLog P) (hg : 10 < gapLog P) :
    NumberField.Units.regOfFamily (mappedCandidate P) <
      2 * (cubicOrder P).regulator := by
  have hc := candidateExpression_lt_one_eighth_log_discriminant_sq P ha hg
  have hcusick := cusick_lower_bound_ABC P
  rw [candidate_regulator_exact P,
    abs_of_pos (candidateRegulatorExpression_pos P)]
  nlinarith

theorem candidateIndex_lt_two_of_large
    (ha : 10 < aLog P) (hg : 10 < gapLog P) :
    candidateIndex P < 2 := by
  have hreg := candidate_regulator_lt_twice_order_regulator P ha hg
  have hratio := candidate_regulator_div_order_regulator P
  have hOpos := (cubicOrder P).regulator_pos
  have hratio' : (candidateIndex P : ℝ) =
      NumberField.Units.regOfFamily (mappedCandidate P) /
        (cubicOrder P).regulator := hratio.symm
  have hcast : (candidateIndex P : ℝ) < 2 := by
    rw [hratio']
    exact (div_lt_iff₀ hOpos).mpr (by nlinarith)
  exact_mod_cast hcast

/-- If the regulator comparison makes the integer index strictly smaller
than two, the candidate units are fundamental.  This packages the last,
purely integral, step of Proposition 3.4. -/
theorem fundamental_of_candidateIndex_lt_two
    (hidx : candidateIndex P < 2) :
    (cubicOrder P).IsFundamentalFamily (candidateUnitFamily P) := by
  have hpos : 0 < candidateIndex P := by
    let U := candidateSubgroup P
    let V := (cubicOrder P).unitSubgroup
    have hV : V.FiniteIndex := inferInstance
    have hle : U ≤ V := candidateSubgroup_le_orderUnits P
    have hclosure : (Subgroup.closure
        (Set.range (mappedCandidate P))).FiniteIndex :=
      NumberField.Units.isMaxRank_iff_closure_finiteIndex.mp
        (mappedCandidate_isMaxRank P)
    have hU : U.FiniteIndex :=
      (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
        (Subgroup.closure (Set.range (mappedCandidate P)))).mp hclosure
    have hne : U.relIndex V ≠ 0 := by
      intro hz
      exact Subgroup.FiniteIndex.index_ne_zero
        (Subgroup.index_eq_zero_of_relIndex_eq_zero hz)
    exact Nat.pos_of_ne_zero hne
  have hone : candidateIndex P = 1 := by omega
  change candidateSubgroup P = (cubicOrder P).unitSubgroup
  apply le_antisymm (candidateSubgroup_le_orderUnits P)
  exact Subgroup.relIndex_eq_one.mp hone

/-- Proposition 3.4, with an explicit harmless threshold. -/
theorem candidateUnitFamily_isFundamental_of_large
    (ha : 10 < Real.log (P.a₁ : ℝ))
    (hg : 10 < Real.log ((P.a₂ : ℝ) - P.a₁)) :
    (cubicOrder P).IsFundamentalFamily (candidateUnitFamily P) := by
  apply fundamental_of_candidateIndex_lt_two P
  exact candidateIndex_lt_two_of_large P ha hg

/-! ## Generator decomposition -/

/-- A paper-faithful generator statement in the maximal-order unit group.
The residual factor is torsion (and therefore is `±1` in this odd-degree
field). -/
theorem unitMap_eq_candidates_mul_torsion
    (hfund : (cubicOrder P).IsFundamentalFamily
      (candidateUnitFamily P))
    (u : (cubicOrder P).carrierˣ) :
    ∃ m n : ℤ, ∃ z : (NumberField.RingOfIntegers (ABCField P))ˣ,
      z ∈ NumberField.Units.torsion (ABCField P) ∧
      (cubicOrder P).unitMap u =
        (cubicOrder P).unitMap (alphaUnit P) ^ m *
          (cubicOrder P).unitMap (alphaSubOneUnit P) ^ n * z := by
  have huO : (cubicOrder P).unitMap u ∈
      (cubicOrder P).unitSubgroup := ⟨u, rfl⟩
  change candidateSubgroup P = (cubicOrder P).unitSubgroup at hfund
  have huC : (cubicOrder P).unitMap u ∈ candidateSubgroup P := by
    rw [hfund]
    exact huO
  obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup.mp huC)
  obtain ⟨a, ha⟩ := Subgroup.exists_of_mem_closure_range
    (mappedCandidate P) y hy
  let eRank : Fin (NumberField.Units.rank (ABCField P)) ≃ Fin 2 :=
    finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))
  refine ⟨a (eRank.symm 0), a (eRank.symm 1), z, hz, ?_⟩
  rw [← hyz, ha, ← (eRank.symm).prod_comp]
  rw [Fin.prod_univ_two]
  have he0 : eRank.symm 0 =
      (finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 0 := rfl
  have he1 : eRank.symm 1 =
      (finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 1 := rfl
  rw [he0, he1]
  simp only [mappedCandidate, Cusick.CubicOrder.mapUnitFamily,
    candidateUnitFamily_zero, candidateUnitFamily_one]

/-- Proposition 3.4 in generator form after the injective inclusion into the
maximal order. -/
theorem unitMap_eq_candidates_or_neg
    (hfund : (cubicOrder P).IsFundamentalFamily
      (candidateUnitFamily P))
    (u : (cubicOrder P).carrierˣ) :
    ∃ m n : ℤ,
      (cubicOrder P).unitMap u =
          (cubicOrder P).unitMap (alphaUnit P) ^ m *
            (cubicOrder P).unitMap (alphaSubOneUnit P) ^ n ∨
      (cubicOrder P).unitMap u =
        -((cubicOrder P).unitMap (alphaUnit P) ^ m *
            (cubicOrder P).unitMap (alphaSubOneUnit P) ^ n) := by
  obtain ⟨m, n, z, hz, hu⟩ := unitMap_eq_candidates_mul_torsion P hfund u
  have hz' := NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
    (Cusick.CubicOrder.degree_odd (K := ABCField P)) ⟨z, hz⟩
  have hzval : z = 1 ∨ z = -1 := by simpa using hz'
  refine ⟨m, n, ?_⟩
  rcases hzval with rfl | rfl
  · left
    simpa using hu
  · right
    simpa using hu

/-- The literal equality inside the ABC order's unit group.  This is the
form used in the suborder calculation: every unit is a sign times powers of
the two canonical candidates. -/
theorem unit_eq_candidateFamily_or_neg
    (hfund : (cubicOrder P).IsFundamentalFamily
      (candidateUnitFamily P))
    (u : (cubicOrder P).carrierˣ) :
    ∃ m n : ℤ,
      u = (candidateUnitFamily P
          ((finCongr (Cusick.CubicOrder.unitRank_eq_two
            (cubicOrder P))).symm 0)) ^ m *
        (candidateUnitFamily P
          ((finCongr (Cusick.CubicOrder.unitRank_eq_two
            (cubicOrder P))).symm 1)) ^ n ∨
      u = -((candidateUnitFamily P
          ((finCongr (Cusick.CubicOrder.unitRank_eq_two
            (cubicOrder P))).symm 0)) ^ m *
        (candidateUnitFamily P
          ((finCongr (Cusick.CubicOrder.unitRank_eq_two
            (cubicOrder P))).symm 1)) ^ n) := by
  obtain ⟨m, n, hu | hu⟩ := unitMap_eq_candidates_or_neg P hfund u
  · refine ⟨m, n, Or.inl ?_⟩
    apply (cubicOrder P).unitMap_injective
    rw [map_mul, map_zpow, map_zpow,
      candidateUnitFamily_zero, candidateUnitFamily_one]
    exact hu
  · refine ⟨m, n, Or.inr ?_⟩
    apply (cubicOrder P).unitMap_injective
    rw [show (cubicOrder P).unitMap
        (-((candidateUnitFamily P
          ((finCongr (Cusick.CubicOrder.unitRank_eq_two
            (cubicOrder P))).symm 0)) ^ m *
        (candidateUnitFamily P
          ((finCongr (Cusick.CubicOrder.unitRank_eq_two
            (cubicOrder P))).symm 1)) ^ n)) =
        -((cubicOrder P).unitMap
            ((candidateUnitFamily P
              ((finCongr (Cusick.CubicOrder.unitRank_eq_two
                (cubicOrder P))).symm 0)) ^ m *
            (candidateUnitFamily P
              ((finCongr (Cusick.CubicOrder.unitRank_eq_two
                (cubicOrder P))).symm 1)) ^ n)) by
          apply Units.ext
          rfl]
    rw [map_mul, map_zpow, map_zpow,
      candidateUnitFamily_zero, candidateUnitFamily_one]
    exact hu

/-- The same statement with the concrete `orderCarrier` and named canonical
units appearing verbatim. -/
theorem orderUnit_eq_alphaUnits_or_neg
    (hfund : (cubicOrder P).IsFundamentalFamily
      (candidateUnitFamily P))
    (u : (orderCarrier P)ˣ) :
    ∃ m n : ℤ,
      u = alphaUnit P ^ m * alphaSubOneUnit P ^ n ∨
      u = -(alphaUnit P ^ m * alphaSubOneUnit P ^ n) := by
  let u' : (cubicOrder P).carrierˣ := by
    change (orderCarrier P)ˣ
    exact u
  obtain ⟨m, n, hu | hu⟩ := unit_eq_candidateFamily_or_neg P hfund u'
  · refine ⟨m, n, Or.inl ?_⟩
    rw [candidateUnitFamily_zero, candidateUnitFamily_one] at hu
    change u = alphaUnit P ^ m * alphaSubOneUnit P ^ n at hu
    exact hu
  · refine ⟨m, n, Or.inr ?_⟩
    rw [candidateUnitFamily_zero, candidateUnitFamily_one] at hu
    change u = -(alphaUnit P ^ m * alphaSubOneUnit P ^ n) at hu
    exact hu

/-- The same decomposition after applying Dirichlet's logarithmic embedding;
the torsion factor disappears. -/
theorem logEmbedding_unitMap_eq_zsmul_candidates
    (hfund : (cubicOrder P).IsFundamentalFamily
      (candidateUnitFamily P))
    (u : (cubicOrder P).carrierˣ) :
    ∃ m n : ℤ,
      NumberField.Units.logEmbedding (ABCField P)
          (Additive.ofMul ((cubicOrder P).unitMap u)) =
        m • NumberField.Units.logEmbedding (ABCField P)
            (Additive.ofMul ((cubicOrder P).unitMap (alphaUnit P))) +
          n • NumberField.Units.logEmbedding (ABCField P)
            (Additive.ofMul
              ((cubicOrder P).unitMap (alphaSubOneUnit P))) := by
  obtain ⟨m, n, z, hz, hu⟩ := unitMap_eq_candidates_mul_torsion P hfund u
  refine ⟨m, n, ?_⟩
  rw [hu]
  have hzlog : NumberField.Units.logEmbedding (ABCField P)
      (Additive.ofMul z) = 0 := by
    exact NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr hz
  simp [hzlog]

end FundamentalUnits

end ABCOrders
