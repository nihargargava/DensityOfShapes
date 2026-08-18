import CusickRegulator
open scoped NumberField
noncomputable section
namespace Cusick.CubicOrder
open NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem
variable {K : Type*} [Field K] [NumberField K] [Fact (Module.finrank ℚ K = 3)]
  (O : Cusick.CubicOrder K) [NumberField.IsTotallyReal K]

open scoped Classical in
noncomputable def pairPlace : Fin 2 ≃ {w : InfinitePlace K // w ≠ w₀} :=
  (finCongr O.unitRank_eq_two.symm).trans (NumberField.Units.equivFinRank K)

open scoped Classical in
noncomputable def fundLog (i j : Fin 2) : ℝ :=
  Real.log ((O.pairPlace j).val (O.orderFundUnits i))

open scoped Classical in
lemma reg_eq : O.regulator = |(Matrix.of fun i j : Fin 2 => O.fundLog i j).det| := by
  simpa [fundLog, pairPlace, NumberField.IsTotallyReal.mult_eq] using O.regulator_eq_abs_det

open scoped Classical in
theorem exists_short_vector :
    ∃ p : ℤ × ℤ, Cusick.BinaryQuadratic.Primitive p ∧
      let x := (p.1 : ℝ) * O.fundLog 0 0 + (p.2 : ℝ) * O.fundLog 1 0
      let y := (p.1 : ℝ) * O.fundLog 0 1 + (p.2 : ℝ) * O.fundLog 1 1
      0 < 2 * (x^2 + x*y + y^2) ∧
        2 * (x^2 + x*y + y^2) ≤ 2 * O.regulator := by
  let a := O.fundLog 0 0
  let b := O.fundLog 0 1
  let c := O.fundLog 1 0
  let d := O.fundLog 1 1
  let A := 2 * (a^2 + a*b + b^2)
  let B := 2*a*c + a*d + b*c + 2*b*d
  let C := 2 * (c^2 + c*d + d^2)
  have hreg : O.regulator = |a*d-b*c| := by
    rw [O.reg_eq]
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    rfl
  have hdet : A*C-B^2 = 3*(a*d-b*c)^2 := by
    dsimp [A,B,C]
    ring
  have hminor : a*d-b*c ≠ 0 := by
    intro h
    have := O.regulator_pos
    rw [hreg, h, abs_zero] at this
    exact lt_irrefl 0 this
  have hA : 0 < A := by
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      have hminor' : a*d-b*c = 0 := by rw [h.1, h.2]; ring
      exact hminor hminor'
    dsimp [A]
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (a+b)]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg (a+b)]
  have hdetpos : 0 < A*C-B^2 := by
    rw [hdet]
    positivity
  obtain ⟨p, hpprim, hpq, hpbound⟩ :=
    Cusick.BinaryQuadratic.exists_primitive_q_le hA hdetpos
  refine ⟨p, hpprim, ?_⟩
  have hqform :
      Cusick.BinaryQuadratic.q A B C p =
        2 * (((p.1 : ℝ)*a + (p.2 : ℝ)*c)^2 +
          ((p.1 : ℝ)*a + (p.2 : ℝ)*c)*((p.1 : ℝ)*b + (p.2 : ℝ)*d) +
          ((p.1 : ℝ)*b + (p.2 : ℝ)*d)^2) := by
    dsimp [Cusick.BinaryQuadratic.q, A, B, C]
    ring
  dsimp only
  constructor
  · simpa [a,b,c,d, hqform] using hpq
  · rw [hqform] at hpbound
    have hsqrt : Real.sqrt ((4 / 3 : ℝ) * (A*C-B^2)) = 2 * |a*d-b*c| := by
      rw [hdet]
      have : (4 / 3 : ℝ) * (3 * (a*d-b*c)^2) = (2 * |a*d-b*c|)^2 := by
        nlinarith [sq_abs (a*d-b*c)]
      rw [this, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity
    rw [hsqrt, ← hreg] at hpbound
    simpa [a,b,c,d] using hpbound

end Cusick.CubicOrder

namespace Cusick.CubicOrder
open NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem
variable {K : Type*} [Field K] [NumberField K] [Fact (Module.finrank ℚ K = 3)]
  (O : Cusick.CubicOrder K) [NumberField.IsTotallyReal K]

open scoped Classical in
theorem testFundMem (i : Fin 2) : O.orderFundUnits i ∈ O.unitSubgroup := by
  exact ((O.orderUnitBasis i).property).choose_spec.1

open scoped Classical in
theorem exists_short_unit :
    ∃ u : (𝓞 K)ˣ, u ∈ O.unitSubgroup ∧
      let x := Real.log ((O.pairPlace 0).val u)
      let y := Real.log ((O.pairPlace 1).val u)
      0 < 2 * (x^2+x*y+y^2) ∧
        2 * (x^2+x*y+y^2) ≤ 2 * O.regulator := by
  obtain ⟨p, hpprim, hp, hbound⟩ := O.exists_short_vector
  let u := O.orderFundUnits 0 ^ p.1 * O.orderFundUnits 1 ^ p.2
  refine ⟨u, ?_, ?_⟩
  · exact O.unitSubgroup.mul_mem
      (O.unitSubgroup.zpow_mem (O.testFundMem 0) p.1)
      (O.unitSubgroup.zpow_mem (O.testFundMem 1) p.2)
  have hlog (j : Fin 2) :
      Real.log ((O.pairPlace j).val u) =
        (p.1 : ℝ) * O.fundLog 0 j + (p.2 : ℝ) * O.fundLog 1 j := by
    have h := congrFun (show
      logEmbedding K (Additive.ofMul u) =
        p.1 • logEmbedding K (Additive.ofMul (O.orderFundUnits 0)) +
        p.2 • logEmbedding K (Additive.ofMul (O.orderFundUnits 1)) by
          simp [u]) (O.pairPlace j)
    simpa [fundLog, NumberField.IsTotallyReal.mult_eq] using h
  dsimp only
  rw [hlog 0, hlog 1]
  exact ⟨hp, hbound⟩

end Cusick.CubicOrder
