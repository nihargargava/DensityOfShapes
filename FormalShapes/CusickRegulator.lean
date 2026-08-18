import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Cusick's lower bound for regulators of cubic orders

This file isolates the arithmetic estimate used as Theorem 2.4 in

Nguyen-Thi Dang, Nihar Gargava, and Jialun Li,
*Density of shapes of periodic tori in the cubic case*, arXiv:2502.12754.

An order is represented by an actual rank-three `ℤ`-subalgebra of the ring of
integers.  Its discriminant is the usual trace discriminant, rather than the
covolume of an unrelated abstract lattice.  Its unit group maps injectively to
the unit group of the maximal order, and its regulator is expressed by the
standard finite-index formula.
-/

open scoped NumberField IntermediateField

noncomputable section

namespace Cusick

/-- The elementary sharp estimate for the three difference factors in the
discriminant of a cubic unit. -/
lemma cubic_factor_nonneg_le_two {v w : ℝ}
    (hv : v ∈ Set.Icc (-1 : ℝ) 1) (hw : w ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ (1 - v) * (1 - w) * (1 - v * w) ∧
      (1 - v) * (1 - w) * (1 - v * w) ≤ 2 := by
  have hv1 : 0 ≤ 1 - v := by linarith [hv.2]
  have hw1 : 0 ≤ 1 - w := by linarith [hw.2]
  have hvw : v * w ≤ 1 := by
    calc
      v * w ≤ |v * w| := le_abs_self _
      _ = |v| * |w| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (abs_le.mpr hv) (abs_le.mpr hw)
        (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  constructor
  · positivity
  · by_cases hw0 : 0 ≤ w
    · have haux : (1 - v) * (1 - v * w) ≤ 2 * (1 + w) := by
        have hnon : 0 ≤ (v + 1) * (1 + 2 * w - v * w) := by
          apply mul_nonneg
          · linarith [hv.1]
          · nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hv.2)]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left haux hw1
      nlinarith [sq_nonneg w]
    · by_cases hv0 : 0 ≤ v
      · have haux : (1 - w) * (1 - w * v) ≤ 2 * (1 + v) := by
          have hnon : 0 ≤ (w + 1) * (1 + 2 * v - w * v) := by
            apply mul_nonneg
            · linarith [hw.1]
            · nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hw.2)]
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left haux hv1
        nlinarith [sq_nonneg v]
      · have hv0' : v ≤ 0 := le_of_not_ge hv0
        have hw0' : w ≤ 0 := le_of_not_ge hw0
        have hab : (1 - v) * (1 - w) ≤ 2 * (1 + v * w) := by
          nlinarith [mul_nonneg (by linarith [hv.1] : 0 ≤ 1 + v)
            (by linarith [hw.1] : 0 ≤ 1 + w)]
        have habpos : 0 ≤ 1 - v * w := by nlinarith
        have hmul := mul_le_mul_of_nonneg_right hab habpos
        nlinarith [sq_nonneg (v * w)]

namespace BinaryQuadratic

/-- A real binary quadratic form, evaluated on an integral vector. -/
def q (A B C : ℝ) (p : ℤ × ℤ) : ℝ :=
  A * (p.1 : ℝ) ^ 2 + 2 * B * (p.1 : ℝ) * (p.2 : ℝ) +
    C * (p.2 : ℝ) ^ 2

lemma q_completion {A B C : ℝ} (hA : A ≠ 0) (p : ℤ × ℤ) :
    q A B C p = A * ((p.1 : ℝ) + B / A * (p.2 : ℝ)) ^ 2 +
      (A * C - B ^ 2) / A * (p.2 : ℝ) ^ 2 := by
  dsimp [q]
  field_simp
  ring

lemma q_pos {A B C : ℝ} (hA : 0 < A) (hdet : 0 < A * C - B ^ 2)
    {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < q A B C p := by
  rw [q_completion hA.ne']
  have hdA : 0 < (A * C - B ^ 2) / A := div_pos hdet hA
  rcases ne_or_eq p.2 0 with hy | hy
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg hA.le (sq_nonneg _))
      (mul_pos hdA (sq_pos_of_ne_zero (by exact_mod_cast hy)))
  · have hx : p.1 ≠ 0 := by
      intro hx
      apply hp
      exact Prod.ext hx hy
    simpa [hy] using
      mul_pos hA
        (sq_pos_of_ne_zero
          (by exact_mod_cast hx : (p.1 : ℝ) ≠ 0))

/-- A positive-definite quadratic form has only finitely many integral
vectors in each sublevel set. -/
lemma sublevel_finite {A B C r : ℝ} (hA : 0 < A)
    (hdet : 0 < A * C - B ^ 2) :
    {p : ℤ × ℤ | q A B C p ≤ r}.Finite := by
  let d := A * C - B ^ 2
  let cy := A / d * max r 0 + 1
  obtain ⟨Ny : ℕ, hNy⟩ := exists_nat_gt cy
  let cx := max r 0 / A + 1
  let bx := |B / A| * Ny + cx + 1
  obtain ⟨Nx : ℕ, hNx⟩ := exists_nat_gt bx
  apply ((Set.finite_Icc (-(Nx : ℤ)) (Nx : ℤ)).prod
    (Set.finite_Icc (-(Ny : ℤ)) (Ny : ℤ))).subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hcomp := q_completion (B := B) (C := C) hA.ne' p
  have hd : 0 < d := hdet
  have hdA : 0 < d / A := div_pos hd hA
  have hq0 : q A B C p ≤ max r 0 :=
    hp.trans (le_max_left _ _)
  have hyterm : d / A * (p.2 : ℝ) ^ 2 ≤ max r 0 := by
    rw [hcomp] at hq0
    nlinarith [mul_nonneg hA.le
      (sq_nonneg ((p.1 : ℝ) + B / A * (p.2 : ℝ)))]
  have hy2 : (p.2 : ℝ) ^ 2 ≤ A / d * max r 0 := by
    calc
      (p.2 : ℝ) ^ 2 =
          A / d * (d / A * (p.2 : ℝ) ^ 2) := by field_simp
      _ ≤ A / d * max r 0 :=
        mul_le_mul_of_nonneg_left hyterm (div_nonneg hA.le hd.le)
  have hyupper : (p.2 : ℝ) < Ny := by
    have hcy : A / d * max r 0 + 1 < Ny := hNy
    nlinarith [sq_nonneg ((p.2 : ℝ) - 1 / 2)]
  have hylower : -(Ny : ℝ) < (p.2 : ℝ) := by
    have hcy : A / d * max r 0 + 1 < Ny := hNy
    nlinarith [sq_nonneg ((p.2 : ℝ) + 1 / 2)]
  have hyI : p.2 ∈ Set.Icc (-(Ny : ℤ)) (Ny : ℤ) := by
    constructor
    · exact_mod_cast hylower.le
    · exact_mod_cast hyupper.le
  have hxterm :
      A * ((p.1 : ℝ) + B / A * (p.2 : ℝ)) ^ 2 ≤ max r 0 := by
    rw [hcomp] at hq0
    nlinarith [mul_nonneg hdA.le (sq_nonneg (p.2 : ℝ))]
  have hx2 :
      ((p.1 : ℝ) + B / A * (p.2 : ℝ)) ^ 2 ≤ max r 0 / A := by
    exact (le_div_iff₀ hA).mpr (by simpa [mul_comm] using hxterm)
  have hyabs : |(p.2 : ℝ)| ≤ Ny := by
    rw [abs_le]
    exact ⟨hylower.le, hyupper.le⟩
  have hcenterabs :
      |(p.1 : ℝ) + B / A * (p.2 : ℝ)| ≤ cx := by
    rw [abs_le]
    constructor <;> dsimp [cx] <;>
      nlinarith [
        sq_nonneg (((p.1 : ℝ) + B / A * (p.2 : ℝ)) - 1 / 2),
        sq_nonneg (((p.1 : ℝ) + B / A * (p.2 : ℝ)) + 1 / 2)]
  have hbx : |B / A * (p.2 : ℝ)| ≤ |B / A| * Ny := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
  have hxabs : |(p.1 : ℝ)| ≤ |B / A| * Ny + cx := by
    calc
      |(p.1 : ℝ)| =
          |((p.1 : ℝ) + B / A * (p.2 : ℝ)) -
            B / A * (p.2 : ℝ)| := by ring_nf
      _ ≤ |(p.1 : ℝ) + B / A * (p.2 : ℝ)| +
          |B / A * (p.2 : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith [add_le_add hcenterabs hbx]
  have hboundx : |B / A| * Ny + cx < Nx := by
    dsimp [bx] at hNx
    linarith
  have hxupper : (p.1 : ℝ) < Nx :=
    lt_of_le_of_lt (le_trans (le_abs_self _) hxabs) hboundx
  have hxlower : -(Nx : ℝ) < (p.1 : ℝ) := by
    calc
      -(Nx : ℝ) < -(|B / A| * Ny + cx) := neg_lt_neg hboundx
      _ ≤ -|(p.1 : ℝ)| := neg_le_neg hxabs
      _ ≤ (p.1 : ℝ) := neg_abs_le _
  have hxI : p.1 ∈ Set.Icc (-(Nx : ℤ)) (Nx : ℤ) := by
    constructor
    · exact_mod_cast hxlower.le
    · exact_mod_cast hxupper.le
  exact ⟨hxI, hyI⟩

/-- An integral vector is primitive when it can be completed to a unimodular
pair. -/
def Primitive (p : ℤ × ℤ) : Prop :=
  ∃ a b : ℤ, p.1 * b - p.2 * a = 1

lemma primitive_one_zero : Primitive (1, 0) := by
  exact ⟨0, 1, by norm_num⟩

lemma primitive_n_one (n : ℤ) : Primitive (n, 1) := by
  exact ⟨-1, 0, by norm_num⟩

/-- The sharp two-dimensional Hermite bound, in the binary quadratic form
normalization used by Cusick. -/
theorem exists_primitive_q_le {A B C : ℝ} (hA : 0 < A)
    (hdet : 0 < A * C - B ^ 2) :
    ∃ p : ℤ × ℤ, Primitive p ∧ 0 < q A B C p ∧
      q A B C p ≤ Real.sqrt ((4 / 3 : ℝ) * (A * C - B ^ 2)) := by
  let S : Set (ℤ × ℤ) :=
    {p | Primitive p ∧ q A B C p ≤ A}
  have hSf : S.Finite :=
    (sublevel_finite (r := A) hA hdet).subset fun _ hp ↦ hp.2
  have hSnonempty : S.Nonempty := by
    refine ⟨(1, 0), primitive_one_zero, ?_⟩
    simp [q]
  obtain ⟨p, hpS, hpmin⟩ :=
    Set.exists_min_image S (q A B C) hSf hSnonempty
  have hpne : p ≠ 0 := by
    intro hp0
    obtain ⟨a, b, hab⟩ := hpS.1
    simp [hp0] at hab
  have hpq : 0 < q A B C p := q_pos hA hdet hpne
  have hmin : ∀ z : ℤ × ℤ, Primitive z →
      q A B C p ≤ q A B C z := by
    intro z hz
    by_cases hzA : q A B C z ≤ A
    · exact hpmin z ⟨hz, hzA⟩
    · exact hpS.2.trans (le_of_not_ge hzA)
  obtain ⟨x₁, y₁, hdetM⟩ := hpS.1
  let A' : ℝ := q A B C p
  let B' : ℝ :=
    A * p.1 * x₁ + B * (p.1 * y₁ + p.2 * x₁) +
      C * p.2 * y₁
  let C' : ℝ := q A B C (x₁, y₁)
  have hdetMR :
      (p.1 : ℝ) * (y₁ : ℝ) - (p.2 : ℝ) * (x₁ : ℝ) = 1 := by
    exact_mod_cast hdetM
  have hdet' : A' * C' - B' ^ 2 = A * C - B ^ 2 := by
    dsimp [A', B', C', q]
    rw [show
      (A * (p.1 : ℝ) ^ 2 + 2 * B * (p.1 : ℝ) * (p.2 : ℝ) +
          C * (p.2 : ℝ) ^ 2) *
          (A * (x₁ : ℝ) ^ 2 + 2 * B * (x₁ : ℝ) * (y₁ : ℝ) +
            C * (y₁ : ℝ) ^ 2) -
        (A * (p.1 : ℝ) * (x₁ : ℝ) +
          B * ((p.1 : ℝ) * (y₁ : ℝ) +
            (p.2 : ℝ) * (x₁ : ℝ)) +
          C * (p.2 : ℝ) * (y₁ : ℝ)) ^ 2 =
        (A * C - B ^ 2) *
          ((p.1 : ℝ) * (y₁ : ℝ) -
            (p.2 : ℝ) * (x₁ : ℝ)) ^ 2 by ring,
      hdetMR]
    ring
  let n : ℤ := round (-B' / A')
  let z : ℤ × ℤ := (n * p.1 + x₁, n * p.2 + y₁)
  have hzprim : Primitive z := by
    refine ⟨-p.1, -p.2, ?_⟩
    dsimp [z]
    nlinarith
  have hqexpand :
      q A B C z = A' * (n : ℝ) ^ 2 + 2 * B' * n + C' := by
    dsimp [z, A', B', C', q]
    push_cast
    ring
  have hnabs : |(n : ℝ) + B' / A'| ≤ (1 / 2 : ℝ) := by
    calc
      |(n : ℝ) + B' / A'| = |-B' / A' - (n : ℝ)| := by
        rw [show -B' / A' - (n : ℝ) =
          -((n : ℝ) + B' / A') by ring, abs_neg]
      _ ≤ 1 / 2 := abs_sub_round (-B' / A')
  have hnsq :
      ((n : ℝ) + B' / A') ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [sq_le_sq]
    simpa using hnabs
  have hA' : 0 < A' := hpq
  have hcompletion :
      q A B C z = A' * ((n : ℝ) + B' / A') ^ 2 +
        (A' * C' - B' ^ 2) / A' := by
    rw [hqexpand]
    field_simp [hA'.ne']
    ring
  have hshort := hmin z hzprim
  rw [hcompletion, hdet'] at hshort
  have hquarter :
      A' * ((n : ℝ) + B' / A') ^ 2 ≤
        A' * (1 / 2 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hnsq hA'.le
  have hshort' :
      A' ≤ A' * (1 / 2 : ℝ) ^ 2 +
        (A * C - B ^ 2) / A' := by
    change A' ≤ _ at hshort
    exact hshort.trans (add_le_add hquarter le_rfl)
  have hsq :
      A' ^ 2 ≤ (4 / 3 : ℝ) * (A * C - B ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hshort' hA'.le
    field_simp [hA'.ne'] at hmul
    nlinarith
  refine ⟨p, hpS.1, hpq, ?_⟩
  rw [Real.le_sqrt hA'.le
    (mul_nonneg (by norm_num) hdet.le)]
  exact hsq

end BinaryQuadratic

variable (K : Type*) [Field K] [NumberField K]

/-- An order in a cubic number field, represented as an actual rank-three
`ℤ`-subalgebra of the maximal order.

The typeclass assumption says that the ambient number field has degree three.
The basis makes the subalgebra a full-rank `ℤ`-lattice, so this is the usual
notion of an order in `K`. -/
structure CubicOrder [Fact (Module.finrank ℚ K = 3)] where
  carrier : Subalgebra ℤ (𝓞 K)
  basis : Module.Basis (Fin 3) ℤ carrier

namespace CubicOrder

variable {K} [Fact (Module.finrank ℚ K = 3)] (O : CubicOrder K)

instance : Coe (CubicOrder K) (Subalgebra ℤ (𝓞 K)) := ⟨carrier⟩

/-- The signed trace discriminant of the chosen integral basis of `O`. -/
def signedDiscriminant : ℤ :=
  Algebra.discr ℤ (fun i ↦ (O.basis i : 𝓞 K))

/-- The conventional positive discriminant of `O`.

For a totally real cubic order the signed trace discriminant is already
positive.  Taking `natAbs` also gives the standard absolute-discriminant
convention without needing that sign fact in the interface. -/
def discriminant : ℕ :=
  (signedDiscriminant O).natAbs

theorem discriminant_eq_natAbs_discr :
    O.discriminant =
      (Algebra.discr ℤ (fun i ↦ (O.basis i : 𝓞 K))).natAbs :=
  rfl

/-- The order discriminant does not depend on its chosen integral basis. -/
theorem discriminant_eq_of_basis
    (b : Module.Basis (Fin 3) ℤ O.carrier) :
    (Algebra.discr ℤ (fun i ↦ (b i : 𝓞 K))).natAbs =
      O.discriminant := by
  rw [discriminant, signedDiscriminant]
  congr 1
  convert! Algebra.discr_of_matrix_vecMul
    (fun i ↦ (O.basis i : 𝓞 K)) (O.basis.toMatrix b)
  · rename_i i
    have hb := congrArg (fun x : O.carrier ↦ (x : 𝓞 K))
      (congrFun (O.basis.toMatrix_map_vecMul b) i).symm
    simpa [Matrix.vecMul, dotProduct, Algebra.smul_def] using hb
  · suffices IsUnit (O.basis.toMatrix b).det by
      rw [Int.isUnit_iff, ← sq_eq_one_iff] at this
      rw [this, one_mul]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b O.basis]
    exact LinearEquiv.isUnit_det (LinearEquiv.refl ℤ O.carrier) b O.basis

/-- A rank-three integral basis of the maximal order, reindexed compatibly
with the chosen order basis. -/
def maximalOrderBasis (O : CubicOrder K) :
    Module.Basis (Fin 3) ℤ (𝓞 K) := by
  classical
  apply (NumberField.RingOfIntegers.basis K).reindex
  apply Fintype.equivOfCardEq
  rw [← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
    NumberField.RingOfIntegers.rank K, (Fact.out : Module.finrank ℚ K = 3),
    Fintype.card_fin]

/-- Inclusion of an order into the maximal order. -/
def toMaximalOrder : O.carrier →+* 𝓞 K :=
  O.carrier.val.toRingHom

theorem toMaximalOrder_injective :
    Function.Injective O.toMaximalOrder := by
  intro x y h
  exact Subtype.ext h

/-- Inclusion of the units of `O` into the units of the maximal order. -/
def unitMap : O.carrierˣ →* (𝓞 K)ˣ :=
  Units.map O.toMaximalOrder.toMonoidHom

theorem unitMap_injective : Function.Injective O.unitMap :=
  Units.map_injective O.toMaximalOrder_injective

/-- The subgroup of maximal-order units which come from units of `O`. -/
def unitSubgroup : Subgroup (𝓞 K)ˣ :=
  O.unitMap.range

theorem unitSubgroup_eq_range :
    O.unitSubgroup = O.unitMap.range :=
  rfl

/-! ### The order-unit subgroup has finite index -/

private theorem finite_additive_quotient :
    Finite ((𝓞 K) ⧸ O.carrier.toSubmodule) := by
  apply Submodule.finiteQuotientOfFreeOfRankEq O.carrier.toSubmodule
  calc
    Module.finrank ℤ O.carrier.toSubmodule = 3 := by
      exact (Module.finrank_eq_card_basis O.basis).trans (by simp)
    _ = Module.finrank ℚ K :=
      (Fact.out : Module.finrank ℚ K = 3).symm
    _ = Module.finrank ℤ (𝓞 K) :=
      (NumberField.RingOfIntegers.rank K).symm

/-- The cardinality of the additive quotient of the maximal order by `O`. -/
def additiveIndex : ℕ :=
  Nat.card ((𝓞 K) ⧸ O.carrier.toSubmodule)

theorem additiveIndex_ne_zero : O.additiveIndex ≠ 0 := by
  letI := finite_additive_quotient O
  exact Nat.card_ne_zero.mpr ⟨Nonempty.intro 0, inferInstance⟩

/-- The determinant of the order basis in a maximal-order basis is its
additive index. -/
theorem natAbs_det_orderBasis :
    ((O.maximalOrderBasis.toMatrix
      (fun i ↦ (O.basis i : 𝓞 K))).det).natAbs = O.additiveIndex := by
  rw [← O.maximalOrderBasis.det_apply]
  exact Submodule.natAbs_det_basis_change O.maximalOrderBasis
    O.carrier.toSubmodule O.basis

/-- The familiar discriminant-index formula for an order in the maximal
order. -/
theorem discriminant_eq_index_sq_mul :
    O.discriminant =
      O.additiveIndex ^ 2 * (NumberField.discr K).natAbs := by
  let P := O.maximalOrderBasis.toMatrix
    (fun i ↦ (O.basis i : 𝓞 K))
  have hfamily :
      Matrix.vecMul (O.maximalOrderBasis : Fin 3 → 𝓞 K)
          (P.map (algebraMap ℤ (𝓞 K))) =
        (fun i ↦ (O.basis i : 𝓞 K)) :=
    O.maximalOrderBasis.toMatrix_map_vecMul _
  have hsigned :
      O.signedDiscriminant =
        P.det ^ 2 * NumberField.discr K := by
    rw [signedDiscriminant, ← NumberField.discr_eq_discr K O.maximalOrderBasis]
    rw [← Algebra.discr_of_matrix_vecMul
      (O.maximalOrderBasis : Fin 3 → 𝓞 K) P]
    exact congrArg (Algebra.discr ℤ) hfamily.symm
  rw [discriminant, hsigned, Int.natAbs_mul, Int.natAbs_pow,
    O.natAbs_det_orderBasis]

/-- The additive index annihilates the quotient by `O`. -/
theorem additiveIndex_smul_mem (x : 𝓞 K) :
    O.additiveIndex • x ∈ O.carrier := by
  change O.additiveIndex • x ∈ O.carrier.toSubmodule
  apply (Submodule.Quotient.mk_eq_zero
    (p := O.carrier.toSubmodule)).mp
  rw [Submodule.Quotient.mk_smul]
  exact card_nsmul_eq_zero'

/-- The conductor of `O` inside the maximal order. -/
def conductor : Ideal (𝓞 K) where
  carrier := {x | ∀ y : 𝓞 K, x * y ∈ O.carrier}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy z
    rw [add_mul]
    exact O.carrier.add_mem (hx z) (hy z)
  smul_mem' := by
    intro c x hx z
    change c * x * z ∈ O.carrier
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx (c * z)

theorem algebraMap_additiveIndex_mem_conductor :
    algebraMap ℤ (𝓞 K) (O.additiveIndex : ℤ) ∈ O.conductor := by
  intro y
  simpa [Algebra.smul_def] using O.additiveIndex_smul_mem y

theorem conductor_ne_bot : O.conductor ≠ ⊥ := by
  intro h
  have hm := O.algebraMap_additiveIndex_mem_conductor
  rw [h, Ideal.mem_bot] at hm
  have hn : (O.additiveIndex : ℤ) = 0 :=
    (RingHom.injective_int (algebraMap ℤ (𝓞 K))) (by simpa using hm)
  exact O.additiveIndex_ne_zero (Int.ofNat_eq_zero.mp hn)

private theorem finite_conductor_quotient :
    Finite ((𝓞 K) ⧸ O.conductor) := by
  exact Ideal.finiteQuotientOfFreeOfNeBot O.conductor O.conductor_ne_bot

/-- Reduction modulo the conductor of `O`. -/
def reduction : (𝓞 K) →+* ((𝓞 K) ⧸ O.conductor) :=
  Ideal.Quotient.mk O.conductor

/-- Reduction of maximal-order units modulo the conductor of `O`. -/
def unitReduction : (𝓞 K)ˣ →* ((𝓞 K) ⧸ O.conductor)ˣ :=
  Units.map O.reduction.toMonoidHom

private theorem finite_unit_reduction_codomain :
    Finite (((𝓞 K) ⧸ O.conductor)ˣ) := by
  letI := finite_conductor_quotient O
  infer_instance

theorem unitReduction_ker_finiteIndex :
    O.unitReduction.ker.FiniteIndex := by
  letI := finite_unit_reduction_codomain O
  infer_instance

theorem coe_mem_carrier_of_mem_unitReduction_ker
    (u : (𝓞 K)ˣ) (hu : u ∈ O.unitReduction.ker) :
    (u : 𝓞 K) ∈ O.carrier := by
  have huq : O.reduction (u : 𝓞 K) = 1 := by
    have h := congrArg Units.val hu
    simpa [unitReduction] using h
  have hsub : (u : 𝓞 K) - 1 ∈ O.conductor := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change O.reduction ((u : 𝓞 K) - 1) = 0
    rw [map_sub, huq, map_one, sub_self]
  have hsubO : (u : 𝓞 K) - 1 ∈ O.carrier := by
    have h := hsub (1 : 𝓞 K)
    simpa [conductor] using h
  have hone : (1 : 𝓞 K) ∈ O.carrier := O.carrier.one_mem
  convert O.carrier.add_mem hsubO hone using 1
  ring

theorem unitReduction_ker_le_unitSubgroup :
    O.unitReduction.ker ≤ O.unitSubgroup := by
  intro u hu
  have huO := O.coe_mem_carrier_of_mem_unitReduction_ker u hu
  have huinvker : u⁻¹ ∈ O.unitReduction.ker :=
    O.unitReduction.ker.inv_mem hu
  have huinvO :=
    O.coe_mem_carrier_of_mem_unitReduction_ker u⁻¹ huinvker
  let v : O.carrierˣ :=
    { val := ⟨(u : 𝓞 K), huO⟩
      inv := ⟨(↑(u⁻¹) : 𝓞 K), huinvO⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  change u ∈ O.unitMap.range
  refine ⟨v, ?_⟩
  apply Units.ext
  rfl

/-- The unit group of every cubic order has finite index in the unit group of
the maximal order. -/
instance unitSubgroup_finiteIndex : O.unitSubgroup.FiniteIndex := by
  letI : O.unitReduction.ker.FiniteIndex :=
    O.unitReduction_ker_finiteIndex
  exact Subgroup.finiteIndex_of_le O.unitReduction_ker_le_unitSubgroup

/-- The regulator of an order, using the classical number-theoretic
normalization.

For a finite-index subgroup of units, the covolume of its logarithmic lattice
is its index times the regulator of the maximal order.  Mathlib's
`NumberField.Units.regulator` uses this same classical normalization (the
absolute determinant of a logarithmic minor). -/
def regulator : ℝ :=
  (O.unitSubgroup.index : ℝ) * NumberField.Units.regulator K

theorem regulator_eq_index_mul :
    O.regulator =
      (O.unitSubgroup.index : ℝ) * NumberField.Units.regulator K :=
  rfl

theorem regulator_nonneg : 0 ≤ O.regulator := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (le_of_lt (NumberField.Units.regulator_pos K))

theorem regulator_pos : 0 < O.regulator := by
  exact mul_pos
    (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero))
    (NumberField.Units.regulator_pos K)

/-! ### The logarithmic lattice of the order -/

open NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem

/-- The image of the units of `O` in the logarithmic space of `K`. -/
def orderUnitLattice : Submodule ℤ (logSpace K) :=
  Submodule.map (logEmbedding K).toIntLinearMap
    O.unitSubgroup.toAddSubgroup.toIntSubmodule

theorem orderUnitLattice_le_unitLattice :
    O.orderUnitLattice ≤ unitLattice K := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨u, Submodule.mem_top, rfl⟩

theorem orderUnitLattice_relIndex :
    O.orderUnitLattice.toAddSubgroup.relIndex
        (unitLattice K).toAddSubgroup = O.unitSubgroup.index := by
  change (O.unitSubgroup.toAddSubgroup.map (logEmbedding K)).relIndex
      ((⊤ : AddSubgroup (Additive ((𝓞 K)ˣ))).map (logEmbedding K)) = _
  rw [AddSubgroup.relIndex_map_map]
  simp only [logEmbedding_ker]
  have ht : NumberField.Units.torsion K ≤ O.unitSubgroup := by
    intro z hz
    have hodd : Odd (Module.finrank ℚ K) := by
      rw [(Fact.out : Module.finrank ℚ K = 3)]
      exact ⟨1, rfl⟩
    have hz' := NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
      hodd ⟨z, hz⟩
    have hzval : z = 1 ∨ z = -1 := by simpa using hz'
    rcases hzval with rfl | rfl
    · exact O.unitSubgroup.one_mem
    · change (-1 : (𝓞 K)ˣ) ∈ O.unitMap.range
      refine ⟨-1, ?_⟩
      ext
      simp [unitMap, toMaximalOrder]
  have ht' : (NumberField.Units.torsion K).toAddSubgroup ≤
      O.unitSubgroup.toAddSubgroup := ht
  rw [sup_eq_left.mpr ht', top_sup_eq]
  rw [AddSubgroup.relIndex_top_right, Subgroup.index_toAddSubgroup]

instance orderUnitLattice_discrete : DiscreteTopology O.orderUnitLattice := by
  rw [← SetLike.isDiscrete_iff_discreteTopology]
  exact (inferInstance : DiscreteTopology (unitLattice K)).isDiscrete.mono
    O.orderUnitLattice_le_unitLattice

theorem orderUnitLattice_span_eq_top :
    Submodule.span ℝ (O.orderUnitLattice : Set (logSpace K)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← unitLattice_span_eq_top (K := K)]
  apply Submodule.span_le.mpr
  intro x hx
  let n := O.orderUnitLattice.toAddSubgroup.relIndex
    (unitLattice K).toAddSubgroup
  have hn : n ≠ 0 := by
    simpa [n, O.orderUnitLattice_relIndex] using
      (Subgroup.FiniteIndex.index_ne_zero :
        O.unitSubgroup.index ≠ 0)
  have hnx : n • x ∈ O.orderUnitLattice.toAddSubgroup :=
    O.orderUnitLattice.toAddSubgroup.nsmul_relIndex_mem hx
  have hspan : (n : ℝ) • x ∈
      Submodule.span ℝ (O.orderUnitLattice : Set (logSpace K)) := by
    apply Submodule.subset_span
    simpa [Nat.cast_smul_eq_nsmul] using hnx
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← one_smul ℝ x, ← inv_mul_cancel₀ hnR, mul_smul]
  exact Submodule.smul_mem _ _ hspan

open scoped Classical in
instance orderUnitLattice_isZLattice :
    IsZLattice ℝ O.orderUnitLattice :=
  ⟨O.orderUnitLattice_span_eq_top⟩

open scoped Classical in
/-- The regulator defined by unit-group index is the covolume of the order's
logarithmic unit lattice. -/
theorem regulator_eq_covolume :
    O.regulator = ZLattice.covolume O.orderUnitLattice := by
  rw [regulator, ← O.orderUnitLattice_relIndex,
    ← ZLattice.covolume_div_covolume_eq_relIndex
      O.orderUnitLattice (unitLattice K) O.orderUnitLattice_le_unitLattice,
    NumberField.Units.regulator, div_mul_cancel₀]
  exact ZLattice.covolume_ne_zero (unitLattice K) MeasureTheory.volume

theorem card_infinitePlaces_eq_three [NumberField.IsTotallyReal K] :
    Fintype.card (InfinitePlace K) = 3 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
    ← NumberField.IsTotallyReal.finrank K,
    (Fact.out : Module.finrank ℚ K = 3)]

theorem unitRank_eq_two [NumberField.IsTotallyReal K]
    (_O : CubicOrder K) : NumberField.Units.rank K = 2 := by
  rw [NumberField.Units.rank, card_infinitePlaces_eq_three]

open scoped Classical in
/-- A rank-two basis of the order's logarithmic unit lattice. -/
def orderUnitBasis [NumberField.IsTotallyReal K] :
    Module.Basis (Fin 2) ℤ O.orderUnitLattice :=
  (IsZLattice.basis O.orderUnitLattice).reindex
    (Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp [card_infinitePlaces_eq_three]))

open scoped Classical in
/-- Representatives in the maximal-order unit group of a logarithmic basis
for the order-unit subgroup. -/
def orderFundUnits [NumberField.IsTotallyReal K] : Fin 2 → (𝓞 K)ˣ :=
  fun i => ((O.orderUnitBasis i).property).choose.toMul

open scoped Classical in
theorem log_orderFundUnits [NumberField.IsTotallyReal K] (i : Fin 2) :
    logEmbedding K (Additive.ofMul (O.orderFundUnits i)) =
      O.orderUnitBasis i := by
  exact ((O.orderUnitBasis i).property).choose_spec.2

open scoped Classical in
/-- Determinant formula for the regulator using the two chosen fundamental
order units. -/
theorem regulator_eq_abs_det [NumberField.IsTotallyReal K] :
    O.regulator = |(Matrix.of fun i j : Fin 2 =>
      logEmbedding K (Additive.ofMul (O.orderFundUnits i))
        (((finCongr O.unitRank_eq_two.symm).trans
          (NumberField.Units.equivFinRank K)) j)).det| := by
  rw [O.regulator_eq_covolume]
  let e : Fin 2 ≃ {w : InfinitePlace K // w ≠ w₀} :=
    (finCongr O.unitRank_eq_two.symm).trans
      (NumberField.Units.equivFinRank K)
  let b := O.orderUnitBasis.reindex e
  rw [ZLattice.covolume_eq_det O.orderUnitLattice b]
  apply congrArg abs
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    logEmbedding K (Additive.ofMul (O.orderFundUnits i)) (e j)
  calc
    (Matrix.of (Subtype.val ∘ (b : _ → O.orderUnitLattice))).det =
        (Matrix.reindex e e M).det := by
      apply congrArg Matrix.det
      ext i j
      simp only [Matrix.of_apply, Function.comp_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply, M, b, Module.Basis.coe_reindex,
        Equiv.apply_symm_apply]
      rw [log_orderFundUnits]
    _ = M.det := Matrix.det_reindex_self e M

/-! ### Regulators of explicit fundamental units -/

open NumberField

theorem degree_odd : Odd (Module.finrank ℚ K) := by
  have hdeg : Module.finrank ℚ K = 3 := Fact.out
  rw [hdeg]
  exact ⟨1, rfl⟩

/-- In odd degree the only roots of unity are `1` and `-1`; both belong to
every order. -/
theorem torsion_le_unitSubgroup :
    NumberField.Units.torsion K ≤ O.unitSubgroup := by
  intro z hz
  have hz' := NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
    (degree_odd (K := K)) ⟨z, hz⟩
  have hzval : z = 1 ∨ z = -1 := by simpa using hz'
  rcases hzval with hzval | hzval
  · rw [hzval]
    exact O.unitSubgroup.one_mem
  · rw [hzval]
    change (-1 : (𝓞 K)ˣ) ∈ O.unitMap.range
    refine ⟨-1, ?_⟩
    ext
    simp [unitMap, toMaximalOrder]

theorem unitSubgroup_sup_torsion :
    O.unitSubgroup ⊔ NumberField.Units.torsion K = O.unitSubgroup :=
  sup_eq_left.mpr O.torsion_le_unitSubgroup

/-- A family of order units, regarded as maximal-order units. -/
def mapUnitFamily
    (u : Fin (NumberField.Units.rank K) → O.carrierˣ) :
    Fin (NumberField.Units.rank K) → (𝓞 K)ˣ :=
  fun i => O.unitMap (u i)

/-- A family is fundamental when it generates every order unit modulo
torsion. -/
def IsFundamentalFamily
    (u : Fin (NumberField.Units.rank K) → O.carrierˣ) : Prop :=
  Subgroup.closure (Set.range (O.mapUnitFamily u)) ⊔
      NumberField.Units.torsion K = O.unitSubgroup

/-- The regulator of a fundamental family, divided by the field regulator,
is the index of the order-unit subgroup. -/
theorem regOfFamily_div_fieldRegulator
    (u : Fin (NumberField.Units.rank K) → O.carrierˣ)
    (hu : O.IsFundamentalFamily u) :
    NumberField.Units.regOfFamily (O.mapUnitFamily u) /
        NumberField.Units.regulator K = O.unitSubgroup.index := by
  rw [NumberField.Units.regOfFamily_div_regulator, hu]

/-- A fundamental family computes the regulator of the order.  This is the
bridge used when the paper identifies explicit generators in Proposition
3.4. -/
theorem regOfFamily_eq_regulator
    (u : Fin (NumberField.Units.rank K) → O.carrierˣ)
    (hu : O.IsFundamentalFamily u) :
    NumberField.Units.regOfFamily (O.mapUnitFamily u) = O.regulator := by
  rw [regulator, ← div_eq_iff (NumberField.Units.regulator_ne_zero K)]
  exact O.regOfFamily_div_fieldRegulator u hu

/-! ### A short order unit -/

open scoped Classical in
noncomputable def pairPlace [NumberField.IsTotallyReal K] :
    Fin 2 ≃ {w : InfinitePlace K // w ≠ w₀} :=
  (finCongr O.unitRank_eq_two.symm).trans
    (NumberField.Units.equivFinRank K)

open scoped Classical in
noncomputable def fundLog [NumberField.IsTotallyReal K] (i j : Fin 2) : ℝ :=
  Real.log ((O.pairPlace j).val (O.orderFundUnits i))

open scoped Classical in
lemma regulator_eq_fundLog_det [NumberField.IsTotallyReal K] :
    O.regulator =
      |(Matrix.of fun i j : Fin 2 => O.fundLog i j).det| := by
  simpa [fundLog, pairPlace, NumberField.IsTotallyReal.mult_eq] using
    O.regulator_eq_abs_det

open scoped Classical in
theorem exists_short_vector [NumberField.IsTotallyReal K] :
    ∃ p : ℤ × ℤ, BinaryQuadratic.Primitive p ∧
      let x := (p.1 : ℝ) * O.fundLog 0 0 +
        (p.2 : ℝ) * O.fundLog 1 0
      let y := (p.1 : ℝ) * O.fundLog 0 1 +
        (p.2 : ℝ) * O.fundLog 1 1
      0 < 2 * (x ^ 2 + x * y + y ^ 2) ∧
        2 * (x ^ 2 + x * y + y ^ 2) ≤ 2 * O.regulator := by
  let a := O.fundLog 0 0
  let b := O.fundLog 0 1
  let c := O.fundLog 1 0
  let d := O.fundLog 1 1
  let A := 2 * (a ^ 2 + a * b + b ^ 2)
  let B := 2 * a * c + a * d + b * c + 2 * b * d
  let C := 2 * (c ^ 2 + c * d + d ^ 2)
  have hreg : O.regulator = |a * d - b * c| := by
    rw [O.regulator_eq_fundLog_det]
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    rfl
  have hdet : A * C - B ^ 2 = 3 * (a * d - b * c) ^ 2 := by
    dsimp [A, B, C]
    ring
  have hminor : a * d - b * c ≠ 0 := by
    intro h
    have hpos := O.regulator_pos
    rw [hreg, h, abs_zero] at hpos
    exact lt_irrefl 0 hpos
  have hA : 0 < A := by
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      have hminor' : a * d - b * c = 0 := by
        rw [h.1, h.2]
        ring
      exact hminor hminor'
    dsimp [A]
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (a + b)]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg (a + b)]
  have hdetpos : 0 < A * C - B ^ 2 := by
    rw [hdet]
    positivity
  obtain ⟨p, hpprim, hpq, hpbound⟩ :=
    BinaryQuadratic.exists_primitive_q_le hA hdetpos
  refine ⟨p, hpprim, ?_⟩
  have hqform :
      BinaryQuadratic.q A B C p =
        2 * (((p.1 : ℝ) * a + (p.2 : ℝ) * c) ^ 2 +
          ((p.1 : ℝ) * a + (p.2 : ℝ) * c) *
            ((p.1 : ℝ) * b + (p.2 : ℝ) * d) +
          ((p.1 : ℝ) * b + (p.2 : ℝ) * d) ^ 2) := by
    dsimp [BinaryQuadratic.q, A, B, C]
    ring
  dsimp only
  constructor
  · simpa [a, b, c, d, hqform] using hpq
  · rw [hqform] at hpbound
    have hsqrt : Real.sqrt ((4 / 3 : ℝ) * (A * C - B ^ 2)) =
        2 * |a * d - b * c| := by
      rw [hdet]
      have hsquare : (4 / 3 : ℝ) * (3 * (a * d - b * c) ^ 2) =
          (2 * |a * d - b * c|) ^ 2 := by
        nlinarith [sq_abs (a * d - b * c)]
      rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity
    rw [hsqrt, ← hreg] at hpbound
    simpa [a, b, c, d] using hpbound

open scoped Classical in
lemma orderFundUnits_mem_unitSubgroup [NumberField.IsTotallyReal K]
    (i : Fin 2) : O.orderFundUnits i ∈ O.unitSubgroup := by
  exact ((O.orderUnitBasis i).property).choose_spec.1

open scoped Classical in
theorem exists_short_unit [NumberField.IsTotallyReal K] :
    ∃ u : (𝓞 K)ˣ, u ∈ O.unitSubgroup ∧
      let x := Real.log ((O.pairPlace 0).val u)
      let y := Real.log ((O.pairPlace 1).val u)
      0 < 2 * (x ^ 2 + x * y + y ^ 2) ∧
        2 * (x ^ 2 + x * y + y ^ 2) ≤ 2 * O.regulator := by
  obtain ⟨p, hpprim, hp, hbound⟩ := O.exists_short_vector
  let u := O.orderFundUnits 0 ^ p.1 * O.orderFundUnits 1 ^ p.2
  refine ⟨u, ?_, ?_⟩
  · exact O.unitSubgroup.mul_mem
      (O.unitSubgroup.zpow_mem (O.orderFundUnits_mem_unitSubgroup 0) p.1)
      (O.unitSubgroup.zpow_mem (O.orderFundUnits_mem_unitSubgroup 1) p.2)
  have hlog (j : Fin 2) :
      Real.log ((O.pairPlace j).val u) =
        (p.1 : ℝ) * O.fundLog 0 j +
          (p.2 : ℝ) * O.fundLog 1 j := by
    have h := congrFun (show
      logEmbedding K (Additive.ofMul u) =
        p.1 • logEmbedding K (Additive.ofMul (O.orderFundUnits 0)) +
        p.2 • logEmbedding K (Additive.ofMul (O.orderFundUnits 1)) by
          simp [u]) (O.pairPlace j)
    simpa [fundLog, NumberField.IsTotallyReal.mult_eq] using h
  dsimp only
  rw [hlog 0, hlog 1]
  exact ⟨hp, hbound⟩

/-! ### Cubic conjugates and power-basis discriminants -/

open scoped Classical in
noncomputable def threePlace [NumberField.IsTotallyReal K] :
    Fin 3 ≃ InfinitePlace K :=
  (finSuccEquiv 2).trans
    ((Equiv.optionSubtype w₀).symm O.pairPlace).val

open scoped Classical in
noncomputable def placeAlgHomEquiv [NumberField.IsTotallyReal K] :
    InfinitePlace K ≃ (K →ₐ[ℚ] ℂ) where
  toFun w := w.embedding.toRatAlgHom
  invFun φ := InfinitePlace.mk φ.toRingHom
  left_inv w := InfinitePlace.mk_embedding w
  right_inv φ := by
    apply AlgHom.ext
    intro x
    exact RingHom.congr_fun (InfinitePlace.embedding_mk_eq_of_isReal
      (NumberField.IsTotallyReal.complexEmbedding_isReal φ.toRingHom)) x

open scoped Classical in
noncomputable def realConjugate [NumberField.IsTotallyReal K]
    (x : K) (i : Fin 3) : ℝ :=
  InfinitePlace.embedding_of_isReal
    (NumberField.IsTotallyReal.isReal (O.threePlace i)) x

lemma map_discr_to_rat (b : Fin 3 → 𝓞 K) :
    algebraMap ℤ ℚ (Algebra.discr ℤ b) =
      Algebra.discr ℚ (fun i => (b i : K)) := by
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  simpa only [map_mul] using
    (Algebra.trace_localization (Rₘ := ℚ) (Sₘ := K) ℤ
      (nonZeroDivisors ℤ) ((b i) * (b j))).symm

open scoped Classical in
lemma power_discriminant_eq_conjugates [NumberField.IsTotallyReal K]
    (u : (𝓞 K)ˣ) :
    ((Algebra.discr ℤ
        (fun i : Fin 3 => (u : 𝓞 K) ^ (i : ℕ))).natAbs : ℝ) =
      ((O.realConjugate (u : K) 0 - O.realConjugate (u : K) 1) *
       (O.realConjugate (u : K) 0 - O.realConjugate (u : K) 2) *
       (O.realConjugate (u : K) 1 - O.realConjugate (u : K) 2)) ^ 2 := by
  let x : K := (u : K)
  let e : Fin 3 ≃ (K →ₐ[ℚ] ℂ) :=
    O.threePlace.trans (placeAlgHomEquiv (K := K))
  have hdiscC := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two
    ℚ ℂ (fun i : Fin 3 => x ^ (i : ℕ)) e
  have hentry (i j : Fin 3) :
      Algebra.embeddingsMatrixReindex ℚ ℂ
        (fun i : Fin 3 => x ^ (i : ℕ)) e i j =
      ((O.realConjugate x j : ℝ) : ℂ) ^ (i : ℕ) := by
    simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply,
      Matrix.submatrix_apply, Algebra.embeddingsMatrix_apply, map_pow]
    congr 1
    change (O.threePlace j).embedding x = _
    exact (InfinitePlace.embedding_of_isReal_apply
      (NumberField.IsTotallyReal.isReal (O.threePlace j)) x).symm
  have hdet :
      (Algebra.embeddingsMatrixReindex ℚ ℂ
        (fun i : Fin 3 => x ^ (i : ℕ)) e).det =
      -(((O.realConjugate x 0 - O.realConjugate x 1) *
       (O.realConjugate x 0 - O.realConjugate x 2) *
       (O.realConjugate x 1 - O.realConjugate x 2) : ℝ) : ℂ) := by
    rw [Matrix.det_fin_three]
    simp_rw [hentry]
    norm_num
    push_cast
    ring
  have hdiscQ := map_discr_to_rat
    (fun i : Fin 3 => (u : 𝓞 K) ^ (i : ℕ))
  have hdiscR :
      ((Algebra.discr ℤ
        (fun i : Fin 3 => (u : 𝓞 K) ^ (i : ℕ)) : ℤ) : ℝ) =
      ((O.realConjugate x 0 - O.realConjugate x 1) *
       (O.realConjugate x 0 - O.realConjugate x 2) *
       (O.realConjugate x 1 - O.realConjugate x 2)) ^ 2 := by
    apply Complex.ofReal_injective
    have hright :
        (((((O.realConjugate x 0 - O.realConjugate x 1) *
          (O.realConjugate x 0 - O.realConjugate x 2) *
          (O.realConjugate x 1 - O.realConjugate x 2)) ^ 2 : ℝ) : ℂ)) =
          (Algebra.embeddingsMatrixReindex ℚ ℂ
            (fun i : Fin 3 => x ^ (i : ℕ)) e).det ^ 2 := by
      rw [hdet]
      push_cast
      ring
    rw [hright, ← hdiscC]
    push_cast
    have hdiscQC := congrArg (algebraMap ℚ ℂ) hdiscQ
    simpa [x, map_pow] using hdiscQC
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs,
    abs_of_nonneg]
  · simpa [x] using hdiscR
  · rw [hdiscR]
    positivity

open scoped Classical in
lemma abs_realConjugate [NumberField.IsTotallyReal K]
    (u : (𝓞 K)ˣ) (i : Fin 3) :
    |O.realConjugate (u : K) i| = O.threePlace i (u : K) := by
  simpa [realConjugate, Real.norm_eq_abs] using
    (InfinitePlace.norm_embedding_of_isReal
      (NumberField.IsTotallyReal.isReal (O.threePlace i)) (u : K))

open scoped Classical in
lemma abs_prod_realConjugates [NumberField.IsTotallyReal K]
    (u : (𝓞 K)ˣ) :
    |O.realConjugate (u : K) 0 * O.realConjugate (u : K) 1 *
      O.realConjugate (u : K) 2| = 1 := by
  rw [abs_mul, abs_mul, O.abs_realConjugate u 0,
    O.abs_realConjugate u 1, O.abs_realConjugate u 2]
  rw [← Fin.prod_univ_three (fun i : Fin 3 =>
    O.threePlace i (u : K))]
  rw [Equiv.prod_comp O.threePlace (fun w => w (u : K))]
  calc
    ∏ w : InfinitePlace K, w (u : K) =
        ∏ w : InfinitePlace K, w (u : K) ^ w.mult := by
          simp [NumberField.IsTotallyReal.mult_eq]
    _ = ((|Algebra.norm ℚ (u : K)| : ℚ) : ℝ) :=
      InfinitePlace.prod_eq_abs_norm (u : K)
    _ = 1 := by
      norm_cast
      exact NumberField.Units.norm K u

open scoped Classical in
lemma logs_three_eq_short_form [NumberField.IsTotallyReal K]
    (u : (𝓞 K)ˣ) :
    Real.log |O.realConjugate (u : K) 0| ^ 2 +
      Real.log |O.realConjugate (u : K) 1| ^ 2 +
      Real.log |O.realConjugate (u : K) 2| ^ 2 =
    2 * (Real.log ((O.pairPlace 0).val u) ^ 2 +
      Real.log ((O.pairPlace 0).val u) *
        Real.log ((O.pairPlace 1).val u) +
      Real.log ((O.pairPlace 1).val u) ^ 2) := by
  have h0 : O.threePlace 0 = w₀ := by
    simp [threePlace]
  have h1 : O.threePlace 1 = (O.pairPlace 0).val := by
    rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) by rfl]
    simp only [threePlace, Equiv.trans_apply, finSuccEquiv_succ,
      Equiv.optionSubtype_symm_apply_apply_some]
  have h2 : O.threePlace 2 = (O.pairPlace 1).val := by
    rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) by rfl]
    simp only [threePlace, Equiv.trans_apply, finSuccEquiv_succ,
      Equiv.optionSubtype_symm_apply_apply_some]
  have habs (i : Fin 3) :
      |O.realConjugate (u : K) i| = O.threePlace i (u : K) :=
    O.abs_realConjugate u i
  have hsum := NumberField.Units.sum_mult_mul_log u
  simp only [NumberField.IsTotallyReal.mult_eq, Nat.cast_one, one_mul] at hsum
  rw [← Equiv.sum_comp O.threePlace] at hsum
  rw [Fin.sum_univ_three, h0, h1, h2] at hsum
  simp_rw [habs]
  rw [h0, h1, h2]
  have hfirst : Real.log (w₀ (u : K)) =
      -(Real.log ((O.pairPlace 0).val (u : K)) +
        Real.log ((O.pairPlace 1).val (u : K))) := by
    linarith [hsum]
  rw [hfirst]
  ring

open scoped Classical in
lemma short_unit_minpoly_degree [NumberField.IsTotallyReal K]
    (u : (𝓞 K)ˣ)
    (hpos : 0 < 2 *
      (Real.log ((O.pairPlace 0).val u) ^ 2 +
       Real.log ((O.pairPlace 0).val u) *
        Real.log ((O.pairPlace 1).val u) +
       Real.log ((O.pairPlace 1).val u) ^ 2)) :
    (minpoly ℚ (algebraMap (𝓞 K) K (u : 𝓞 K))).natDegree = 3 := by
  let x : K := algebraMap (𝓞 K) K (u : 𝓞 K)
  have hdiv : (minpoly ℚ x).natDegree ∣ 3 := by
    have h := minpoly.degree_dvd (IsIntegral.of_finite ℚ x)
    simpa [x, (Fact.out : Module.finrank ℚ K = 3)] using h
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hdeg | hdeg
  · exfalso
    have hxrat : x ∈ (algebraMap ℚ K).range :=
      minpoly.natDegree_eq_one_iff.mp hdeg
    obtain ⟨q, hq⟩ := hxrat
    have hplace (w : InfinitePlace K) : w (u : K) = ‖q‖ := by
      rw [show w (u : K) = w x by rfl, ← hq]
      exact w.map_ratCast q
    have hsum := NumberField.Units.sum_mult_mul_log u
    simp only [NumberField.IsTotallyReal.mult_eq, Nat.cast_one, one_mul] at hsum
    simp_rw [hplace] at hsum
    rw [Finset.sum_const, Finset.card_univ,
      card_infinitePlaces_eq_three (K := K), nsmul_eq_mul] at hsum
    have hlog : Real.log ‖q‖ = 0 :=
      (mul_eq_zero.mp hsum).resolve_left (by norm_num)
    rw [hplace, hplace, hlog] at hpos
    norm_num at hpos
  · exact hdeg

open scoped Classical in
lemma discriminant_le_power_discriminant
    (v : O.carrierˣ)
    (hdeg : (minpoly ℚ
      (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K))).natDegree = 3) :
    O.discriminant ≤
      (Algebra.discr ℤ (fun i : Fin 3 =>
        (((v : O.carrier) ^ (i : ℕ) : O.carrier) : 𝓞 K))).natAbs := by
  let g : Fin 3 → O.carrier := fun i => (v : O.carrier) ^ (i : ℕ)
  let b : Fin 3 → 𝓞 K := fun i => (g i : 𝓞 K)
  let P := O.basis.toMatrix g
  have hfamily :
      Matrix.vecMul (fun i => (O.basis i : 𝓞 K))
          (P.map (algebraMap ℤ (𝓞 K))) = b := by
    dsimp only [P, b]
    have h := O.basis.toMatrix_map_vecMul g
    funext i
    have hi := congrFun h i
    simpa [Matrix.vecMul, dotProduct, Algebra.smul_def] using
      congrArg (fun z : O.carrier => (z : 𝓞 K)) hi
  have hsigned :
      Algebra.discr ℤ b = P.det ^ 2 * O.signedDiscriminant := by
    have hdisc := Algebra.discr_of_matrix_vecMul
      (fun i => (O.basis i : 𝓞 K)) P
    rw [hfamily] at hdisc
    simpa only [signedDiscriminant] using hdisc
  have hbK : (fun i => (b i : K)) =
      (fun i : Fin 3 =>
        algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) ^ (i : ℕ)) := by
    funext i
    rfl
  have hbne : Algebra.discr ℤ b ≠ 0 := by
    intro hbzero
    have hmap := map_discr_to_rat b
    rw [hbzero, map_zero, hbK] at hmap
    have hne : Algebra.discr ℚ
        (fun i : Fin 3 =>
          algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) ^ (i : ℕ)) ≠ 0 := by
      have hxint : IsIntegral ℚ
          (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)) :=
        IsIntegral.of_finite ℚ _
      have hprim : ℚ⟮algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)⟯ = ⊤ := by
        apply (Field.primitive_element_iff_minpoly_natDegree_eq ℚ _).2
        exact hdeg.trans (Fact.out : Module.finrank ℚ K = 3).symm
      have hadj : Algebra.adjoin ℚ
          {algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)} = ⊤ := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          hxint.isAlgebraic]
        exact congrArg IntermediateField.toSubalgebra hprim
      let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hxint hadj
      have hpbdim : pb.dim = 3 := by simpa [pb] using hdeg
      let bas : Module.Basis (Fin 3) ℚ K :=
        pb.basis.reindex (finCongr hpbdim)
      have hbasi (i : Fin 3) : bas i =
          algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) ^ (i : ℕ) := by
        change (pb.basis.reindex (finCongr hpbdim)) i = _
        rw [Module.Basis.coe_reindex]
        simp only [Function.comp_apply]
        rw [PowerBasis.basis_eq_pow]
        rw [show pb.gen =
          algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) by
            exact PowerBasis.ofAdjoinEqTop_gen hxint hadj]
        have hi : (((finCongr hpbdim).symm i : Fin pb.dim) : ℕ) =
            (i : ℕ) := by rfl
        rw [hi]
      have hf : (fun i : Fin 3 =>
          algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) ^ (i : ℕ)) =
          (bas : Fin 3 → K) := by
        funext i
        exact (hbasi i).symm
      rw [hf]
      exact Algebra.discr_not_zero_of_basis ℚ bas
    exact hne hmap.symm
  have hP : P.det ≠ 0 := by
    intro hPzero
    apply hbne
    rw [hsigned, hPzero]
    norm_num
  have habs : (Algebra.discr ℤ b).natAbs =
      P.det.natAbs ^ 2 * O.discriminant := by
    rw [hsigned, Int.natAbs_mul, Int.natAbs_pow]
    rfl
  change O.discriminant ≤ (Algebra.discr ℤ b).natAbs
  rw [habs]
  exact Nat.le_mul_of_pos_left O.discriminant (by positivity)

lemma discriminant_ge_four [NumberField.IsTotallyReal K] :
    4 ≤ O.discriminant := by
  have hreal : (4 : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
    have h := NumberField.abs_discr_ge' (K := K)
    rw [(Fact.out : Module.finrank ℚ K = 3),
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h
    norm_num at h ⊢
    exact le_trans (by norm_num) h
  have hz : (4 : ℤ) ≤ |NumberField.discr K| := by
    exact_mod_cast hreal
  rw [← Int.natCast_natAbs] at hz
  have hn : 4 ≤ (NumberField.discr K).natAbs := by
    exact_mod_cast hz
  rw [O.discriminant_eq_index_sq_mul]
  calc
    4 ≤ (NumberField.discr K).natAbs := hn
    _ ≤ O.additiveIndex ^ 2 * (NumberField.discr K).natAbs := by
      have hi : 0 < O.additiveIndex :=
        Nat.pos_of_ne_zero O.additiveIndex_ne_zero
      have hi2 : 1 ≤ O.additiveIndex ^ 2 := by nlinarith
      simpa using
        Nat.mul_le_mul_right (NumberField.discr K).natAbs hi2

/-! ### Analytic estimates for cubic conjugates -/

lemma cubic_log_bound_sorted {a b c d : ℝ}
    (hd : 4 ≤ d)
    (hddisc : d ≤ ((a - b) * (a - c) * (b - c)) ^ 2)
    (hprod : |a * b * c| = 1)
    (hab : |b| ≤ |a|) (hbc : |c| ≤ |b|) :
    Real.log (d / 4) ≤ 2 * Real.sqrt 2 *
      Real.sqrt (Real.log |a| ^ 2 + Real.log |b| ^ 2 +
        Real.log |c| ^ 2) := by
  have habc : a * b * c ≠ 0 := by
    intro h
    rw [h, abs_zero] at hprod
    norm_num at hprod
  have ha : a ≠ 0 := by
    intro h
    apply habc
    rw [h, zero_mul, zero_mul]
  have hb : b ≠ 0 := by
    intro h
    apply habc
    rw [h, mul_zero, zero_mul]
  have hc : c ≠ 0 := by
    intro h
    apply habc
    rw [h, mul_zero]
  let v := b / a
  let w := c / b
  have hvabs : |v| ≤ 1 := by
    dsimp [v]
    rw [abs_div, div_le_one (abs_pos.mpr ha)]
    exact hab
  have hwabs : |w| ≤ 1 := by
    dsimp [w]
    rw [abs_div, div_le_one (abs_pos.mpr hb)]
    exact hbc
  have hv : v ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hvabs
  have hw : w ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hwabs
  obtain ⟨hfac0, hfac2⟩ := cubic_factor_nonneg_le_two hv hw
  let f := (1 - v) * (1 - w) * (1 - v * w)
  have hdiff : (a - b) * (a - c) * (b - c) = a ^ 2 * b * f := by
    dsimp [f, v, w]
    field_simp
  have hf2 : f ^ 2 ≤ 4 := by nlinarith
  have hdiffupper :
      ((a - b) * (a - c) * (b - c)) ^ 2 ≤
        |a| ^ 4 * |b| ^ 2 * 4 := by
    rw [hdiff]
    have habs : (a ^ 2 * b * f) ^ 2 =
        |a| ^ 4 * |b| ^ 2 * f ^ 2 := by
      rw [(show Even 4 by exact ⟨2, rfl⟩).pow_abs a, sq_abs b]
      ring
    rw [habs]
    gcongr
  have hd4 : d / 4 ≤ |a| ^ 4 * |b| ^ 2 := by
    nlinarith [hddisc.trans hdiffupper]
  have hdpos : 0 < d / 4 := by positivity
  have habpos : 0 < |a| ^ 4 * |b| ^ 2 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hdpos habpos hd4
  have hlogexpand : Real.log (|a| ^ 4 * |b| ^ 2) =
      4 * Real.log |a| + 2 * Real.log |b| := by
    rw [Real.log_mul (pow_ne_zero _ (abs_ne_zero.mpr ha))
      (pow_ne_zero _ (abs_ne_zero.mpr hb)), Real.log_pow, Real.log_pow]
    norm_num
  rw [hlogexpand] at hlog
  let x := Real.log |a|
  let y := Real.log |b|
  let z := Real.log |c|
  have hsum : x + y + z = 0 := by
    dsimp [x, y, z]
    rw [← Real.log_mul (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb),
      ← Real.log_mul (mul_ne_zero (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb))
        (abs_ne_zero.mpr hc), ← abs_mul, ← abs_mul, hprod, Real.log_one]
  have hxy : y ≤ x := by
    dsimp [x, y]
    exact Real.strictMonoOn_log.monotoneOn
      (abs_pos.mpr hb) (abs_pos.mpr ha) hab
  have hyz : z ≤ y := by
    dsimp [y, z]
    exact Real.strictMonoOn_log.monotoneOn
      (abs_pos.mpr hc) (abs_pos.mpr hb) hbc
  have hlin0 : 0 ≤ 2 * x + y := by linarith
  let Q := x ^ 2 + y ^ 2 + z ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsq : (2 * x + y) ^ 2 ≤ 2 * Q := by
    dsimp [Q]
    nlinarith [sq_nonneg y]
  have hsqrt : 2 * x + y ≤ Real.sqrt 2 * Real.sqrt Q := by
    have hs2 : 0 ≤ Real.sqrt 2 * Real.sqrt Q :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ hlin0 hs2).mp
    calc
      (2 * x + y) ^ 2 ≤ 2 * Q := hsq
      _ = (Real.sqrt 2 * Real.sqrt Q) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt hQ]
  calc
    Real.log (d / 4) ≤ 2 * (2 * x + y) := by
      dsimp [x, y]
      linarith [hlog]
    _ ≤ 2 * (Real.sqrt 2 * Real.sqrt Q) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = 2 * Real.sqrt 2 *
        Real.sqrt (Real.log |a| ^ 2 + Real.log |b| ^ 2 +
          Real.log |c| ^ 2) := by
      dsimp [Q, x, y, z]
      ring

lemma cubic_log_bound {a b c d : ℝ}
    (hd : 4 ≤ d)
    (hddisc : d ≤ ((a - b) * (a - c) * (b - c)) ^ 2)
    (hprod : |a * b * c| = 1) :
    Real.log (d / 4) ≤ 2 * Real.sqrt 2 *
      Real.sqrt (Real.log |a| ^ 2 + Real.log |b| ^ 2 +
        Real.log |c| ^ 2) := by
  by_cases hab : |b| ≤ |a|
  · by_cases hbc : |c| ≤ |b|
    · exact cubic_log_bound_sorted hd hddisc hprod hab hbc
    · have hcb : |b| ≤ |c| := le_of_not_ge hbc
      by_cases hca : |c| ≤ |a|
      · have hdisc' : d ≤ ((a - c) * (a - b) * (c - b)) ^ 2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |a * c * b| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hca hcb
        convert h using 1 <;> ring
      · have hac : |a| ≤ |c| := le_of_not_ge hca
        have hdisc' : d ≤ ((c - a) * (c - b) * (a - b)) ^ 2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |c * a * b| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hac hab
        convert h using 1 <;> ring
  · have hab' : |a| ≤ |b| := le_of_not_ge hab
    by_cases hac : |c| ≤ |a|
    · have hdisc' : d ≤ ((b - a) * (b - c) * (a - c)) ^ 2 := by
        convert hddisc using 1 <;> ring
      have hprod' : |b * a * c| = 1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      have h := cubic_log_bound_sorted hd hdisc' hprod' hab' hac
      convert h using 1 <;> ring
    · have hac' : |a| ≤ |c| := le_of_not_ge hac
      by_cases hcb : |c| ≤ |b|
      · have hdisc' : d ≤ ((b - c) * (b - a) * (c - a)) ^ 2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |b * c * a| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hcb hac'
        convert h using 1 <;> ring
      · have hbc : |b| ≤ |c| := le_of_not_ge hcb
        have hdisc' : d ≤ ((c - b) * (c - a) * (b - a)) ^ 2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |c * b * a| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hbc hab'
        convert h using 1 <;> ring

/-- **Cusick's inequality for cubic orders.** For every order `O` in a
totally real cubic number field,

`(1 / 16) * log(discriminant(O) / 4)^2 ≤ regulator(O)`.

This is Theorem 2.4 of arXiv:2502.12754. Cusick stated the inequality for
totally real cubic fields (equivalently, their rings of integers); footnote 3
of the cited paper records that the proof applies verbatim to general,
possibly nonmaximal, orders. -/
theorem regulator_lower_bound [NumberField.IsTotallyReal K] :
    (1 / 16 : ℝ) *
        Real.log ((O.discriminant : ℝ) / 4) ^ 2 ≤ O.regulator := by
  classical
  obtain ⟨u, huO, hshortpos, hshort⟩ := O.exists_short_unit
  change u ∈ O.unitMap.range at huO
  obtain ⟨v, hv⟩ := huO
  have hdegU := O.short_unit_minpoly_degree u hshortpos
  have hdegV :
      (minpoly ℚ
        (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K))).natDegree = 3 := by
    have huv :
        algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) = (u : K) := by
      have hval := congrArg Units.val hv
      exact congrArg (algebraMap (𝓞 K) K) hval
    rw [huv]
    exact hdegU
  have hdiscOrder := O.discriminant_le_power_discriminant v hdegV
  have hpowEq := O.power_discriminant_eq_conjugates u
  have hpowsame :
      (Algebra.discr ℤ (fun i : Fin 3 =>
        (((v : O.carrier) ^ (i : ℕ) : O.carrier) : 𝓞 K))).natAbs =
      (Algebra.discr ℤ
        (fun i : Fin 3 => (u : 𝓞 K) ^ (i : ℕ))).natAbs := by
    congr 1
    congr 1
    funext i
    have hval := congrArg Units.val hv
    exact congrArg (fun z : 𝓞 K => z ^ (i : ℕ)) hval
  rw [hpowsame] at hdiscOrder
  have hdiscReal :
      (O.discriminant : ℝ) ≤
      ((O.realConjugate (u : K) 0 - O.realConjugate (u : K) 1) *
       (O.realConjugate (u : K) 0 - O.realConjugate (u : K) 2) *
       (O.realConjugate (u : K) 1 - O.realConjugate (u : K) 2)) ^ 2 := by
    rw [← hpowEq]
    exact_mod_cast hdiscOrder
  have hlog := cubic_log_bound
    (d := (O.discriminant : ℝ))
    (a := O.realConjugate (u : K) 0)
    (b := O.realConjugate (u : K) 1)
    (c := O.realConjugate (u : K) 2)
    (by exact_mod_cast O.discriminant_ge_four) hdiscReal
    (O.abs_prod_realConjugates u)
  have hlogs := O.logs_three_eq_short_form u
  rw [hlogs] at hlog
  have hsqrtQ :
      Real.sqrt (2 * (Real.log ((O.pairPlace 0).val u) ^ 2 +
       Real.log ((O.pairPlace 0).val u) *
        Real.log ((O.pairPlace 1).val u) +
       Real.log ((O.pairPlace 1).val u) ^ 2)) ≤
        Real.sqrt (2 * O.regulator) :=
    Real.sqrt_le_sqrt hshort
  have hlogR :
      Real.log ((O.discriminant : ℝ) / 4) ≤
        4 * Real.sqrt O.regulator := by
    calc
      Real.log ((O.discriminant : ℝ) / 4) ≤
          2 * Real.sqrt 2 * Real.sqrt
            (2 * (Real.log ((O.pairPlace 0).val u) ^ 2 +
             Real.log ((O.pairPlace 0).val u) *
              Real.log ((O.pairPlace 1).val u) +
             Real.log ((O.pairPlace 1).val u) ^ 2)) := hlog
      _ ≤ 2 * Real.sqrt 2 * Real.sqrt (2 * O.regulator) := by
        gcongr
      _ = 4 * Real.sqrt O.regulator := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        calc
          2 * √2 * (√2 * √(O.regulator)) =
              2 * (√2 * √2) * √(O.regulator) := by ring
          _ = 4 * √(O.regulator) := by
            rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
            ring
  have hlognonneg :
      0 ≤ Real.log ((O.discriminant : ℝ) / 4) := by
    apply Real.log_nonneg
    have hfour : (4 : ℝ) ≤ (O.discriminant : ℝ) := by
      exact_mod_cast O.discriminant_ge_four
    exact (one_le_div (by norm_num : (0 : ℝ) < 4)).2 hfour
  have hsquare :
      Real.log ((O.discriminant : ℝ) / 4) ^ 2 ≤
        16 * O.regulator := by
    have hR : 0 ≤ O.regulator := O.regulator_nonneg
    have hsqrtR := Real.sq_sqrt hR
    nlinarith [sq_nonneg (4 * Real.sqrt O.regulator -
      Real.log ((O.discriminant : ℝ) / 4))]
  nlinarith

end CubicOrder

end Cusick
