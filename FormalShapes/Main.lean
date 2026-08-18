import External.BananaDensity
import External.CusickRegulator
import SageCalculations
import Mathlib.Algebra.Group.Subgroup.Finsupp
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Real.Sign
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.PowModTotient
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sequences

/-!
# Density of shapes of periodic tori in the cubic case

This is the main formalization of Nguyen-Thi Dang, Nihar Gargava, and
Jialun Li, *Density of shapes of periodic tori in the cubic case*.

The file follows the rendered preprint from its background definitions,
through the cubic-order and suborder constructions, to the density argument.
The only separate modules are the two cited external inputs and the finite
calculations that the preprint reports as SageMath computations.
-/


/-!
# Foundational dynamics and period-lattice definitions

This section contains the homogeneous spaces, diagonal action, period basis,
shape normalization, and exact matrix period criterion used throughout the
main theorem and the arithmetic period bridge.
-/

noncomputable section

namespace CubicPeriodicTori

/-- The matrix special linear group `SL(n, R)`. -/
abbrev SL (n : ℕ) (R : Type) [CommRing R] :=
  Matrix.SpecialLinearGroup (Fin n) R

abbrev SL2R := SL 2 ℝ
abbrev SL3R := SL 3 ℝ

/-- The copy of `SL(n, ℤ)` inside `SL(n, ℝ)`. -/
def integralSpecialLinear (n : ℕ) : Subgroup (SL n ℝ) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)).range

/-- The moduli space `SL(2, ℝ) / SL(2, ℤ)` of oriented covolume-one lattices. -/
abbrev ShapeSpace := SL2R ⧸ integralSpecialLinear 2

/-- The space `SL(3, ℝ) / SL(3, ℤ)` of unimodular cubic lattices. -/
abbrev CubicLatticeSpace := SL3R ⧸ integralSpecialLinear 3

/-- Additive coordinates on the positive diagonal group, viewed multiplicatively. -/
abbrev FlowParameter := Multiplicative (Fin 2 → ℝ)

/-- The homomorphism
`(u₁, u₂) ↦ diag(exp u₁, exp u₂, exp (-u₁-u₂))` into `SL(3, ℝ)`. -/
def diagonalEmbedding : FlowParameter →* SL3R where
  toFun u :=
    ⟨Matrix.diagonal ![Real.exp (Multiplicative.toAdd u 0),
        Real.exp (Multiplicative.toAdd u 1),
        Real.exp (-(Multiplicative.toAdd u 0 + Multiplicative.toAdd u 1))], by
      simp [Matrix.det_diagonal, Fin.prod_univ_succ, ← Real.exp_add]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := by
    intro u v
    apply Subtype.ext
    change Matrix.diagonal
        ![Real.exp (Multiplicative.toAdd (u * v) 0),
          Real.exp (Multiplicative.toAdd (u * v) 1),
          Real.exp (-(Multiplicative.toAdd (u * v) 0 +
            Multiplicative.toAdd (u * v) 1))] =
      Matrix.diagonal
          ![Real.exp (Multiplicative.toAdd u 0),
            Real.exp (Multiplicative.toAdd u 1),
            Real.exp (-(Multiplicative.toAdd u 0 + Multiplicative.toAdd u 1))] *
        Matrix.diagonal
          ![Real.exp (Multiplicative.toAdd v 0),
            Real.exp (Multiplicative.toAdd v 1),
            Real.exp (-(Multiplicative.toAdd v 0 + Multiplicative.toAdd v 1))]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [Real.exp_add]
    ring

/-- The positive diagonal flow on `SL(3, ℝ) / SL(3, ℤ)`. -/
instance cubicFlowAction : MulAction FlowParameter CubicLatticeSpace :=
  MulAction.compHom CubicLatticeSpace diagonalEmbedding

/-- The subgroup `M < SL(3, ℝ)` of diagonal sign matrices. -/
def signDiagonal : Subgroup SL3R where
  carrier := {g | (∀ i j, i ≠ j → g i j = 0) ∧
    ∀ i, g i i = 1 ∨ g i i = -1}
  one_mem' := by
    constructor
    · intro i j hij
      simp [hij]
    · intro i
      exact Or.inl (by simp)
  mul_mem' := by
    rintro g h ⟨hgdiag, hgsgn⟩ ⟨hhdiag, hhsgn⟩
    have hmul : (↑(g * h) : Matrix (Fin 3) (Fin 3) ℝ) =
        Matrix.diagonal (fun k ↦ g k k * h k k) := by
      rw [Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.IsDiag.diagonal_diag hgdiag,
        ← Matrix.IsDiag.diagonal_diag hhdiag,
        Matrix.diagonal_mul_diagonal]
      simp
    constructor
    · intro i j hij
      rw [hmul]
      exact Matrix.diagonal_apply_ne _ hij
    · intro i
      rcases hgsgn i with hgi | hgi <;> rcases hhsgn i with hhi | hhi
      · left; rw [hmul]; simp [hgi, hhi]
      · right; rw [hmul]; simp [hgi, hhi]
      · right; rw [hmul]; simp [hgi, hhi]
      · left; rw [hmul]; simp [hgi, hhi]
  inv_mem' := by
    rintro g ⟨hgdiag, hgsgn⟩
    have hgg : g * g = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.IsDiag.diagonal_diag hgdiag,
        ← Matrix.IsDiag.diagonal_diag hgdiag,
        Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        rcases hgsgn i with hi | hi <;> simp [hi]
      · simp [hij]
    have hginv : g⁻¹ = g := by
      calc
        g⁻¹ = g⁻¹ * 1 := by simp
        _ = g⁻¹ * (g * g) := by rw [hgg]
        _ = g := by simp
    simpa [hginv] using And.intro hgdiag hgsgn

/-- The space `M \ SL(3, ℝ) / SL(3, ℤ)` of Weyl chambers. -/
abbrev WeylChamberSpace :=
  MulAction.orbitRel.Quotient signDiagonal CubicLatticeSpace

/-- Positive diagonal matrices commute with the diagonal sign subgroup. -/
lemma diagonalEmbedding_commutes_sign
    (u : FlowParameter) (m : signDiagonal) :
    diagonalEmbedding u * (m : SL3R) = (m : SL3R) * diagonalEmbedding u := by
  apply Subtype.ext
  change Matrix.diagonal
      ![Real.exp (Multiplicative.toAdd u 0),
        Real.exp (Multiplicative.toAdd u 1),
        Real.exp (-(Multiplicative.toAdd u 0 + Multiplicative.toAdd u 1))] *
      (m : SL3R) =
    (m : SL3R) * Matrix.diagonal
      ![Real.exp (Multiplicative.toAdd u 0),
        Real.exp (Multiplicative.toAdd u 1),
        Real.exp (-(Multiplicative.toAdd u 0 + Multiplicative.toAdd u 1))]
  rw [← Matrix.IsDiag.diagonal_diag m.property.1,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- Auxiliary fact `flow_smul_sign_smul` used in the proof of the surrounding result from the preprint. -/
lemma flow_smul_sign_smul (u : FlowParameter) (m : signDiagonal)
    (x : CubicLatticeSpace) :
    u • (m • x) = m • (u • x) := by
  change diagonalEmbedding u • ((m : SL3R) • x) =
    (m : SL3R) • (diagonalEmbedding u • x)
  rw [← mul_smul, ← mul_smul, diagonalEmbedding_commutes_sign]

/-- Auxiliary fact `weylSmul_respects` used in the proof of the surrounding result from the preprint. -/
lemma weylSmul_respects (u : FlowParameter) (x y : CubicLatticeSpace)
    (hxy : MulAction.orbitRel signDiagonal CubicLatticeSpace x y) :
    MulAction.orbitRel signDiagonal CubicLatticeSpace (u • x) (u • y) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy ⊢
  obtain ⟨m, rfl⟩ := hxy
  exact ⟨m, (flow_smul_sign_smul u m y).symm⟩

/-- The positive diagonal flow descends to the Weyl chamber space because it
commutes with the sign subgroup `M`. -/
instance weylFlowAction : MulAction FlowParameter WeylChamberSpace where
  smul u q := Quotient.map' (u • ·) (weylSmul_respects u) q
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ x =>
        exact congrArg
          (fun z => (Quotient.mk'' z : WeylChamberSpace))
          (one_smul FlowParameter x)
  mul_smul u v q := by
    induction q using Quotient.inductionOn with
    | _ x =>
        exact congrArg
          (fun z => (Quotient.mk'' z : WeylChamberSpace))
          (mul_smul u v x)

/-- `u` is a logarithmic period of the diagonal orbit through `x`. -/
def IsPeriod (x : WeylChamberSpace) (u : Fin 2 → ℝ) : Prop :=
  Multiplicative.ofAdd u • x = x

/-- This is the paper's formulation of a period: it fixes every point on the
diagonal orbit, not just the chosen base point. -/
def IsOrbitPeriod (x : WeylChamberSpace) (u : Fin 2 → ℝ) : Prop :=
  ∀ y ∈ MulAction.orbit FlowParameter x, Multiplicative.ofAdd u • y = y

/-- Auxiliary fact `isOrbitPeriod_iff_isPeriod` used in the proof of the surrounding result from the preprint. -/
lemma isOrbitPeriod_iff_isPeriod (x : WeylChamberSpace) (u : Fin 2 → ℝ) :
    IsOrbitPeriod x u ↔ IsPeriod x u := by
  constructor
  · intro h
    exact h x ⟨1, one_smul FlowParameter x⟩
  · intro h y hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨v, rfl⟩ := hy
    rw [← mul_smul, mul_comm, mul_smul, h]

/-- The columns of `b` are a positively oriented `ℤ`-basis of the period lattice
of the orbit through `x`. -/
def IsPeriodBasis (x : WeylChamberSpace)
    (b : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  0 < b.det ∧
    ∀ u : Fin 2 → ℝ, IsPeriod x u ↔
      ∃ z : Fin 2 → ℤ, u = b.mulVec (fun i ↦ (z i : ℝ))

/-- A diagonal orbit is periodic when its period group is a full lattice in
the two-dimensional Lie algebra.  Existence of `b` is the finite-covolume
condition used in the paper. -/
def IsPeriodicTorus (x : WeylChamberSpace) : Prop :=
  ∃ b : Matrix (Fin 2) (Fin 2) ℝ, IsPeriodBasis x b

/-- Rescale a positively oriented period basis to determinant one. -/
def normalizeBasis (b : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : 0 < b.det) : SL2R :=
  ⟨(Real.sqrt b.det)⁻¹ • b, by
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin, pow_two]
    calc
      (Real.sqrt b.det)⁻¹ * (Real.sqrt b.det)⁻¹ * b.det =
          (Real.sqrt b.det)⁻¹ * (Real.sqrt b.det)⁻¹ *
            Real.sqrt b.det ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hb)]
      _ = 1 := by
        field_simp [ne_of_gt (Real.sqrt_pos.2 hb)]⟩

/-- Normalization commutes with multiplying positive-determinant bases. -/
theorem normalizeBasis_mul (a b : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : 0 < a.det) (hb : 0 < b.det) :
    normalizeBasis (a * b) (by simpa [Matrix.det_mul] using mul_pos ha hb) =
      normalizeBasis a ha * normalizeBasis b hb := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have hs : Real.sqrt (a.det * b.det) =
      Real.sqrt a.det * Real.sqrt b.det := by
    rw [Real.sqrt_mul (le_of_lt ha)]
  ext i j
  simp only [normalizeBasis, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  rw [Matrix.det_mul, hs]
  have hsa : Real.sqrt a.det ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hsb : Real.sqrt b.det ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  simp only [Fin.sum_univ_two]
  field_simp [hsa, hsb]

/-- `s` is the shape of the period lattice of the orbit through `x`. -/
def HasShape (x : WeylChamberSpace) (s : ShapeSpace) : Prop :=
  ∃ (b : Matrix (Fin 2) (Fin 2) ℝ) (hb : 0 < b.det),
    IsPeriodBasis x b ∧ s = (normalizeBasis b hb : ShapeSpace)

/-- The set of shapes of periodic tori in
`M \ SL(3, ℝ) / SL(3, ℤ)`. -/
def periodicTorusShapes : Set ShapeSpace :=
  {s | ∃ x : WeylChamberSpace, IsPeriodicTorus x ∧ HasShape x s}

/-- Auxiliary fact `periodBasis_shape_mem` used in the proof of the surrounding result from the preprint. -/
lemma periodBasis_shape_mem {x : WeylChamberSpace}
    {b : Matrix (Fin 2) (Fin 2) ℝ} (hb : IsPeriodBasis x b) :
    (normalizeBasis b hb.1 : ShapeSpace) ∈ periodicTorusShapes := by
  exact ⟨x, ⟨b, hb⟩, b, hb.1, hb, rfl⟩

/-- The Weyl chamber represented by a determinant-one real matrix. -/
def chamberOfMatrix (g : SL3R) : WeylChamberSpace :=
  Quotient.mk'' ((g : SL3R) : CubicLatticeSpace)

/-- The exact matrix equation saying that `u` fixes the chamber represented
by `g`, allowing a diagonal sign on the left and an integral change of basis
on the right. -/
def MatrixPeriodCondition (g : SL3R) (u : Fin 2 → ℝ) : Prop :=
  ∃ m : signDiagonal, ∃ gamma : SL3R,
    gamma ∈ integralSpecialLinear 3 ∧
      (m : SL3R) * g * gamma =
        diagonalEmbedding (Multiplicative.ofAdd u) * g

/-- Matrix form of the period criterion used in Lemma 2.6 of the paper. -/
theorem isPeriod_chamberOfMatrix_iff (g : SL3R) (u : Fin 2 → ℝ) :
    IsPeriod (chamberOfMatrix g) u ↔ MatrixPeriodCondition g u := by
  change Quotient.mk''
      ((diagonalEmbedding (Multiplicative.ofAdd u) * g : SL3R) :
        CubicLatticeSpace) =
      Quotient.mk'' ((g : SL3R) : CubicLatticeSpace) ↔ _
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨m, hm⟩
    change (((m : SL3R) * g : SL3R) : CubicLatticeSpace) =
      ((diagonalEmbedding (Multiplicative.ofAdd u) * g : SL3R) :
        CubicLatticeSpace) at hm
    have hgamma : ((m : SL3R) * g)⁻¹ *
        (diagonalEmbedding (Multiplicative.ofAdd u) * g) ∈
          integralSpecialLinear 3 := QuotientGroup.eq.mp hm
    refine ⟨m, ((m : SL3R) * g)⁻¹ *
      (diagonalEmbedding (Multiplicative.ofAdd u) * g), hgamma, ?_⟩
    group
  · rintro ⟨m, gamma, hgamma, hmatrix⟩
    refine ⟨m, ?_⟩
    change (((m : SL3R) * g : SL3R) : CubicLatticeSpace) =
      ((diagonalEmbedding (Multiplicative.ofAdd u) * g : SL3R) :
        CubicLatticeSpace)
    apply QuotientGroup.eq.mpr
    convert hgamma using 1
    rw [← hmatrix]
    group

/-- A matrix criterion for a prescribed oriented period basis. -/
theorem isPeriodBasis_chamberOfMatrix
    (g : SL3R) (b : Matrix (Fin 2) (Fin 2) ℝ) (hdet : 0 < b.det)
    (hperiod : ∀ u : Fin 2 → ℝ,
      MatrixPeriodCondition g u ↔
        ∃ z : Fin 2 → ℤ, u = b.mulVec (fun i ↦ (z i : ℝ))) :
    IsPeriodBasis (chamberOfMatrix g) b := by
  refine ⟨hdet, ?_⟩
  intro u
  rw [isPeriod_chamberOfMatrix_iff, hperiod]


end CubicPeriodicTori


/-!
The exact matrix criterion underlying Lemma 2.6 of the paper.
-/

noncomputable section

namespace CubicPeriodicTori

namespace OrderPeriods

open Matrix

variable {A : Type*} [CommRing A]

/-- The matrix whose rows are three real embeddings and whose columns are an
integral basis of a cubic order. -/
def embeddingMatrix (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j ↦ σ i (b j)

/-- Multiplication in the order is diagonalized by its real embeddings. -/
lemma embeddingMatrix_mul_leftMulMatrix
    (b : Module.Basis (Fin 3) ℤ A) (σ : Fin 3 → A →+* ℝ) (x : A) :
    embeddingMatrix b σ *
        (Algebra.leftMulMatrix b x).map (Int.castRingHom ℝ) =
      Matrix.diagonal (fun i ↦ σ i x) * embeddingMatrix b σ := by
  ext i j
  rw [show (Matrix.diagonal (fun i ↦ σ i x) * embeddingMatrix b σ) i j =
      σ i x * σ i (b j) by
    exact Matrix.diagonal_mul _ _ _ _]
  simp only [Matrix.mul_apply, embeddingMatrix, Matrix.of_apply,
    Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc
    ∑ k, σ i (b k) * ((b.repr (x * b j) k : ℤ) : ℝ) =
        σ i (∑ k, (b.repr (x * b j) k) • b k) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_zsmul]
      simp [mul_comm]
    _ = σ i (x * b j) := by rw [b.sum_repr]
    _ = σ i x * σ i (b j) := map_mul _ _ _

/-- A nonzero embedding matrix is rescaled in one row to determinant one.
The row rescaling commutes with every diagonal matrix, so it does not alter
the diagonal stabilizer. -/
def embeddingSL (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0) : SL3R :=
  ⟨Matrix.diagonal ![(embeddingMatrix b σ).det⁻¹, 1, 1] *
      embeddingMatrix b σ, by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, hdet]⟩

/-- Auxiliary fact `embeddingSL_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma embeddingSL_apply (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0)
    (i j : Fin 3) :
    embeddingSL b σ hdet i j =
      ![(embeddingMatrix b σ).det⁻¹, 1, 1] i * σ i (b j) := by
  simp [embeddingSL, embeddingMatrix, Matrix.diagonal_mul]

/-- Auxiliary fact `real_sign_mul` used in the proof of the surrounding result from the preprint. -/
lemma real_sign_mul (x y : ℝ) : Real.sign (x * y) = Real.sign x * Real.sign y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [Real.sign_of_neg hx, Real.sign_of_neg hy,
        Real.sign_of_pos (mul_pos_of_neg_of_neg hx hy)]
      norm_num
    · simp
    · rw [Real.sign_of_neg hx, Real.sign_of_pos hy,
        Real.sign_of_neg (mul_neg_of_neg_of_pos hx hy)]
      norm_num
  · simp
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [Real.sign_of_pos hx, Real.sign_of_neg hy,
        Real.sign_of_neg (mul_neg_of_pos_of_neg hx hy)]
      norm_num
    · simp
    · rw [Real.sign_of_pos hx, Real.sign_of_pos hy,
        Real.sign_of_pos (mul_pos hx hy)]
      norm_num

/-- Auxiliary fact `real_sign_mul_self_eq_abs` used in the proof of the surrounding result from the preprint. -/
lemma real_sign_mul_self_eq_abs (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]
    ring
  · simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx]
    ring

/-- Auxiliary fact `unit_embedding_ne_zero` used in the proof of the surrounding result from the preprint. -/
lemma unit_embedding_ne_zero (σ : A →+* ℝ) (x : Aˣ) : σ (x : A) ≠ 0 := by
  exact (x.isUnit.map σ).ne_zero

/-- Multiplying a unit by `-1`, if necessary, makes its integral
multiplication matrix orientation preserving without changing any absolute
value of an embedding. -/
lemma exists_oriented_unit (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (x : Aˣ) :
    ∃ y : Aˣ,
      (∀ i, |σ i (y : A)| = |σ i (x : A)|) ∧
      (Algebra.leftMulMatrix b (y : A)).det = 1 := by
  let M := Algebra.leftMulMatrix b (x : A)
  have hMunit : IsUnit M := x.isUnit.map (Algebra.leftMulMatrix b)
  have hdetunit : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp hMunit
  rcases Int.isUnit_iff.mp hdetunit with hdet | hdet
  · exact ⟨x, fun _ ↦ rfl, hdet⟩
  · refine ⟨-x, ?_, ?_⟩
    · intro i
      simp
    · change (Algebra.leftMulMatrix b (-(x : A))).det = 1
      rw [map_neg, Matrix.det_neg]
      simp [Fintype.card_fin, M, hdet]

/-- Auxiliary fact `isUnit_of_leftMulMatrix_det_isUnit` used in the proof of the surrounding result from the preprint. -/
lemma isUnit_of_leftMulMatrix_det_isUnit
    (b : Module.Basis (Fin 3) ℤ A) (z : A)
    (hz : IsUnit (Algebra.leftMulMatrix b z).det) : IsUnit z := by
  let e := (Algebra.leftMulMatrix b z).toLinearEquiv b hz
  let w : A := e.symm 1
  have hew : e w = z * w := by
    change Matrix.toLin b b (Algebra.leftMulMatrix b z) w = z * w
    rw [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
    rfl
  have hw : z * w = 1 := calc
    z * w = e w := hew.symm
    _ = 1 := e.apply_symm_apply 1
  exact ⟨⟨z, w, hw, by simpa [mul_comm] using hw⟩, rfl⟩

/-- The two coordinates of the logarithmic embedding used by the diagonal
flow.  The third coordinate is forced to be the negative of their sum once
the multiplication determinant is `1`. -/
def unitLog (σ : Fin 3 → A →+* ℝ) (x : Aˣ) : Fin 2 → ℝ :=
  ![Real.log (abs (σ 0 (x : A))), Real.log (abs (σ 1 (x : A)))]

def flowEigenvalues (u : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![Real.exp (u 0), Real.exp (u 1), Real.exp (-(u 0 + u 1))]

/-- Auxiliary fact `diagonalEmbedding_eq_flowEigenvalues` used in the proof of the surrounding result from the preprint. -/
lemma diagonalEmbedding_eq_flowEigenvalues (u : Fin 2 → ℝ) :
    (diagonalEmbedding (Multiplicative.ofAdd u) : SL3R) =
      ⟨Matrix.diagonal (flowEigenvalues u), by
        simp [flowEigenvalues, Matrix.det_diagonal, Fin.prod_univ_succ,
          ← Real.exp_add]⟩ := by
  rfl

/-- The determinant of integral multiplication is the product of its three
real eigenvalues. -/
lemma prod_embeddings_eq_det (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0)
    (x : A) :
    ∏ i, σ i x = ((Algebra.leftMulMatrix b x).det : ℤ) := by
  have h := congrArg Matrix.det
    (embeddingMatrix_mul_leftMulMatrix b σ x)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
  have hcast :
      (((Algebra.leftMulMatrix b x).map (Int.castRingHom ℝ)).det) =
        ((Algebra.leftMulMatrix b x).det : ℤ) := by
    exact (Int.cast_det (Algebra.leftMulMatrix b x)).symm
  rw [hcast] at h
  change (embeddingMatrix b σ).det *
      ((Algebra.leftMulMatrix b x).det : ℝ) =
    (∏ i, σ i x) * (embeddingMatrix b σ).det at h
  apply (mul_left_cancel₀ hdet)
  simpa [mul_comm] using h.symm

/-- Auxiliary fact `prod_oriented_unit_embeddings` used in the proof of the surrounding result from the preprint. -/
lemma prod_oriented_unit_embeddings (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0)
    (x : Aˣ) (hx : (Algebra.leftMulMatrix b (x : A)).det = 1) :
    ∏ i, σ i (x : A) = 1 := by
  rw [prod_embeddings_eq_det b σ hdet, hx]
  norm_num

/-- The diagonal sign matrix of an oriented unit. -/
def orientedUnitSign (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0)
    (x : Aˣ) (hx : (Algebra.leftMulMatrix b (x : A)).det = 1) :
    signDiagonal := by
  let s : Fin 3 → ℝ := fun i ↦ Real.sign (σ i (x : A))
  have hsprod : ∏ i, s i = 1 := by
    have hp := prod_oriented_unit_embeddings b σ hdet x hx
    simp [Fin.prod_univ_succ, s] at hp ⊢
    rw [← real_sign_mul, ← real_sign_mul, hp, Real.sign_one]
  let m : SL3R := ⟨Matrix.diagonal s, by
    rw [Matrix.det_diagonal, hsprod]⟩
  refine ⟨m, ?_⟩
  constructor
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ hij
  · intro i
    rcases Real.sign_apply_eq_of_ne_zero (σ i (x : A))
        (unit_embedding_ne_zero (σ i) x) with hi | hi
    · right
      simpa [m, s] using hi
    · left
      simpa [m, s] using hi

/-- Auxiliary fact `orientedUnitSign_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma orientedUnitSign_apply (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0)
    (x : Aˣ) (hx : (Algebra.leftMulMatrix b (x : A)).det = 1)
    (i j : Fin 3) :
    ((orientedUnitSign b σ hdet x hx : signDiagonal) : SL3R) i j =
      Matrix.diagonal (fun k ↦ Real.sign (σ k (x : A))) i j := rfl

/-- Auxiliary fact `diagonalEmbedding_unitLog_of_oriented` used in the proof of the surrounding result from the preprint. -/
lemma diagonalEmbedding_unitLog_of_oriented
    (b : Module.Basis (Fin 3) ℤ A) (σ : Fin 3 → A →+* ℝ)
    (hdet : (embeddingMatrix b σ).det ≠ 0) (x : Aˣ)
    (hx : (Algebra.leftMulMatrix b (x : A)).det = 1) :
    (diagonalEmbedding (Multiplicative.ofAdd (unitLog σ x)) : SL3R) =
      ⟨Matrix.diagonal (fun i ↦ |σ i (x : A)|), by
        rw [Matrix.det_diagonal]
        have hp := prod_oriented_unit_embeddings b σ hdet x hx
        simp [Fin.prod_univ_succ] at hp ⊢
        have hpabs := congrArg abs hp
        simpa [abs_mul, mul_assoc] using hpabs⟩ := by
  apply Subtype.ext
  have hp := prod_oriented_unit_embeddings b σ hdet x hx
  have h0 : 0 < |σ 0 (x : A)| := abs_pos.mpr (unit_embedding_ne_zero (σ 0) x)
  have h1 : 0 < |σ 1 (x : A)| := abs_pos.mpr (unit_embedding_ne_zero (σ 1) x)
  have h2 : 0 < |σ 2 (x : A)| := abs_pos.mpr (unit_embedding_ne_zero (σ 2) x)
  have hpabs : |σ 0 (x : A)| * |σ 1 (x : A)| * |σ 2 (x : A)| = 1 := by
    have hp' := congrArg abs hp
    simpa [Fin.prod_univ_succ, abs_mul, mul_assoc] using hp'
  have hthird :
      Real.exp (-(Real.log |σ 0 (x : A)| + Real.log |σ 1 (x : A)|)) =
        |σ 2 (x : A)| := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log h0, Real.exp_log h1]
    field_simp
    nlinarith
  change Matrix.diagonal
      ![Real.exp (unitLog σ x 0), Real.exp (unitLog σ x 1),
        Real.exp (-(unitLog σ x 0 + unitLog σ x 1))] =
    Matrix.diagonal (fun i ↦ |σ i (x : A)|)
  congr 1
  funext i
  fin_cases i
  · change Real.exp (Real.log |σ 0 (x : A)|) = |σ 0 (x : A)|
    exact Real.exp_log h0
  · change Real.exp (Real.log |σ 1 (x : A)|) = |σ 1 (x : A)|
    exact Real.exp_log h1
  · change Real.exp
      (-(Real.log |σ 0 (x : A)| + Real.log |σ 1 (x : A)|)) =
        |σ 2 (x : A)|
    exact hthird

/-- Every unit gives a period of the chamber defined by the embedding
matrix. -/
lemma matrixPeriodCondition_unitLog
    (b : Module.Basis (Fin 3) ℤ A) (σ : Fin 3 → A →+* ℝ)
    (hdet : (embeddingMatrix b σ).det ≠ 0) (x : Aˣ) :
    MatrixPeriodCondition (embeddingSL b σ hdet) (unitLog σ x) := by
  obtain ⟨y, habs, hy⟩ := exists_oriented_unit b σ x
  have hlog : unitLog σ y = unitLog σ x := by
    funext i
    fin_cases i <;> simp only [unitLog, Matrix.cons_val_zero,
      Matrix.cons_val_one, habs]
  rw [← hlog]
  let gammaZ : SL 3 ℤ := ⟨Algebra.leftMulMatrix b (y : A), hy⟩
  let gammaR : SL3R :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) gammaZ
  let m : signDiagonal := orientedUnitSign b σ hdet y hy
  refine ⟨m, gammaR, ⟨gammaZ, rfl⟩, ?_⟩
  apply Subtype.ext
  let E := embeddingMatrix b σ
  let q : Fin 3 → ℝ := ![E.det⁻¹, 1, 1]
  let v : Fin 3 → ℝ := fun i ↦ σ i (y : A)
  have hE : E * (Algebra.leftMulMatrix b (y : A)).map (Int.castRingHom ℝ) =
      Matrix.diagonal v * E := embeddingMatrix_mul_leftMulMatrix b σ (y : A)
  have hD := diagonalEmbedding_unitLog_of_oriented b σ hdet y hy
  change (((m : SL3R) : Matrix (Fin 3) (Fin 3) ℝ) *
      (embeddingSL b σ hdet : Matrix (Fin 3) (Fin 3) ℝ)) *
      (gammaR : Matrix (Fin 3) (Fin 3) ℝ) =
    (diagonalEmbedding (Multiplicative.ofAdd (unitLog σ y)) :
      Matrix (Fin 3) (Fin 3) ℝ) *
      (embeddingSL b σ hdet : Matrix (Fin 3) (Fin 3) ℝ)
  change (Matrix.diagonal (fun i ↦ Real.sign (v i)) *
      (Matrix.diagonal q * E)) *
      (Algebra.leftMulMatrix b (y : A)).map (Int.castRingHom ℝ) =
    (diagonalEmbedding (Multiplicative.ofAdd (unitLog σ y)) :
      Matrix (Fin 3) (Fin 3) ℝ) * (Matrix.diagonal q * E)
  rw [hD]
  change (Matrix.diagonal (fun i ↦ Real.sign (v i)) *
      (Matrix.diagonal q * E)) *
      (Algebra.leftMulMatrix b (y : A)).map (Int.castRingHom ℝ) =
    Matrix.diagonal (fun i ↦ |v i|) * (Matrix.diagonal q * E)
  rw [Matrix.mul_assoc, Matrix.mul_assoc (Matrix.diagonal q), hE]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.diagonal_mul,
    Matrix.diagonal_mul, Matrix.diagonal_mul]
  calc
    Real.sign (v i) * (q i * (v i * E i j)) =
        (Real.sign (v i) * v i) * (q i * E i j) := by ring
    _ = |v i| * (q i * E i j) := by rw [real_sign_mul_self_eq_abs]

/-- Conversely, an integral stabilizer of the embedding matrix is
multiplication by a unit of the order. -/
lemma exists_unit_of_matrixPeriodCondition
    (b : Module.Basis (Fin 3) ℤ A) (σ : Fin 3 → A →+* ℝ)
    (hb0 : b 0 = 1) (hσ : Function.Injective (σ 0))
    (hdet : (embeddingMatrix b σ).det ≠ 0) (u : Fin 2 → ℝ)
    (hu : MatrixPeriodCondition (embeddingSL b σ hdet) u) :
    ∃ x : Aˣ, u = unitLog σ x := by
  rcases hu with ⟨m, gammaR, hgamma, hmatrix⟩
  rcases hgamma with ⟨gammaZ, rfl⟩
  let E := embeddingMatrix b σ
  let q : Fin 3 → ℝ := ![E.det⁻¹, 1, 1]
  let s : Fin 3 → ℝ := fun i ↦ (m : SL3R) i i
  let d : Fin 3 → ℝ := flowEigenvalues u
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    (gammaZ : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℝ)
  have hq (i : Fin 3) : q i ≠ 0 := by
    fin_cases i <;> simp [q, E, hdet]
  have hs (i : Fin 3) : s i = 1 ∨ s i = -1 := m.property.2 i
  have hs_sq (i : Fin 3) : s i * s i = 1 := by
    rcases hs i with hi | hi <;> rw [hi] <;> norm_num
  have hmatrix' :
      (Matrix.diagonal s * (Matrix.diagonal q * E)) * M =
        Matrix.diagonal d * (Matrix.diagonal q * E) := by
    have h := congrArg
      (fun g : SL3R ↦ (g : Matrix (Fin 3) (Fin 3) ℝ)) hmatrix
    change (((m : SL3R) : Matrix (Fin 3) (Fin 3) ℝ) *
        (embeddingSL b σ hdet : Matrix (Fin 3) (Fin 3) ℝ)) * M =
      (diagonalEmbedding (Multiplicative.ofAdd u) :
        Matrix (Fin 3) (Fin 3) ℝ) *
        (embeddingSL b σ hdet : Matrix (Fin 3) (Fin 3) ℝ) at h
    rw [← Matrix.IsDiag.diagonal_diag m.property.1] at h
    rw [diagonalEmbedding_eq_flowEigenvalues u] at h
    exact h
  have hraw : E * M = Matrix.diagonal (fun i ↦ s i * d i) * E := by
    ext i j
    have hij := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℝ ↦ X i j) hmatrix'
    rw [Matrix.mul_assoc, Matrix.mul_assoc (Matrix.diagonal q)] at hij
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.diagonal_mul,
      Matrix.diagonal_mul] at hij
    have hcancel : s i * (E * M) i j = d i * E i j := by
      apply mul_left_cancel₀ (hq i)
      calc
        q i * (s i * (E * M) i j) =
            s i * (q i * (E * M) i j) := by ring
        _ = d i * (q i * E i j) := hij
        _ = q i * (d i * E i j) := by ring
    rw [Matrix.diagonal_mul]
    calc
      (E * M) i j = (s i * s i) * (E * M) i j := by rw [hs_sq]; ring
      _ = s i * (s i * (E * M) i j) := by ring
      _ = s i * (d i * E i j) := by rw [hcancel]
      _ = (s i * d i) * E i j := by ring
  let z : A := ∑ k, (gammaZ k 0) • b k
  have hEM (i j : Fin 3) :
      (E * M) i j = σ i (∑ k, (gammaZ k j) • b k) := by
    simp only [Matrix.mul_apply, E, M, embeddingMatrix, Matrix.of_apply,
      Matrix.map_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_zsmul]
    simp [mul_comm]
  have hzemb (i : Fin 3) : σ i z = s i * d i := by
    have hi := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℝ ↦ X i 0) hraw
    rw [Matrix.diagonal_mul] at hi
    rw [hEM] at hi
    simpa [z, E, embeddingMatrix, hb0] using hi
  have hleft : Algebra.leftMulMatrix b z =
      (gammaZ : Matrix (Fin 3) (Fin 3) ℤ) := by
    ext k j
    have helem : ∑ r, (gammaZ r j) • b r = z * b j := by
      apply hσ
      calc
        σ 0 (∑ r, (gammaZ r j) • b r) = (E * M) 0 j := (hEM 0 j).symm
        _ = (s 0 * d 0) * E 0 j := by
          have h := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℝ ↦ X 0 j) hraw
          simpa only [Matrix.diagonal_mul] using h
        _ = (s 0 * d 0) * σ 0 (b j) := by simp [E, embeddingMatrix]
        _ = σ 0 z * σ 0 (b j) := by rw [hzemb]
        _ = σ 0 (z * b j) := (map_mul _ _ _).symm
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [← helem]
    exact congrFun (b.repr_sum_self (fun r ↦ gammaZ r j)) k
  have hzdet : (Algebra.leftMulMatrix b z).det = 1 := by
    rw [hleft]
    exact gammaZ.property
  have hzunit : IsUnit z :=
    isUnit_of_leftMulMatrix_det_isUnit b z (hzdet ▸ isUnit_one)
  let x : Aˣ := hzunit.unit
  refine ⟨x, ?_⟩
  have hxval : (x : A) = z := hzunit.unit_spec
  funext i
  fin_cases i
  · change u 0 = Real.log |σ 0 (x : A)|
    rw [hxval, hzemb]
    have hsabs : |s 0| = 1 := by
      rcases hs 0 with h | h <;> rw [h] <;> norm_num
    have hd0 : d 0 = Real.exp (u 0) := rfl
    rw [hd0, abs_mul, hsabs, one_mul, abs_of_pos (Real.exp_pos _), Real.log_exp]
  · change u 1 = Real.log |σ 1 (x : A)|
    rw [hxval, hzemb]
    have hsabs : |s 1| = 1 := by
      rcases hs 1 with h | h <;> rw [h] <;> norm_num
    have hd1 : d 1 = Real.exp (u 1) := rfl
    rw [hd1, abs_mul, hsabs, one_mul, abs_of_pos (Real.exp_pos _), Real.log_exp]

/-- Auxiliary fact `matrixPeriodCondition_iff_unitLog` used in the proof of the surrounding result from the preprint. -/
theorem matrixPeriodCondition_iff_unitLog
    (b : Module.Basis (Fin 3) ℤ A) (σ : Fin 3 → A →+* ℝ)
    (hb0 : b 0 = 1) (hσ : Function.Injective (σ 0))
    (hdet : (embeddingMatrix b σ).det ≠ 0) (u : Fin 2 → ℝ) :
    MatrixPeriodCondition (embeddingSL b σ hdet) u ↔
      ∃ x : Aˣ, u = unitLog σ x := by
  constructor
  · exact exists_unit_of_matrixPeriodCondition b σ hb0 hσ hdet u
  · rintro ⟨x, rfl⟩
    exact matrixPeriodCondition_unitLog b σ hdet x

/-- Lemma 2.6 in the form used by the final construction: once a matrix is
known to be a positively oriented basis of the logarithms of all units, it
is the period basis of the associated chamber. -/
theorem isPeriodBasis_embeddingSL
    (b : Module.Basis (Fin 3) ℤ A) (σ : Fin 3 → A →+* ℝ)
    (hb0 : b 0 = 1) (hσ : Function.Injective (σ 0))
    (hdet : (embeddingMatrix b σ).det ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : 0 < B.det)
    (hlogs : ∀ u : Fin 2 → ℝ,
      (∃ x : Aˣ, u = unitLog σ x) ↔
        ∃ z : Fin 2 → ℤ, u = B.mulVec (fun i ↦ (z i : ℝ))) :
    IsPeriodBasis (chamberOfMatrix (embeddingSL b σ hdet)) B := by
  apply isPeriodBasis_chamberOfMatrix _ _ hB
  intro u
  rw [matrixPeriodCondition_iff_unitLog b σ hb0 hσ hdet]
  exact hlogs u

/-- Auxiliary fact `normalized_unit_log_shape_mem_periodicTorusShapes` used in the proof of the surrounding result from the preprint. -/
theorem normalized_unit_log_shape_mem_periodicTorusShapes
    (b : Module.Basis (Fin 3) ℤ A) (σ : Fin 3 → A →+* ℝ)
    (hb0 : b 0 = 1) (hσ : Function.Injective (σ 0))
    (hdet : (embeddingMatrix b σ).det ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : 0 < B.det)
    (hlogs : ∀ u : Fin 2 → ℝ,
      (∃ x : Aˣ, u = unitLog σ x) ↔
        ∃ z : Fin 2 → ℤ, u = B.mulVec (fun i ↦ (z i : ℝ))) :
    (normalizeBasis B hB : ShapeSpace) ∈ periodicTorusShapes := by
  exact periodBasis_shape_mem
    (isPeriodBasis_embeddingSL b σ hb0 hσ hdet B hB hlogs)

end OrderPeriods

end CubicPeriodicTori


noncomputable section

namespace CubicOrderFamily

open Polynomial

def definingPolynomial (a₁ a₂ : ℤ) : Polynomial ℤ :=
  X * (X - C a₁) * (X - C a₂) - 1

/-- Auxiliary fact `definingPolynomial_monic` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomial_monic (a₁ a₂ : ℤ) :
    (definingPolynomial a₁ a₂).Monic := by
  have hp12 : (X * (X - C a₁) : Polynomial ℤ).Monic :=
    monic_X.mul (monic_X_sub_C a₁)
  have hp : (X * (X - C a₁) * (X - C a₂) : Polynomial ℤ).Monic :=
    hp12.mul (monic_X_sub_C a₂)
  apply Monic.sub_of_left
  · exact hp
  · rw [degree_one, degree_eq_natDegree hp.ne_zero,
      hp12.natDegree_mul (monic_X_sub_C a₂),
      monic_X.natDegree_mul (monic_X_sub_C a₁),
      natDegree_X, natDegree_X_sub_C, natDegree_X_sub_C]
    norm_num

/-- Auxiliary fact `definingPolynomial_natDegree` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomial_natDegree (a₁ a₂ : ℤ) :
    (definingPolynomial a₁ a₂).natDegree = 3 := by
  have hp12 : (X * (X - C a₁) : Polynomial ℤ).Monic :=
    monic_X.mul (monic_X_sub_C a₁)
  have hp : (X * (X - C a₁) * (X - C a₂) : Polynomial ℤ).Monic :=
    hp12.mul (monic_X_sub_C a₂)
  have hlt : (1 : Polynomial ℤ).degree <
      (X * (X - C a₁) * (X - C a₂)).degree := by
    rw [degree_one, degree_eq_natDegree hp.ne_zero,
      hp12.natDegree_mul (monic_X_sub_C a₂),
      monic_X.natDegree_mul (monic_X_sub_C a₁),
      natDegree_X, natDegree_X_sub_C, natDegree_X_sub_C]
    norm_num
  rw [definingPolynomial,
    natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlt),
    hp12.natDegree_mul (monic_X_sub_C a₂),
    monic_X.natDegree_mul (monic_X_sub_C a₁),
    natDegree_X, natDegree_X_sub_C, natDegree_X_sub_C]

/-- Auxiliary fact `definingPolynomial_eval` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomial_eval (a₁ a₂ x : ℤ) :
    (definingPolynomial a₁ a₂).eval x = x * (x - a₁) * (x - a₂) - 1 := by
  simp [definingPolynomial]

/-- Auxiliary fact `definingPolynomial_eval_one_ne_zero` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomial_eval_one_ne_zero {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    (definingPolynomial a₁ a₂).eval 1 ≠ 0 := by
  rw [definingPolynomial_eval]
  have h₁ : 2 ≤ a₁ - 1 := by omega
  have h₂ : 3 ≤ a₂ - 1 := by omega
  have hmul : 6 ≤ (a₁ - 1) * (a₂ - 1) := by nlinarith
  nlinarith

/-- Auxiliary fact `definingPolynomial_eval_neg_one_ne_zero` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomial_eval_neg_one_ne_zero {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    (definingPolynomial a₁ a₂).eval (-1) ≠ 0 := by
  rw [definingPolynomial_eval]
  have h₁ : 0 < 1 + a₁ := by omega
  have h₂ : 0 < 1 + a₂ := by omega
  have hmul : 0 < (1 + a₁) * (1 + a₂) := mul_pos h₁ h₂
  nlinarith

def definingPolynomialQ (a₁ a₂ : ℤ) : Polynomial ℚ :=
  (definingPolynomial a₁ a₂).map (Int.castRingHom ℚ)

def definingPolynomialR (a₁ a₂ : ℤ) : Polynomial ℝ :=
  (definingPolynomial a₁ a₂).map (Int.castRingHom ℝ)

/-- Parameters for the family of cubic orders, bundled so their inequalities are available
to the typeclass system when constructing the number field. -/
structure Parameters where
  a₁ : ℤ
  a₂ : ℤ
  three_le : 3 ≤ a₁
  lt : a₁ < a₂

/-- Auxiliary fact `definingPolynomialR_eval` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomialR_eval (a₁ a₂ : ℤ) (x : ℝ) :
    (definingPolynomialR a₁ a₂).eval x =
      x * (x - a₁) * (x - a₂) - 1 := by
  simp [definingPolynomialR, definingPolynomial]

/-- The three separated real roots used to identify the cubic field as totally
real.  The intervals are the ones used in the paper. -/
lemma exists_three_real_roots {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    ∃ r₀ r₁ r₂ : ℝ,
      r₀ ∈ Set.Icc 0 1 ∧
      r₁ ∈ Set.Icc ((a₁ : ℝ) - 1) a₁ ∧
      r₂ ∈ Set.Icc (a₂ : ℝ) (a₂ + 1) ∧
      (definingPolynomialR a₁ a₂).IsRoot r₀ ∧
      (definingPolynomialR a₁ a₂).IsRoot r₁ ∧
      (definingPolynomialR a₁ a₂).IsRoot r₂ := by
  let p := definingPolynomialR a₁ a₂
  have ha₁r : (3 : ℝ) ≤ a₁ := by exact_mod_cast ha₁
  have ha₂r : (a₁ : ℝ) < a₂ := by exact_mod_cast ha₂
  have h0 : p.eval 0 ≤ 0 := by simp [p, definingPolynomialR_eval]
  have h1 : 0 ≤ p.eval 1 := by
    rw [show p.eval 1 =
      (1 : ℝ) * (1 - a₁) * (1 - a₂) - 1 by
        simp [p, definingPolynomialR_eval]]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha₁r) (sub_nonneg.mpr ha₂r.le)]
  have hz₀ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    p.continuous.continuousOn ⟨h0, h1⟩
  rcases hz₀ with ⟨r₀, hr₀I, hr₀⟩
  have hmidL : 0 ≤ p.eval ((a₁ : ℝ) - 1) := by
    rw [show p.eval ((a₁ : ℝ) - 1) =
      ((a₁ : ℝ) - 1) * (((a₁ : ℝ) - 1) - a₁) *
        (((a₁ : ℝ) - 1) - a₂) - 1 by
          simp [p, definingPolynomialR_eval]]
    have ha₁m : 0 ≤ (a₁ : ℝ) - 1 := by linarith
    have hgap : 0 ≤ (a₂ : ℝ) - a₁ + 1 := by linarith
    nlinarith [mul_nonneg ha₁m hgap]
  have hmidR : p.eval (a₁ : ℝ) ≤ 0 := by simp [p, definingPolynomialR_eval]
  have hz₁ := intermediate_value_Icc'
    (by norm_num : (a₁ : ℝ) - 1 ≤ a₁)
    p.continuous.continuousOn ⟨hmidR, hmidL⟩
  rcases hz₁ with ⟨r₁, hr₁I, hr₁⟩
  have hrightL : p.eval (a₂ : ℝ) ≤ 0 := by simp [p, definingPolynomialR_eval]
  have hrightR : 0 ≤ p.eval ((a₂ : ℝ) + 1) := by
    rw [show p.eval ((a₂ : ℝ) + 1) =
      ((a₂ : ℝ) + 1) * (((a₂ : ℝ) + 1) - a₁) *
        (((a₂ : ℝ) + 1) - a₂) - 1 by
          simp [p, definingPolynomialR_eval]]
    nlinarith
  have hz₂ := intermediate_value_Icc
    (by norm_num : (a₂ : ℝ) ≤ a₂ + 1)
    p.continuous.continuousOn ⟨hrightL, hrightR⟩
  rcases hz₂ with ⟨r₂, hr₂I, hr₂⟩
  exact ⟨r₀, r₁, r₂, hr₀I, hr₁I, hr₂I, hr₀, hr₁, hr₂⟩

/-- A chosen ordered triple of the three real roots. -/
structure RootTriple (P : Parameters) where
  r₀ : ℝ
  r₁ : ℝ
  r₂ : ℝ
  r₀_mem : r₀ ∈ Set.Icc 0 1
  r₁_mem : r₁ ∈ Set.Icc ((P.a₁ : ℝ) - 1) P.a₁
  r₂_mem : r₂ ∈ Set.Icc (P.a₂ : ℝ) (P.a₂ + 1)
  r₀_root : (definingPolynomialR P.a₁ P.a₂).IsRoot r₀
  r₁_root : (definingPolynomialR P.a₁ P.a₂).IsRoot r₁
  r₂_root : (definingPolynomialR P.a₁ P.a₂).IsRoot r₂

/-- Auxiliary fact `rootTriple_nonempty` used in the proof of the surrounding result from the preprint. -/
lemma rootTriple_nonempty (P : Parameters) : Nonempty (RootTriple P) := by
  obtain ⟨r₀, r₁, r₂, h₀, h₁, h₂, hr₀, hr₁, hr₂⟩ :=
    exists_three_real_roots P.three_le P.lt
  exact ⟨⟨r₀, r₁, r₂, h₀, h₁, h₂, hr₀, hr₁, hr₂⟩⟩

noncomputable def rootTriple (P : Parameters) : RootTriple P :=
  Classical.choice (rootTriple_nonempty P)

noncomputable def realRoot (P : Parameters) : Fin 3 → ℝ :=
  ![(rootTriple P).r₀, (rootTriple P).r₁, (rootTriple P).r₂]

noncomputable def root0 (P : Parameters) : ℝ := realRoot P 0
noncomputable def root1 (P : Parameters) : ℝ := realRoot P 1
noncomputable def root2 (P : Parameters) : ℝ := realRoot P 2

/-- Auxiliary fact `root0_eq` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma root0_eq (P : Parameters) : root0 P = (rootTriple P).r₀ := rfl
/-- Auxiliary fact `root1_eq` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma root1_eq (P : Parameters) : root1 P = (rootTriple P).r₁ := rfl
/-- Auxiliary fact `root2_eq` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma root2_eq (P : Parameters) : root2 P = (rootTriple P).r₂ := rfl

/-- Auxiliary fact `realRoot_root` used in the proof of the surrounding result from the preprint. -/
lemma realRoot_root (P : Parameters) (i : Fin 3) :
    (definingPolynomialR P.a₁ P.a₂).IsRoot (realRoot P i) := by
  fin_cases i
  · exact (rootTriple P).r₀_root
  · exact (rootTriple P).r₁_root
  · exact (rootTriple P).r₂_root

/-- Auxiliary fact `realRoot_injective` used in the proof of the surrounding result from the preprint. -/
lemma realRoot_injective (P : Parameters) : Function.Injective (realRoot P) := by
  have ha₁r : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂r : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  rcases (rootTriple P).r₀_mem with ⟨h₀l, h₀u⟩
  rcases (rootTriple P).r₁_mem with ⟨h₁l, h₁u⟩
  rcases (rootTriple P).r₂_mem with ⟨h₂l, h₂u⟩
  have hr₀₁ : (rootTriple P).r₀ ≠ (rootTriple P).r₁ := by
    intro h
    rw [h] at h₀u
    linarith
  have hr₀₂ : (rootTriple P).r₀ ≠ (rootTriple P).r₂ := by
    intro h
    have ha₂three : (3 : ℝ) < P.a₂ := lt_of_le_of_lt ha₁r ha₂r
    rw [h] at h₀u
    linarith
  have hr₁₂ : (rootTriple P).r₁ ≠ (rootTriple P).r₂ := by
    intro h
    rw [h] at h₁u
    linarith
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [realRoot]

/-- Auxiliary fact `root0_strictBounds` used in the proof of the surrounding result from the preprint. -/
lemma root0_strictBounds (P : Parameters) : 0 < root0 P ∧ root0 P < 1 := by
  have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hroot := (rootTriple P).r₀_root
  rw [Polynomial.IsRoot, definingPolynomialR_eval] at hroot
  constructor
  · refine lt_of_le_of_ne (rootTriple P).r₀_mem.1 ?_
    intro h
    have : (rootTriple P).r₀ = 0 := h.symm
    rw [this] at hroot
    norm_num at hroot
  · refine lt_of_le_of_ne (rootTriple P).r₀_mem.2 ?_
    intro h
    change (rootTriple P).r₀ = 1 at h
    rw [h] at hroot
    nlinarith

/-- Auxiliary fact `root1_strictBounds` used in the proof of the surrounding result from the preprint. -/
lemma root1_strictBounds (P : Parameters) :
    (P.a₁ : ℝ) - 1 < root1 P ∧ root1 P < P.a₁ := by
  have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hroot := (rootTriple P).r₁_root
  rw [Polynomial.IsRoot, definingPolynomialR_eval] at hroot
  constructor
  · refine lt_of_le_of_ne (rootTriple P).r₁_mem.1 ?_
    intro h
    change (P.a₁ : ℝ) - 1 = (rootTriple P).r₁ at h
    rw [← h] at hroot
    have ha₂step : P.a₁ + 1 ≤ P.a₂ := Int.add_one_le_iff.mpr P.lt
    have ha₂stepR : (P.a₁ : ℝ) + 1 ≤ P.a₂ := by exact_mod_cast ha₂step
    have hleft : (2 : ℝ) ≤ (P.a₁ : ℝ) - 1 := by linarith
    have hgap : (2 : ℝ) ≤ (P.a₂ : ℝ) - P.a₁ + 1 := by linarith
    have hprod : (4 : ℝ) ≤ ((P.a₁ : ℝ) - 1) * ((P.a₂ : ℝ) - P.a₁ + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : (1 : ℝ) ≤ P.a₁))
        (by linarith : 0 ≤ (P.a₂ : ℝ) - P.a₁)]
    nlinarith
  · refine lt_of_le_of_ne (rootTriple P).r₁_mem.2 ?_
    intro h
    change (rootTriple P).r₁ = (P.a₁ : ℝ) at h
    rw [h] at hroot
    norm_num at hroot

/-- Auxiliary fact `root2_strictBounds` used in the proof of the surrounding result from the preprint. -/
lemma root2_strictBounds (P : Parameters) :
    (P.a₂ : ℝ) < root2 P ∧ root2 P < P.a₂ + 1 := by
  have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hroot := (rootTriple P).r₂_root
  rw [Polynomial.IsRoot, definingPolynomialR_eval] at hroot
  constructor
  · refine lt_of_le_of_ne (rootTriple P).r₂_mem.1 ?_
    intro h
    change (P.a₂ : ℝ) = (rootTriple P).r₂ at h
    rw [← h] at hroot
    norm_num at hroot
  · refine lt_of_le_of_ne (rootTriple P).r₂_mem.2 ?_
    intro h
    change (rootTriple P).r₂ = (P.a₂ : ℝ) + 1 at h
    rw [h] at hroot
    have ha₂step : P.a₁ + 1 ≤ P.a₂ := Int.add_one_le_iff.mpr P.lt
    have ha₂stepR : (P.a₁ : ℝ) + 1 ≤ P.a₂ := by exact_mod_cast ha₂step
    have hgap : (2 : ℝ) ≤ (P.a₂ : ℝ) + 1 - P.a₁ := by linarith
    have ha₂pos : (4 : ℝ) ≤ (P.a₂ : ℝ) + 1 := by linarith
    have hprod : (8 : ℝ) ≤ ((P.a₂ : ℝ) + 1) * ((P.a₂ : ℝ) + 1 - P.a₁) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ (P.a₂ : ℝ) + 1)
        (by linarith : 0 ≤ (P.a₂ : ℝ) + 1 - P.a₁)]
    nlinarith

/-- Auxiliary fact `roots_strict_order` used in the proof of the surrounding result from the preprint. -/
lemma roots_strict_order (P : Parameters) :
    root0 P < root1 P ∧ root1 P < root2 P := by
  constructor
  · have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root0_strictBounds P).2, (root1_strictBounds P).1]
  · have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith [(root1_strictBounds P).2, (root2_strictBounds P).1]

/-- Auxiliary fact `definingPolynomialQ_eval₂_real_eq` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomialQ_eval₂_real_eq
    (a₁ a₂ : ℤ) (x : ℝ) :
    Polynomial.eval₂ (algebraMap ℚ ℝ) x (definingPolynomialQ a₁ a₂) =
      (definingPolynomialR a₁ a₂).eval x := by
  simp [definingPolynomialQ, definingPolynomialR, definingPolynomial,
    Polynomial.eval₂_eq_eval_map]

/-- Auxiliary fact `definingPolynomialQ_monic` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomialQ_monic (a₁ a₂ : ℤ) :
    (definingPolynomialQ a₁ a₂).Monic :=
  (definingPolynomial_monic a₁ a₂).map (Int.castRingHom ℚ)

/-- Auxiliary fact `definingPolynomialQ_natDegree` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomialQ_natDegree (a₁ a₂ : ℤ) :
    (definingPolynomialQ a₁ a₂).natDegree = 3 := by
  rw [definingPolynomialQ, (definingPolynomial_monic a₁ a₂).natDegree_map]
  exact definingPolynomial_natDegree a₁ a₂

/-- Auxiliary fact `definingPolynomialQ_irreducible` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomialQ_irreducible {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    Irreducible (definingPolynomialQ a₁ a₂) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [definingPolynomialQ_natDegree]
  · intro x hx
    have hroot : aeval x (definingPolynomial a₁ a₂) = 0 := by
      rw [IsRoot, definingPolynomialQ, eval_map] at hx
      simpa [aeval_def] using hx
    obtain ⟨z, rfl, hz⟩ := exists_integer_of_is_root_of_monic
      (definingPolynomial_monic a₁ a₂) hroot
    have hz' : z ∣ (1 : ℤ) := by
      simpa [definingPolynomial, coeff_sub] using hz
    have hzunit : IsUnit z := isUnit_iff_dvd_one.mpr hz'
    rcases Int.isUnit_iff.mp hzunit with rfl | rfl
    · have ha₁q : (3 : ℚ) ≤ a₁ := by exact_mod_cast ha₁
      have ha₂q : (a₁ : ℚ) < a₂ := by exact_mod_cast ha₂
      simp [definingPolynomialQ, definingPolynomial, IsRoot] at hx
      nlinarith
    · have ha₁q : (3 : ℚ) ≤ a₁ := by exact_mod_cast ha₁
      have ha₂q : (a₁ : ℚ) < a₂ := by exact_mod_cast ha₂
      simp [definingPolynomialQ, definingPolynomial, IsRoot] at hx
      nlinarith

/-- Auxiliary fact `definingPolynomial_irreducible` used in the proof of the surrounding result from the preprint. -/
lemma definingPolynomial_irreducible {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    Irreducible (definingPolynomial a₁ a₂) := by
  exact ((definingPolynomial_monic a₁ a₂).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mpr (definingPolynomialQ_irreducible ha₁ ha₂)

instance (P : Parameters) : Fact (Irreducible (definingPolynomialQ P.a₁ P.a₂)) :=
  ⟨definingPolynomialQ_irreducible P.three_le P.lt⟩

/-- The cubic field generated by a root of the defining polynomial. -/
abbrev CubicField (P : Parameters) := AdjoinRoot (definingPolynomialQ P.a₁ P.a₂)

/-- Auxiliary fact `field_finrank` used in the proof of the surrounding result from the preprint. -/
lemma field_finrank (P : Parameters) : Module.finrank ℚ (CubicField P) = 3 := by
  rw [(AdjoinRoot.powerBasis (definingPolynomialQ_monic P.a₁ P.a₂).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, definingPolynomialQ_natDegree]

instance (P : Parameters) : Fact (Module.finrank ℚ (CubicField P) = 3) :=
  ⟨field_finrank P⟩

/-- The distinguished root in the cubic-order number field. -/
def thetaZero (P : Parameters) : CubicField P :=
  AdjoinRoot.root (definingPolynomialQ P.a₁ P.a₂)

/-- A real root of the defining polynomial gives a real embedding of the cubic-order
field. -/
def realLift (P : Parameters) (r : ℝ)
    (hr : (definingPolynomialR P.a₁ P.a₂).IsRoot r) : CubicField P →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) r <| by
    rw [definingPolynomialQ_eval₂_real_eq]
    exact hr

/-- Auxiliary fact `realLift_thetaZero` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma realLift_thetaZero (P : Parameters) (r : ℝ)
    (hr : (definingPolynomialR P.a₁ P.a₂).IsRoot r) :
    realLift P r hr (thetaZero P) = r := by
  exact AdjoinRoot.lift_root _

/-- Regard a real embedding as a complex embedding fixed by conjugation. -/
def complexOfRealEmbedding {K : Type*} [Field K] (f : K →+* ℝ) :
    { φ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ } :=
  ⟨Complex.ofRealHom.comp f, by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq]⟩

/-- Auxiliary fact `complexOfRealEmbedding_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma complexOfRealEmbedding_apply {K : Type*} [Field K]
    (f : K →+* ℝ) (x : K) :
    (complexOfRealEmbedding f : K →+* ℂ) x = f x :=
  rfl

noncomputable def rootEmbedding (P : Parameters) (i : Fin 3) :
    CubicField P →+* ℝ :=
  realLift P (realRoot P i) (realRoot_root P i)

noncomputable def rootPlace (P : Parameters) (i : Fin 3) :
    NumberField.InfinitePlace (CubicField P) :=
  NumberField.InfinitePlace.mk (complexOfRealEmbedding (rootEmbedding P i))

/-- Auxiliary fact `realRoot_nonneg` used in the proof of the surrounding result from the preprint. -/
lemma realRoot_nonneg (P : Parameters) (i : Fin 3) : 0 ≤ realRoot P i := by
  have ha₁r : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂r : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  fin_cases i
  · exact (rootTriple P).r₀_mem.1
  · exact le_trans (by linarith) (rootTriple P).r₁_mem.1
  · exact le_trans (by linarith) (rootTriple P).r₂_mem.1

/-- Auxiliary fact `rootPlace_thetaZero` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma rootPlace_thetaZero (P : Parameters) (i : Fin 3) :
    rootPlace P i (thetaZero P) = realRoot P i := by
  rw [rootPlace, NumberField.InfinitePlace.apply]
  simp [rootEmbedding, Real.norm_eq_abs, abs_of_nonneg (realRoot_nonneg P i)]

/-- Auxiliary fact `rootPlace_injective` used in the proof of the surrounding result from the preprint. -/
lemma rootPlace_injective (P : Parameters) : Function.Injective (rootPlace P) := by
  intro i j h
  apply realRoot_injective P
  rw [← rootPlace_thetaZero P i, ← rootPlace_thetaZero P j, h]

/-- The cubic field is totally real: the three disjoint sign-change intervals
produce three real embeddings, exhausting its three complex embeddings. -/
theorem cubicField_isTotallyReal (P : Parameters) :
    NumberField.IsTotallyReal (CubicField P) := by
  classical
  obtain ⟨r₀, r₁, r₂, hr₀I, hr₁I, hr₂I, hr₀, hr₁, hr₂⟩ :=
    exists_three_real_roots P.three_le P.lt
  have ha₁r : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂r : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hr₀₁ : r₀ ≠ r₁ := by
    intro h
    rw [h] at hr₀I
    linarith [hr₀I.2, hr₁I.1]
  have hr₁₂ : r₁ ≠ r₂ := by
    intro h
    rw [h] at hr₁I
    linarith [hr₁I.2, hr₂I.1]
  have hr₀₂ : r₀ ≠ r₂ := by
    intro h
    rw [h] at hr₀I
    linarith [hr₀I.2, hr₂I.1]
  let e₀ := complexOfRealEmbedding (realLift P r₀ hr₀)
  let e₁ := complexOfRealEmbedding (realLift P r₁ hr₁)
  let e₂ := complexOfRealEmbedding (realLift P r₂ hr₂)
  have he₀₁ : e₀ ≠ e₁ := by
    intro h
    have hv := congrArg
      (fun e : { φ : CubicField P →+* ℂ //
        NumberField.ComplexEmbedding.IsReal φ } ↦ (e.1 (thetaZero P)).re) h
    exact hr₀₁ (by simpa [e₀, e₁] using hv)
  have he₁₂ : e₁ ≠ e₂ := by
    intro h
    have hv := congrArg
      (fun e : { φ : CubicField P →+* ℂ //
        NumberField.ComplexEmbedding.IsReal φ } ↦ (e.1 (thetaZero P)).re) h
    exact hr₁₂ (by simpa [e₁, e₂] using hv)
  have he₀₂ : e₀ ≠ e₂ := by
    intro h
    have hv := congrArg
      (fun e : { φ : CubicField P →+* ℂ //
        NumberField.ComplexEmbedding.IsReal φ } ↦ (e.1 (thetaZero P)).re) h
    exact hr₀₂ (by simpa [e₀, e₂] using hv)
  let e : Fin 3 → { φ : CubicField P →+* ℂ //
      NumberField.ComplexEmbedding.IsReal φ } := ![e₀, e₁, e₂]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have hcard : 3 ≤ Fintype.card { φ : CubicField P →+* ℂ //
      NumberField.ComplexEmbedding.IsReal φ } := by
    simpa using Fintype.card_le_of_injective e he
  rw [NumberField.InfinitePlace.card_real_embeddings] at hcard
  have hsignature :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (CubicField P)
  rw [field_finrank] at hsignature
  apply NumberField.nrComplexPlaces_eq_zero_iff.mp
  omega

noncomputable instance (P : Parameters) :
    NumberField.IsTotallyReal (CubicField P) :=
  cubicField_isTotallyReal P

noncomputable def rootPlaceEquiv (P : Parameters) :
    Fin 3 ≃ NumberField.InfinitePlace (CubicField P) :=
  Equiv.ofBijective (rootPlace P) <|
    (Fintype.bijective_iff_injective_and_card (rootPlace P)).mpr ⟨
      rootPlace_injective P, by
        rw [Fintype.card_fin,
          Cusick.CubicOrder.card_infinitePlaces_eq_three (K := CubicField P)]⟩

/-- The first two real places, indexed after omitting the third. -/
noncomputable def firstTwoPlaces (P : Parameters) :
    Fin 2 ≃ {w : NumberField.InfinitePlace (CubicField P) //
      w ≠ rootPlace P 2} := by
  let f : Fin 2 → {w : NumberField.InfinitePlace (CubicField P) //
      w ≠ rootPlace P 2} := fun i ↦
    ⟨rootPlace P i.castSucc, by
      intro h
      have := rootPlace_injective P h
      have hval := congrArg Fin.val this
      fin_cases i <;> norm_num at hval⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    apply Fin.castSucc_injective
    exact rootPlace_injective P (Subtype.ext_iff.mp h)
  · rintro ⟨w, hw⟩
    obtain ⟨i, rfl⟩ := (rootPlaceEquiv P).surjective w
    have hi : i ≠ 2 := by
      intro hi
      apply hw
      change rootPlace P i = rootPlace P 2
      rw [hi]
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact (hi rfl).elim

/-- Auxiliary fact `thetaZero_definingPolynomialQ` used in the proof of the surrounding result from the preprint. -/
lemma thetaZero_definingPolynomialQ (P : Parameters) :
    Polynomial.aeval (thetaZero P) (definingPolynomialQ P.a₁ P.a₂) = 0 := by
  change Polynomial.eval₂ (AdjoinRoot.of _) (AdjoinRoot.root _)
    (definingPolynomialQ P.a₁ P.a₂) = 0
  exact AdjoinRoot.eval₂_root _

/-- Auxiliary fact `thetaZero_definingPolynomial` used in the proof of the surrounding result from the preprint. -/
lemma thetaZero_definingPolynomial (P : Parameters) :
    Polynomial.aeval (thetaZero P) (definingPolynomial P.a₁ P.a₂) = 0 := by
  rw [aeval_def]
  have hmap : algebraMap ℤ (CubicField P) =
      (AdjoinRoot.of (definingPolynomialQ P.a₁ P.a₂)).comp (Int.castRingHom ℚ) := by
    ext z
    simp
  rw [hmap, ← Polynomial.eval₂_map]
  change Polynomial.eval₂ _ _ (definingPolynomialQ P.a₁ P.a₂) = 0
  exact AdjoinRoot.eval₂_root _

/-- Auxiliary fact `thetaZero_isIntegral` used in the proof of the surrounding result from the preprint. -/
lemma thetaZero_isIntegral (P : Parameters) : IsIntegral ℤ (thetaZero P) :=
  ⟨definingPolynomial P.a₁ P.a₂, definingPolynomial_monic _ _, thetaZero_definingPolynomial P⟩

/-- Auxiliary fact `thetaZero_unit_relation` used in the proof of the surrounding result from the preprint. -/
lemma thetaZero_unit_relation (P : Parameters) :
    thetaZero P * (thetaZero P - algebraMap ℤ (CubicField P) P.a₁) *
      (thetaZero P - algebraMap ℤ (CubicField P) P.a₂) = 1 := by
  have h := thetaZero_definingPolynomial P
  simp [definingPolynomial, map_mul, map_sub] at h
  exact sub_eq_zero.mp h

/-- The distinguished algebraic integer, as an element of the maximal order. -/
def thetaZeroInteger (P : Parameters) : NumberField.RingOfIntegers (CubicField P) :=
  ⟨thetaZero P, thetaZero_isIntegral P⟩

/-- Auxiliary fact `thetaZeroInteger_minpoly` used in the proof of the surrounding result from the preprint. -/
lemma thetaZeroInteger_minpoly (P : Parameters) :
    minpoly ℤ (thetaZeroInteger P) = definingPolynomial P.a₁ P.a₂ := by
  have hroot : Polynomial.aeval (thetaZeroInteger P)
      (definingPolynomial P.a₁ P.a₂) = 0 := by
    rw [aeval_def]
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_zero, Polynomial.hom_eval₂]
    have hthetaZero : algebraMap (NumberField.RingOfIntegers (CubicField P)) (CubicField P)
        (thetaZeroInteger P) = thetaZero P := by
      unfold thetaZeroInteger
      exact NumberField.RingOfIntegers.map_mk _ _
    rw [hthetaZero]
    simpa [thetaZeroInteger, aeval_def, IsScalarTower.algebraMap_eq ℤ
      (NumberField.RingOfIntegers (CubicField P)) (CubicField P)] using thetaZero_definingPolynomial P
  let hI : IsIntegral ℤ (thetaZeroInteger P) :=
    NumberField.RingOfIntegers.isIntegral _
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hI hroot
  have hqUnit : IsUnit q :=
    (definingPolynomial_irreducible P.three_le P.lt).isUnit_or_isUnit hq |>.resolve_left
      (minpoly.not_isUnit ℤ (thetaZeroInteger P))
  apply Polynomial.eq_of_monic_of_associated (minpoly.monic hI)
    (definingPolynomial_monic P.a₁ P.a₂)
  exact ⟨hqUnit.unit, by simpa [hqUnit.unit_spec] using hq.symm⟩

/-- The monogenic order `ℤ[θ₀]` inside the ring of integers. -/
def orderCarrier (P : Parameters) :
    Subalgebra ℤ (NumberField.RingOfIntegers (CubicField P)) :=
  Algebra.adjoin ℤ ({thetaZeroInteger P} : Set (NumberField.RingOfIntegers (CubicField P)))

/-- The distinguished generator, now viewed inside the monogenic order. -/
def thetaZeroInOrder (P : Parameters) : orderCarrier P :=
  ⟨thetaZeroInteger P, Algebra.subset_adjoin (Set.mem_singleton _)⟩

def thetaZeroSubAOneInOrder (P : Parameters) : orderCarrier P :=
  thetaZeroInOrder P - algebraMap ℤ (orderCarrier P) P.a₁

def thetaZeroSubATwoInOrder (P : Parameters) : orderCarrier P :=
  thetaZeroInOrder P - algebraMap ℤ (orderCarrier P) P.a₂

/-- Auxiliary fact `order_generators_mul` used in the proof of the surrounding result from the preprint. -/
lemma order_generators_mul (P : Parameters) :
    thetaZeroInOrder P * thetaZeroSubAOneInOrder P * thetaZeroSubATwoInOrder P = 1 := by
  apply Subtype.ext
  apply NumberField.RingOfIntegers.ext
  simp only [thetaZeroInOrder, thetaZeroSubAOneInOrder, thetaZeroSubATwoInOrder,
    Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_algebraMap,
    map_mul, map_sub]
  have hthetaZero : algebraMap (NumberField.RingOfIntegers (CubicField P)) (CubicField P)
      (thetaZeroInteger P) = thetaZero P := by
    unfold thetaZeroInteger
    exact NumberField.RingOfIntegers.map_mk _ _
  rw [hthetaZero, ← IsScalarTower.algebraMap_apply ℤ
    (NumberField.RingOfIntegers (CubicField P)) (CubicField P),
    ← IsScalarTower.algebraMap_apply ℤ
      (NumberField.RingOfIntegers (CubicField P)) (CubicField P)]
  exact thetaZero_unit_relation P

/-- The three canonical canonical units. -/
noncomputable def thetaZeroUnit (P : Parameters) : (orderCarrier P)ˣ :=
  Units.mkOfMulEqOne (thetaZeroInOrder P) (thetaZeroSubAOneInOrder P * thetaZeroSubATwoInOrder P) <| by
    simpa [mul_assoc] using order_generators_mul P

noncomputable def thetaZeroSubAOneUnit (P : Parameters) : (orderCarrier P)ˣ :=
  Units.mkOfMulEqOne (thetaZeroSubAOneInOrder P) (thetaZeroSubATwoInOrder P * thetaZeroInOrder P) <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using order_generators_mul P

noncomputable def thetaZeroSubATwoUnit (P : Parameters) : (orderCarrier P)ˣ :=
  Units.mkOfMulEqOne (thetaZeroSubATwoInOrder P) (thetaZeroInOrder P * thetaZeroSubAOneInOrder P) <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using order_generators_mul P

/-- Auxiliary fact `coe_thetaZeroUnit` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_thetaZeroUnit (P : Parameters) :
    (thetaZeroUnit P : orderCarrier P) = thetaZeroInOrder P := rfl

/-- Auxiliary fact `coe_thetaZeroSubOneUnit` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_thetaZeroSubOneUnit (P : Parameters) :
    (thetaZeroSubAOneUnit P : orderCarrier P) = thetaZeroSubAOneInOrder P := rfl

/-- Auxiliary fact `coe_thetaZeroSubTwoUnit` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_thetaZeroSubTwoUnit (P : Parameters) :
    (thetaZeroSubATwoUnit P : orderCarrier P) = thetaZeroSubATwoInOrder P := rfl

/-- The power basis generated by `θ₀` before reindexing its degree by the
explicit equality `deg(f) = 3`. -/
noncomputable def orderPowerBasis (P : Parameters) :
    PowerBasis ℤ (orderCarrier P) := by
  let hI : IsIntegral ℤ (thetaZeroInteger P) :=
    NumberField.RingOfIntegers.isIntegral _
  exact Algebra.adjoin.powerBasis' hI

/-- Auxiliary fact `orderPowerBasis_dim` used in the proof of the surrounding result from the preprint. -/
lemma orderPowerBasis_dim (P : Parameters) : (orderPowerBasis P).dim = 3 := by
  rw [orderPowerBasis, Algebra.adjoin.powerBasis'_dim, thetaZeroInteger_minpoly,
    definingPolynomial_natDegree]

/-- Auxiliary fact `orderPowerBasis_gen` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma orderPowerBasis_gen (P : Parameters) :
    (orderPowerBasis P).gen = thetaZeroInOrder P := by
  unfold orderPowerBasis
  rw [Algebra.adjoin.powerBasis'_gen]
  apply Subtype.ext
  rfl

/-- The power basis `1, θ₀, θ₀²` of the cubic order. -/
noncomputable def orderBasis (P : Parameters) :
    Module.Basis (Fin 3) ℤ (orderCarrier P) :=
  (orderPowerBasis P).basis.reindex (finCongr (orderPowerBasis_dim P))

/-- Auxiliary fact `orderBasis_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma orderBasis_apply (P : Parameters) (i : Fin 3) :
    orderBasis P i = thetaZeroInOrder P ^ (i : ℕ) := by
  simp [orderBasis, PowerBasis.basis_eq_pow]

/-- Auxiliary fact `orderBasis_zero` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma orderBasis_zero (P : Parameters) : orderBasis P 0 = 1 := by
  simp

/-- The three ordered real embeddings restricted to the cubic order. -/
noncomputable def orderEmbedding (P : Parameters) (i : Fin 3) :
    orderCarrier P →+* ℝ :=
  (rootEmbedding P i).comp (algebraMap (orderCarrier P) (CubicField P))

/-- Auxiliary fact `orderEmbedding_orderThetaZero` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma orderEmbedding_orderThetaZero (P : Parameters) (i : Fin 3) :
    orderEmbedding P i (thetaZeroInOrder P) = realRoot P i := by
  change rootEmbedding P i (thetaZero P) = realRoot P i
  simp [rootEmbedding]

/-- Auxiliary fact `orderEmbedding_orderBasis` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma orderEmbedding_orderBasis (P : Parameters) (i j : Fin 3) :
    orderEmbedding P i (orderBasis P j) = realRoot P i ^ (j : ℕ) := by
  rw [orderBasis_apply, map_pow, orderEmbedding_orderThetaZero]

/-- Auxiliary fact `orderEmbedding_zero_injective` used in the proof of the surrounding result from the preprint. -/
lemma orderEmbedding_zero_injective (P : Parameters) :
    Function.Injective (orderEmbedding P 0) :=
  (rootEmbedding P 0).injective.comp
    (FaithfulSMul.algebraMap_injective (orderCarrier P) (CubicField P))

/-- The Minkowski embedding matrix of the power basis. This definition is
kept independent of the dynamical period bridge. -/
noncomputable def orderEmbeddingMatrix (P : Parameters) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j ↦ orderEmbedding P i (orderBasis P j)

/-- Auxiliary fact `orderEmbeddingMatrix_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma orderEmbeddingMatrix_apply (P : Parameters) (i j : Fin 3) :
    orderEmbeddingMatrix P i j = realRoot P i ^ (j : ℕ) := by
  simp [orderEmbeddingMatrix]

/-- Auxiliary fact `orderEmbeddingMatrix_det` used in the proof of the surrounding result from the preprint. -/
lemma orderEmbeddingMatrix_det (P : Parameters) :
    (orderEmbeddingMatrix P).det =
      (root1 P - root0 P) * (root2 P - root0 P) * (root2 P - root1 P) := by
  rw [Matrix.det_fin_three]
  simp [orderEmbeddingMatrix, root0, root1, root2]
  ring

/-- Auxiliary fact `orderEmbeddingMatrix_det_pos` used in the proof of the surrounding result from the preprint. -/
lemma orderEmbeddingMatrix_det_pos (P : Parameters) :
    0 < (orderEmbeddingMatrix P).det := by
  rw [orderEmbeddingMatrix_det]
  exact mul_pos (mul_pos (sub_pos.mpr (roots_strict_order P).1)
    (sub_pos.mpr (lt_trans (roots_strict_order P).1 (roots_strict_order P).2)))
    (sub_pos.mpr (roots_strict_order P).2)

/-- Auxiliary fact `orderEmbeddingMatrix_det_ne_zero` used in the proof of the surrounding result from the preprint. -/
lemma orderEmbeddingMatrix_det_ne_zero (P : Parameters) :
    (orderEmbeddingMatrix P).det ≠ 0 := ne_of_gt (orderEmbeddingMatrix_det_pos P)

/-- The monogenic order as an actual cubic order in the sense used by
the regulator formalization. -/
noncomputable def cubicOrder (P : Parameters) : Cusick.CubicOrder (CubicField P) where
  carrier := orderCarrier P
  basis := orderBasis P

noncomputable def basicUnitFamily (P : Parameters) :
    Fin 2 → (orderCarrier P)ˣ :=
  ![thetaZeroUnit P, thetaZeroSubAOneUnit P]

noncomputable def candidateUnitFamily (P : Parameters) :
    Fin (NumberField.Units.rank (CubicField P)) → (cubicOrder P).carrierˣ :=
  fun i ↦ basicUnitFamily P
    ((finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))) i)

/-- Auxiliary fact `candidateUnitFamily_zero` used in the proof of the surrounding result from the preprint. -/
lemma candidateUnitFamily_zero (P : Parameters) :
    candidateUnitFamily P
      ((finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 0) =
        thetaZeroUnit P := by
  simp [candidateUnitFamily, basicUnitFamily]
  rfl

/-- Auxiliary fact `candidateUnitFamily_one` used in the proof of the surrounding result from the preprint. -/
lemma candidateUnitFamily_one (P : Parameters) :
    candidateUnitFamily P
      ((finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 1) =
        thetaZeroSubAOneUnit P := by
  simp [candidateUnitFamily, basicUnitFamily]
  rfl

/-! ### The order as a localization lattice -/

private lemma orderCarrier_map_eq_adjoin (P : Parameters) :
    (orderCarrier P).map
        (IsScalarTower.toAlgHom ℤ
          (NumberField.RingOfIntegers (CubicField P)) (CubicField P)) =
      Algebra.adjoin ℤ ({thetaZero P} : Set (CubicField P)) := by
  rw [orderCarrier, AlgHom.map_adjoin_singleton]
  congr 2

/-- Auxiliary fact `exists_orderCarrier_mul_int_eq` used in the proof of the surrounding result from the preprint. -/
private lemma exists_orderCarrier_mul_int_eq (P : Parameters) (z : CubicField P) :
    ∃ (x : orderCarrier P) (d : ℤ), d ≠ 0 ∧
      z * algebraMap ℤ (CubicField P) d =
        algebraMap (orderCarrier P) (CubicField P) x := by
  have hzQ : z ∈ Algebra.adjoin ℚ ({thetaZero P} : Set (CubicField P)) := by
    rw [show Algebra.adjoin ℚ ({thetaZero P} : Set (CubicField P)) = ⊤ by
      exact AdjoinRoot.adjoinRoot_eq_top]
    trivial
  obtain ⟨d, hd⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin
      (nonZeroDivisors ℤ) ℚ ({thetaZero P} : Set (CubicField P)) z hzQ
  have hd0 : (d : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hd' : algebraMap ℤ (CubicField P) (d : ℤ) * z ∈
      Algebra.adjoin ℤ ({thetaZero P} : Set (CubicField P)) := by
    simpa only [Submonoid.smul_def, Algebra.smul_def] using hd
  rw [← orderCarrier_map_eq_adjoin P] at hd'
  obtain ⟨x, hx, hxeq⟩ := Subalgebra.mem_map.mp hd'
  refine ⟨⟨x, hx⟩, d, hd0, ?_⟩
  rw [mul_comm]
  exact hxeq.symm

noncomputable local instance orderCarrier_isLocalization (P : Parameters) :
    IsLocalization
      (Algebra.algebraMapSubmonoid (orderCarrier P) (nonZeroDivisors ℤ))
      (CubicField P) := by
  apply (isLocalization_iff _ _).mpr
  refine ⟨fun y ↦ ?_, fun z ↦ ?_, ?_⟩
  ·
    obtain ⟨d, hd, hdy⟩ := y.property
    change IsUnit (algebraMap (orderCarrier P) (CubicField P) (y : orderCarrier P))
    rw [← hdy]
    change IsUnit (algebraMap ℤ (CubicField P) d)
    exact (map_ne_zero_of_mem_nonZeroDivisors _
      (FaithfulSMul.algebraMap_injective ℤ (CubicField P)) hd).isUnit
  ·
    obtain ⟨x, d, hd, hzx⟩ := exists_orderCarrier_mul_int_eq P z
    let d' : nonZeroDivisors ℤ := ⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩
    let e : Algebra.algebraMapSubmonoid (orderCarrier P) (nonZeroDivisors ℤ) :=
      ⟨algebraMap ℤ (orderCarrier P) d,
        Algebra.mem_algebraMapSubmonoid_of_mem d'⟩
    refine ⟨(x, e), ?_⟩
    simpa [e, IsScalarTower.algebraMap_apply ℤ (orderCarrier P) (CubicField P)] using hzx
  · intro x y hxy
    have hxy' : x = y := by
      exact FaithfulSMul.algebraMap_injective (orderCarrier P) (CubicField P) hxy
    subst y
    exact ⟨1, by simp⟩

end CubicOrderFamily


/-!
# Fundamental units in the family of cubic orders

This section formalizes Proposition 3.4 of the paper. Its proof follows the
paper's regulator-index argument: compute the regulator of the two canonical
units, compare it with Cusick's discriminant lower bound, and use integrality
of the lattice index.
-/

noncomputable section

namespace CubicOrderFamily

open scoped NumberField
open NumberField NumberField.Units

namespace FundamentalUnits

variable (P : Parameters)

/-! ## Exact formulas -/

/-- The positive Vandermonde product of the three ordered roots. -/
def rootDiscriminant : ℝ :=
  (root1 P - root0 P) * (root2 P - root0 P) * (root2 P - root1 P)

/-- Auxiliary fact `rootDiscriminant_pos` used in the proof of the surrounding result from the preprint. -/
lemma rootDiscriminant_pos : 0 < rootDiscriminant P := by
  unfold rootDiscriminant
  exact mul_pos
    (mul_pos (sub_pos.mpr (roots_strict_order P).1)
      (sub_pos.mpr (lt_trans (roots_strict_order P).1
        (roots_strict_order P).2)))
    (sub_pos.mpr (roots_strict_order P).2)

/-- Auxiliary fact `rootDiscriminant_eq_embeddingMatrix_det` used in the proof of the surrounding result from the preprint. -/
lemma rootDiscriminant_eq_embeddingMatrix_det :
    rootDiscriminant P = (orderEmbeddingMatrix P).det := by
  rw [orderEmbeddingMatrix_det]
  rfl

/-- Auxiliary fact `rootPlace_embedding_thetaZero` used in the proof of the surrounding result from the preprint. -/
lemma rootPlace_embedding_thetaZero (i : Fin 3) :
    (rootPlace P i).embedding (thetaZero P) = (realRoot P i : ℂ) := by
  have h := NumberField.InfinitePlace.embedding_mk_eq_of_isReal
    (complexOfRealEmbedding (rootEmbedding P i)).property
  have hx := DFunLike.congr_fun h (thetaZero P)
  simpa [rootPlace, complexOfRealEmbedding, rootEmbedding] using hx

/-- Auxiliary fact `coe_thetaZeroInteger_cubicField` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_thetaZeroInteger_cubicField :
    algebraMap (NumberField.RingOfIntegers (CubicField P)) (CubicField P)
      (thetaZeroInteger P) = thetaZero P := by
  unfold thetaZeroInteger
  exact NumberField.RingOfIntegers.map_mk _ _

open scoped Classical in
/-- Exact discriminant formula for the power basis `1, θ₀, θ₀²`. -/
lemma powerBasis_discriminant_cast :
    ((Algebra.discr ℤ (fun i : Fin 3 ↦
        (thetaZeroInteger P : NumberField.RingOfIntegers (CubicField P)) ^
          (i : ℕ))).natAbs : ℝ) =
      rootDiscriminant P ^ 2 := by
  let K := CubicField P
  let x : K := thetaZero P
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
    simpa [x] using rootPlace_embedding_thetaZero P j
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
    (K := CubicField P)
    (fun i : Fin 3 ↦
      (thetaZeroInteger P : NumberField.RingOfIntegers (CubicField P)) ^ (i : ℕ))
  have hdiscR :
      ((Algebra.discr ℤ (fun i : Fin 3 ↦
        (thetaZeroInteger P : NumberField.RingOfIntegers (CubicField P)) ^
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
          NumberField.RingOfIntegers (CubicField P)) =
        thetaZeroInteger P ^ (i : ℕ) := by
    change ((orderBasis P i : orderCarrier P) :
      NumberField.RingOfIntegers (CubicField P)) = _
    rw [orderBasis_apply]
    rfl
  simp_rw [hb]
  exact powerBasis_discriminant_cast P

/-- The candidate units after inclusion in the maximal order. -/
def mappedCandidate :
    Fin (NumberField.Units.rank (CubicField P)) →
      (NumberField.RingOfIntegers (CubicField P))ˣ :=
  (cubicOrder P).mapUnitFamily (candidateUnitFamily P)

/-- Auxiliary fact `rootPlace_unitMap_thetaZero` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma rootPlace_unitMap_thetaZero (i : Fin 3) :
    rootPlace P i
      (((cubicOrder P).unitMap (thetaZeroUnit P) :
        NumberField.RingOfIntegers (CubicField P)) : CubicField P) =
      realRoot P i := by
  have hv :
      ((cubicOrder P).unitMap (thetaZeroUnit P) :
        NumberField.RingOfIntegers (CubicField P)) = thetaZeroInteger P := by
    rfl
  rw [hv]
  exact rootPlace_thetaZero P i

/-- Auxiliary fact `rootPlace_unitMap_thetaZeroSubOne` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma rootPlace_unitMap_thetaZeroSubOne (i : Fin 3) :
    rootPlace P i
      (((cubicOrder P).unitMap (thetaZeroSubAOneUnit P) :
        NumberField.RingOfIntegers (CubicField P)) : CubicField P) =
      |realRoot P i - (P.a₁ : ℝ)| := by
  have hv :
      ((cubicOrder P).unitMap (thetaZeroSubAOneUnit P) :
        NumberField.RingOfIntegers (CubicField P)) =
      thetaZeroInteger P - algebraMap ℤ
        (NumberField.RingOfIntegers (CubicField P)) P.a₁ := by
    rfl
  rw [hv]
  rw [rootPlace, NumberField.InfinitePlace.apply]
  rw [show ((thetaZeroInteger P -
      algebraMap ℤ (NumberField.RingOfIntegers (CubicField P)) P.a₁ :
        NumberField.RingOfIntegers (CubicField P)) : CubicField P) =
      thetaZero P - algebraMap ℤ (CubicField P) P.a₁ by simp]
  simp only [complexOfRealEmbedding_apply]
  rw [map_sub]
  simp [rootEmbedding]
  convert Complex.norm_real (realRoot P i - (P.a₁ : ℝ)) using 1 <;> simp

/-- The four positive logarithms occurring in the paper's determinant. -/
def xLog : ℝ := Real.log ((P.a₁ : ℝ) - root0 P)
def yLog : ℝ := Real.log ((P.a₂ : ℝ) - root0 P)
def uLog : ℝ := Real.log (root1 P)
def vLog : ℝ := Real.log ((P.a₂ : ℝ) - root1 P)

/-- The exact regulator expression for `⟨θ₀, θ₀-a₁⟩`. -/
def candidateRegulatorExpression : ℝ :=
  xLog P * vLog P + yLog P * uLog P + yLog P * vLog P

/-- Auxiliary fact `root0_product_eq_one` used in the proof of the surrounding result from the preprint. -/
lemma root0_product_eq_one :
    root0 P * ((P.a₁ : ℝ) - root0 P) *
      ((P.a₂ : ℝ) - root0 P) = 1 := by
  have h := realRoot_root P 0
  rw [Polynomial.IsRoot, definingPolynomialR_eval] at h
  change root0 P * (root0 P - (P.a₁ : ℝ)) *
    (root0 P - (P.a₂ : ℝ)) - 1 = 0 at h
  nlinarith

/-- Auxiliary fact `root1_product_eq_one` used in the proof of the surrounding result from the preprint. -/
lemma root1_product_eq_one :
    root1 P * ((P.a₁ : ℝ) - root1 P) *
      ((P.a₂ : ℝ) - root1 P) = 1 := by
  have h := realRoot_root P 1
  rw [Polynomial.IsRoot, definingPolynomialR_eval] at h
  change root1 P * (root1 P - (P.a₁ : ℝ)) *
    (root1 P - (P.a₂ : ℝ)) - 1 = 0 at h
  nlinarith

/-- Auxiliary fact `log_root0_eq` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `log_root1_sub_a₁_eq` used in the proof of the surrounding result from the preprint. -/
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
  let eRank : Fin (NumberField.Units.rank (CubicField P)) ≃ Fin 2 :=
    finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))
  let ePlaces : {w : NumberField.InfinitePlace (CubicField P) //
      w ≠ rootPlace P 2} ≃ Fin (NumberField.Units.rank (CubicField P)) :=
    (firstTwoPlaces P).symm.trans eRank.symm
  rw [NumberField.Units.regOfFamily_eq_det (mappedCandidate P)
    (rootPlace P 2) ePlaces]
  congr 1
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j ↦
    (((firstTwoPlaces P) j).val.mult : ℝ) *
      Real.log (((firstTwoPlaces P) j).val
        ((mappedCandidate P (ePlaces ((firstTwoPlaces P) i)) :
          NumberField.RingOfIntegers (CubicField P)) : CubicField P))
  have hdet :
      (Matrix.of fun i w : {w : NumberField.InfinitePlace (CubicField P) //
        w ≠ rootPlace P 2} ↦ (w.val.mult : ℝ) *
          Real.log (w.val
            ((mappedCandidate P (ePlaces i) :
              NumberField.RingOfIntegers (CubicField P)) : CubicField P))).det =
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
    rootPlace_unitMap_thetaZero, rootPlace_unitMap_thetaZeroSubOne]
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

/-- Auxiliary fact `candidateRegulatorExpression_pos` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `mappedCandidate_isMaxRank` used in the proof of the surrounding result from the preprint. -/
theorem mappedCandidate_isMaxRank :
    NumberField.Units.IsMaxRank (mappedCandidate P) := by
  rw [← NumberField.Units.regOfFamily_ne_zero_iff]
  rw [candidate_regulator_exact P,
    abs_of_pos (candidateRegulatorExpression_pos P)]
  exact (candidateRegulatorExpression_pos P).ne'

/-! ## The regulator-index argument -/

/-- The subgroup generated by the candidate units, together with torsion. -/
def candidateSubgroup : Subgroup
    (NumberField.RingOfIntegers (CubicField P))ˣ :=
  Subgroup.closure (Set.range (mappedCandidate P)) ⊔
    NumberField.Units.torsion (CubicField P)

/-- Auxiliary fact `candidateSubgroup_le_orderUnits` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `candidate_regulator_div_order_regulator` used in the proof of the surrounding result from the preprint. -/
theorem candidate_regulator_div_order_regulator :
    NumberField.Units.regOfFamily (mappedCandidate P) /
        (cubicOrder P).regulator = (candidateIndex P : ℝ) := by
  let U := candidateSubgroup P
  let V := (cubicOrder P).unitSubgroup
  have hV : V.FiniteIndex := inferInstance
  have hle : U ≤ V := candidateSubgroup_le_orderUnits P
  rw [Cusick.CubicOrder.regulator]
  have hreg0 : NumberField.Units.regulator (CubicField P) ≠ 0 :=
    (NumberField.Units.regulator_pos (CubicField P)).ne'
  calc
    NumberField.Units.regOfFamily (mappedCandidate P) /
        ((V.index : ℝ) * NumberField.Units.regulator (CubicField P)) =
        (NumberField.Units.regOfFamily (mappedCandidate P) /
          NumberField.Units.regulator (CubicField P)) / (V.index : ℝ) := by
            field_simp
    _ = (U.index : ℝ) / (V.index : ℝ) := by
      rw [NumberField.Units.regOfFamily_div_regulator]
      rfl
    _ = (candidateIndex P : ℝ) := by
      have hVind : (V.index : ℝ) ≠ 0 := by
        exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := V))
      rw [div_eq_iff hVind]
      exact_mod_cast (Subgroup.relIndex_mul_index hle).symm

/-- Cusick's inequality in the exact order discriminant variables. -/
theorem cusick_lower_bound_for_order :
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

/-- Auxiliary fact `gap_one_le` used in the proof of the surrounding result from the preprint. -/
lemma gap_one_le : 1 ≤ gap P := by
  have h : P.a₁ + 1 ≤ P.a₂ := Int.add_one_le_iff.mpr P.lt
  have hr : (P.a₁ : ℝ) + 1 ≤ P.a₂ := by exact_mod_cast h
  unfold gap
  linarith

/-- Auxiliary fact `a_pos` used in the proof of the surrounding result from the preprint. -/
lemma a_pos : 0 < (P.a₁ : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 3) P.three_le)

/-- Auxiliary fact `b_pos` used in the proof of the surrounding result from the preprint. -/
lemma b_pos : 0 < (P.a₂ : ℝ) := by
  exact lt_trans (a_pos P) (by exact_mod_cast P.lt)

/-- Auxiliary fact `gap_pos` used in the proof of the surrounding result from the preprint. -/
lemma gap_pos : 0 < gap P := lt_of_lt_of_le zero_lt_one (gap_one_le P)

/-- Auxiliary fact `xLog_le_aLog` used in the proof of the surrounding result from the preprint. -/
lemma xLog_le_aLog : xLog P ≤ aLog P := by
  unfold xLog aLog
  apply Real.log_le_log
  · have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root0_strictBounds P).2]
  · linarith [(root0_strictBounds P).1]

/-- Auxiliary fact `yLog_le_bLog` used in the proof of the surrounding result from the preprint. -/
lemma yLog_le_bLog : yLog P ≤ bLog P := by
  unfold yLog bLog
  apply Real.log_le_log
  · have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    have hab : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith [(root0_strictBounds P).2]
  · linarith [(root0_strictBounds P).1]

/-- Auxiliary fact `uLog_le_aLog` used in the proof of the surrounding result from the preprint. -/
lemma uLog_le_aLog : uLog P ≤ aLog P := by
  unfold uLog aLog
  exact Real.log_le_log (by
    have ha : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root1_strictBounds P).1]) (root1_strictBounds P).2.le

/-- Auxiliary fact `vLog_le_gapLog_add_log_two` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `aLog_lt_bLog` used in the proof of the surrounding result from the preprint. -/
lemma aLog_lt_bLog : aLog P < bLog P := by
  unfold aLog bLog
  exact Real.log_lt_log (a_pos P) (by exact_mod_cast P.lt)

/-- Auxiliary fact `candidateRegulatorExpression_le_logMajorant` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `rootDiscriminant_gt_product_div_four` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `log_discriminant_lower` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `logMajorant_lt_half_square` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `candidateExpression_lt_one_eighth_log_discriminant_sq` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `candidate_regulator_lt_twice_order_regulator` used in the proof of the surrounding result from the preprint. -/
theorem candidate_regulator_lt_twice_order_regulator
    (ha : 10 < aLog P) (hg : 10 < gapLog P) :
    NumberField.Units.regOfFamily (mappedCandidate P) <
      2 * (cubicOrder P).regulator := by
  have hc := candidateExpression_lt_one_eighth_log_discriminant_sq P ha hg
  have hcusick := cusick_lower_bound_for_order P
  rw [candidate_regulator_exact P,
    abs_of_pos (candidateRegulatorExpression_pos P)]
  nlinarith

/-- Auxiliary fact `candidateIndex_lt_two_of_large` used in the proof of the surrounding result from the preprint. -/
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
    ∃ m n : ℤ, ∃ z : (NumberField.RingOfIntegers (CubicField P))ˣ,
      z ∈ NumberField.Units.torsion (CubicField P) ∧
      (cubicOrder P).unitMap u =
        (cubicOrder P).unitMap (thetaZeroUnit P) ^ m *
          (cubicOrder P).unitMap (thetaZeroSubAOneUnit P) ^ n * z := by
  have huO : (cubicOrder P).unitMap u ∈
      (cubicOrder P).unitSubgroup := ⟨u, rfl⟩
  change candidateSubgroup P = (cubicOrder P).unitSubgroup at hfund
  have huC : (cubicOrder P).unitMap u ∈ candidateSubgroup P := by
    rw [hfund]
    exact huO
  obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup.mp huC)
  obtain ⟨a, ha⟩ := Subgroup.exists_of_mem_closure_range
    (mappedCandidate P) y hy
  let eRank : Fin (NumberField.Units.rank (CubicField P)) ≃ Fin 2 :=
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
          (cubicOrder P).unitMap (thetaZeroUnit P) ^ m *
            (cubicOrder P).unitMap (thetaZeroSubAOneUnit P) ^ n ∨
      (cubicOrder P).unitMap u =
        -((cubicOrder P).unitMap (thetaZeroUnit P) ^ m *
            (cubicOrder P).unitMap (thetaZeroSubAOneUnit P) ^ n) := by
  obtain ⟨m, n, z, hz, hu⟩ := unitMap_eq_candidates_mul_torsion P hfund u
  have hz' := NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
    (Cusick.CubicOrder.degree_odd (K := CubicField P)) ⟨z, hz⟩
  have hzval : z = 1 ∨ z = -1 := by simpa using hz'
  refine ⟨m, n, ?_⟩
  rcases hzval with rfl | rfl
  · left
    simpa using hu
  · right
    simpa using hu

/-- The literal equality inside the cubic order's unit group.  This is the
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
theorem orderUnit_eq_thetaZeroUnits_or_neg
    (hfund : (cubicOrder P).IsFundamentalFamily
      (candidateUnitFamily P))
    (u : (orderCarrier P)ˣ) :
    ∃ m n : ℤ,
      u = thetaZeroUnit P ^ m * thetaZeroSubAOneUnit P ^ n ∨
      u = -(thetaZeroUnit P ^ m * thetaZeroSubAOneUnit P ^ n) := by
  let u' : (cubicOrder P).carrierˣ := by
    change (orderCarrier P)ˣ
    exact u
  obtain ⟨m, n, hu | hu⟩ := unit_eq_candidateFamily_or_neg P hfund u'
  · refine ⟨m, n, Or.inl ?_⟩
    rw [candidateUnitFamily_zero, candidateUnitFamily_one] at hu
    change u = thetaZeroUnit P ^ m * thetaZeroSubAOneUnit P ^ n at hu
    exact hu
  · refine ⟨m, n, Or.inr ?_⟩
    rw [candidateUnitFamily_zero, candidateUnitFamily_one] at hu
    change u = -(thetaZeroUnit P ^ m * thetaZeroSubAOneUnit P ^ n) at hu
    exact hu

/-- The same decomposition after applying Dirichlet's logarithmic embedding;
the torsion factor disappears. -/
theorem logEmbedding_unitMap_eq_zsmul_candidates
    (hfund : (cubicOrder P).IsFundamentalFamily
      (candidateUnitFamily P))
    (u : (cubicOrder P).carrierˣ) :
    ∃ m n : ℤ,
      NumberField.Units.logEmbedding (CubicField P)
          (Additive.ofMul ((cubicOrder P).unitMap u)) =
        m • NumberField.Units.logEmbedding (CubicField P)
            (Additive.ofMul ((cubicOrder P).unitMap (thetaZeroUnit P))) +
          n • NumberField.Units.logEmbedding (CubicField P)
            (Additive.ofMul
              ((cubicOrder P).unitMap (thetaZeroSubAOneUnit P))) := by
  obtain ⟨m, n, z, hz, hu⟩ := unitMap_eq_candidates_mul_torsion P hfund u
  refine ⟨m, n, ?_⟩
  rw [hu]
  have hzlog : NumberField.Units.logEmbedding (CubicField P)
      (Additive.ofMul z) = 0 := by
    exact NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr hz
  simp [hzlog]

end FundamentalUnits

end CubicOrderFamily


/-!
# Scalar suborders of the cubic order

For a positive natural number `q`, `scalarSuborder P q` is the order
`ℤ + q ℤ[θ₀]`. Its displayed basis is `1, qθ₀, qθ₀²`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ScalarSuborders

open CubicOrderFamily

/-- The scalar suborder `ℤ + q O` of the cubic order `O = ℤ[θ₀]`. -/
def scalarSuborder (P : Parameters) (q : ℕ) :
    Subalgebra ℤ (orderCarrier P) where
  carrier := {x | ∃ a : ℤ, ∃ y : orderCarrier P,
    x = algebraMap ℤ (orderCarrier P) a + q • y}
  algebraMap_mem' a := ⟨a, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, u, rfl⟩ ⟨b, v, rfl⟩
    refine ⟨a + b, u + v, ?_⟩
    simp only [map_add, nsmul_add]
    abel
  mul_mem' := by
    rintro x y ⟨a, u, rfl⟩ ⟨b, v, rfl⟩
    refine ⟨a * b,
      algebraMap ℤ (orderCarrier P) a * v +
        algebraMap ℤ (orderCarrier P) b * u + q • (u * v), ?_⟩
    simp only [map_mul, nsmul_add, nsmul_eq_mul]
    ring

/-- Auxiliary fact `mem_scalarSuborder_iff` used in the proof of the surrounding result from the preprint. -/
lemma mem_scalarSuborder_iff (P : Parameters) (q : ℕ) (x : orderCarrier P) :
    x ∈ scalarSuborder P q ↔
      ∃ a : ℤ, ∃ y : orderCarrier P,
        x = algebraMap ℤ (orderCarrier P) a + q • y :=
  Iff.rfl

/-- Coordinate form of membership in `ℤ + qO`: the `θ₀` and `θ₀²`
coordinates are divisible by `q`. -/
lemma mem_scalarSuborder_iff_repr_dvd (P : Parameters) (q : ℕ)
    (x : orderCarrier P) :
    x ∈ scalarSuborder P q ↔
      (q : ℤ) ∣ (orderBasis P).repr x 1 ∧
        (q : ℤ) ∣ (orderBasis P).repr x 2 := by
  constructor
  · rintro ⟨a, y, rfl⟩
    have ha : algebraMap ℤ (orderCarrier P) a = a • orderBasis P 0 := by
      rw [orderBasis_zero]
      simp [Algebra.smul_def]
    constructor
    · refine ⟨(orderBasis P).repr y 1, ?_⟩
      simp only [map_add, map_nsmul]
      have ha1 : (orderBasis P).repr
          (algebraMap ℤ (orderCarrier P) a) 1 = 0 := by
        rw [ha, map_zsmul]
        change a * (orderBasis P).repr (orderBasis P 0) 1 = 0
        have hcoord : (orderBasis P).repr (orderBasis P 0) 1 = 0 := by
          have h := congrArg (fun z : Fin 3 →₀ ℤ => z 1)
            ((orderBasis P).repr_self 0)
          simpa only [Finsupp.single_apply, if_neg (by decide : (0 : Fin 3) ≠ 1)]
            using h
        rw [hcoord, mul_zero]
      change (orderBasis P).repr (algebraMap ℤ (orderCarrier P) a) 1 +
          (q : ℤ) * (orderBasis P).repr y 1 =
        (q : ℤ) * (orderBasis P).repr y 1
      rw [ha1, zero_add]
    · refine ⟨(orderBasis P).repr y 2, ?_⟩
      simp only [map_add, map_nsmul]
      have ha2 : (orderBasis P).repr
          (algebraMap ℤ (orderCarrier P) a) 2 = 0 := by
        rw [ha, map_zsmul]
        change a * (orderBasis P).repr (orderBasis P 0) 2 = 0
        have hcoord : (orderBasis P).repr (orderBasis P 0) 2 = 0 := by
          have h := congrArg (fun z : Fin 3 →₀ ℤ => z 2)
            ((orderBasis P).repr_self 0)
          simpa only [Finsupp.single_apply, if_neg (by decide : (0 : Fin 3) ≠ 2)]
            using h
        rw [hcoord, mul_zero]
      change (orderBasis P).repr (algebraMap ℤ (orderCarrier P) a) 2 +
          (q : ℤ) * (orderBasis P).repr y 2 =
        (q : ℤ) * (orderBasis P).repr y 2
      rw [ha2, zero_add]
  · rintro ⟨⟨d, hd⟩, ⟨e, he⟩⟩
    refine ⟨(orderBasis P).repr x 0,
      d • orderBasis P 1 + e • orderBasis P 2, ?_⟩
    have hzero : algebraMap ℤ (orderCarrier P) ((orderBasis P).repr x 0) =
        (orderBasis P).repr x 0 • orderBasis P 0 := by
      rw [orderBasis_zero]
      simp [Algebra.smul_def]
    calc
      x = ∑ i : Fin 3, (orderBasis P).repr x i • orderBasis P i :=
        ((orderBasis P).sum_repr x).symm
      _ = (orderBasis P).repr x 0 • orderBasis P 0 +
          (orderBasis P).repr x 1 • orderBasis P 1 +
          (orderBasis P).repr x 2 • orderBasis P 2 := by
            rw [Fin.sum_univ_three]
      _ = algebraMap ℤ (orderCarrier P) ((orderBasis P).repr x 0) +
          q • (d • orderBasis P 1 + e • orderBasis P 2) := by
            rw [hzero, hd, he]
            simp only [nsmul_add]
            module

/-- Auxiliary fact `orderThetaZero_pow_three` used in the proof of the surrounding result from the preprint. -/
lemma orderThetaZero_pow_three (P : Parameters) :
    thetaZeroInOrder P ^ 3 =
      1 - algebraMap ℤ (orderCarrier P) (P.a₁ * P.a₂) * thetaZeroInOrder P +
        algebraMap ℤ (orderCarrier P) (P.a₁ + P.a₂) * thetaZeroInOrder P ^ 2 := by
  have h := order_generators_mul P
  simp only [thetaZeroSubAOneInOrder, thetaZeroSubATwoInOrder] at h
  simp only [map_mul, map_add]
  linear_combination h

/-- Auxiliary fact `orderThetaZero_pow_three_eq_basis` used in the proof of the surrounding result from the preprint. -/
lemma orderThetaZero_pow_three_eq_basis (P : Parameters) :
    thetaZeroInOrder P ^ 3 =
      orderBasis P 0 + (-(P.a₁ * P.a₂)) • orderBasis P 1 +
        (P.a₁ + P.a₂) • orderBasis P 2 := by
  rw [orderThetaZero_pow_three]
  simp [orderBasis_apply, Algebra.smul_def]
  ring

/-- Multiplication by `θ₀` in the power basis is the companion matrix of
`X³ - (a₁+a₂)X² + a₁a₂X - 1`. -/
lemma leftMulMatrix_orderThetaZero (P : Parameters) :
    Algebra.leftMulMatrix (orderBasis P) (thetaZeroInOrder P) =
      PrimePowerCalculations.companion ℤ (P.a₁ + P.a₂) (P.a₁ * P.a₂) := by
  have htheta : thetaZeroInOrder P = orderBasis P 1 := by
    simpa using (orderBasis_apply P 1).symm
  have hThetaZeroSq : thetaZeroInOrder P * thetaZeroInOrder P = orderBasis P 2 := by
    rw [orderBasis_apply]
    norm_num
    ring
  have hThetaZeroCube : thetaZeroInOrder P * (thetaZeroInOrder P * thetaZeroInOrder P) =
      orderBasis P 0 + (-(P.a₁ * P.a₂)) • orderBasis P 1 +
        (P.a₁ + P.a₂) • orderBasis P 2 := by
    rw [← orderThetaZero_pow_three_eq_basis P]
    ring
  have hrThetaZero (i : Fin 3) :
      (orderBasis P).repr (thetaZeroInOrder P) i = if i = 1 then 1 else 0 := by
    rw [htheta]
    simp only [Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, one_mul, eq_comm]
  have hrThetaZeroSq (i : Fin 3) :
      (orderBasis P).repr (thetaZeroInOrder P * thetaZeroInOrder P) i =
        if i = 2 then 1 else 0 := by
    rw [hThetaZeroSq]
    simp only [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hrThetaZeroCube (i : Fin 3) :
      (orderBasis P).repr (thetaZeroInOrder P * (thetaZeroInOrder P * thetaZeroInOrder P)) i =
        (if i = 0 then 1 else 0) +
          (-(P.a₁ * P.a₂)) * (if i = 1 then 1 else 0) +
            (P.a₁ + P.a₂) * (if i = 2 then 1 else 0) := by
    rw [hThetaZeroCube, map_add, map_add, map_zsmul, map_zsmul]
    simp only [Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, one_mul, eq_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul, PrimePowerCalculations.companion,
      orderBasis_apply, pow_two, hrThetaZero, hrThetaZeroSq, hrThetaZeroCube]

/-- The family `1, qθ₀, qθ₀²`, regarded as elements of `ℤ + qO`. -/
def scalarSuborderBasisVector (P : Parameters) (q : ℕ) :
    Fin 3 → scalarSuborder P q :=
  ![⟨1, 1, 0, by simp⟩,
    ⟨q • thetaZeroInOrder P, 0, thetaZeroInOrder P, by simp⟩,
    ⟨q • thetaZeroInOrder P ^ 2, 0, thetaZeroInOrder P ^ 2, by simp⟩]

/-- Auxiliary fact `coe_scalarSuborderBasisVector_zero` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_scalarSuborderBasisVector_zero (P : Parameters) (q : ℕ) :
    (scalarSuborderBasisVector P q 0 : orderCarrier P) = 1 := rfl

/-- Auxiliary fact `coe_scalarSuborderBasisVector_one` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_scalarSuborderBasisVector_one (P : Parameters) (q : ℕ) :
    (scalarSuborderBasisVector P q 1 : orderCarrier P) = q • thetaZeroInOrder P := rfl

/-- Auxiliary fact `coe_scalarSuborderBasisVector_two` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_scalarSuborderBasisVector_two (P : Parameters) (q : ℕ) :
    (scalarSuborderBasisVector P q 2 : orderCarrier P) =
      q • thetaZeroInOrder P ^ 2 := rfl

/-- Auxiliary fact `coe_scalarSuborderBasisVector` used in the proof of the surrounding result from the preprint. -/
lemma coe_scalarSuborderBasisVector (P : Parameters) (q : ℕ) (i : Fin 3) :
    (scalarSuborderBasisVector P q i : orderCarrier P) =
      (if i = 0 then 1 else q • orderBasis P i) := by
  fin_cases i <;> simp [scalarSuborderBasisVector]

/-- Auxiliary fact `scalarSuborderBasisVector_linearIndependent` used in the proof of the surrounding result from the preprint. -/
private lemma scalarSuborderBasisVector_linearIndependent
    (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    LinearIndependent ℤ (scalarSuborderBasisVector P q) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have hfOrder :
      ∑ j : Fin 3, f j • (scalarSuborderBasisVector P q j : orderCarrier P) = 0 := by
    exact congrArg (fun x : scalarSuborder P q => (x : orderCarrier P)) hf
  let g : Fin 3 → ℤ := ![f 0, (q : ℤ) * f 1, (q : ℤ) * f 2]
  have hfbasis : ∑ j : Fin 3, g j • orderBasis P j = 0 := by
    rw [Fin.sum_univ_three] at hfOrder ⊢
    simpa [g, scalarSuborderBasisVector, orderBasis_apply, mul_smul,
      nsmul_eq_mul, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using hfOrder
  have hcoord := Fintype.linearIndependent_iff.mp
    (orderBasis P).linearIndependent g hfbasis i
  fin_cases i
  · simpa [g] using hcoord
  · have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    have : (q : ℤ) * f 1 = 0 := by simpa [g] using hcoord
    exact (mul_eq_zero.mp this).resolve_left hqz
  · have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    have : (q : ℤ) * f 2 = 0 := by simpa [g] using hcoord
    exact (mul_eq_zero.mp this).resolve_left hqz

/-- Auxiliary fact `scalarSuborderBasisVector_span` used in the proof of the surrounding result from the preprint. -/
private lemma scalarSuborderBasisVector_span
    (P : Parameters) (q : ℕ) :
    ⊤ ≤ Submodule.span ℤ (Set.range (scalarSuborderBasisVector P q)) := by
  intro x _
  rcases x.property with ⟨a, y, hy⟩
  let c := (orderBasis P).repr y
  have hyBasis : y = ∑ i : Fin 3, c i • orderBasis P i := by
    exact ((orderBasis P).sum_repr y).symm
  have hx : x =
      (a + q * c 0) • scalarSuborderBasisVector P q 0 +
      c 1 • scalarSuborderBasisVector P q 1 +
      c 2 • scalarSuborderBasisVector P q 2 := by
    apply Subtype.ext
    rw [hy]
    simp only [Subalgebra.coe_add, SetLike.val_smul]
    rw [hyBasis, Fin.sum_univ_three]
    simp only [scalarSuborderBasisVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, orderBasis_zero, orderBasis_apply, pow_one,
      Nat.cast_ofNat, nsmul_add, nsmul_eq_mul, zsmul_eq_mul,
      Int.cast_add, Int.cast_mul]
    push_cast
    norm_num
    ring
  rw [hx]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self 0))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self 1))
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self 2))

/-- The integral basis `1, qθ₀, qθ₀²` of `ℤ + qℤ[θ₀]`. -/
def scalarSuborderBasis (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    Module.Basis (Fin 3) ℤ (scalarSuborder P q) :=
  Module.Basis.mk (scalarSuborderBasisVector_linearIndependent P q hq)
    (scalarSuborderBasisVector_span P q)

/-- Auxiliary fact `scalarSuborderBasis_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma scalarSuborderBasis_apply (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) (i : Fin 3) :
    scalarSuborderBasis P q hq i = scalarSuborderBasisVector P q i :=
  Module.Basis.mk_apply _ _ i

/-- The same scalar suborder, now placed directly inside the maximal order. -/
def scalarSuborderInIntegers (P : Parameters) (q : ℕ) :
    Subalgebra ℤ (NumberField.RingOfIntegers (CubicField P)) :=
  (scalarSuborder P q).map (orderCarrier P).val

/-- Inclusion identifies the nested model of the scalar suborder with its
image in the maximal order. -/
def scalarSuborderEquivInIntegers (P : Parameters) (q : ℕ) :
    scalarSuborder P q ≃ₐ[ℤ] scalarSuborderInIntegers P q :=
  Subalgebra.equivMapOfInjective (scalarSuborder P q) (orderCarrier P).val
    (by exact Subtype.val_injective)

/-- `ℤ + qℤ[θ₀]`, bundled as a cubic order for the regulator interface. -/
def scalarCubicOrder (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    Cusick.CubicOrder (CubicField P) where
  carrier := scalarSuborderInIntegers P q
  basis := (scalarSuborderBasis P q hq).map
    (scalarSuborderEquivInIntegers P q).toLinearEquiv

/-- The ordered real embeddings restricted to the scalar suborder. -/
def scalarSuborderEmbedding (P : Parameters) (q : ℕ) (i : Fin 3) :
    scalarSuborder P q →+* ℝ :=
  (orderEmbedding P i).comp (scalarSuborder P q).val

/-- Auxiliary fact `scalarSuborderEmbedding_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma scalarSuborderEmbedding_apply (P : Parameters) (q : ℕ)
    (i : Fin 3) (x : scalarSuborder P q) :
    scalarSuborderEmbedding P q i x = orderEmbedding P i (x : orderCarrier P) :=
  rfl

/-- The Minkowski embedding matrix of the basis `1, qθ₀, qθ₀²`. -/
def scalarSuborderEmbeddingMatrix (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => scalarSuborderEmbedding P q i (scalarSuborderBasis P q hq j)

/-- Auxiliary fact `scalarSuborderEmbeddingMatrix_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma scalarSuborderEmbeddingMatrix_apply (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) (i j : Fin 3) :
    scalarSuborderEmbeddingMatrix P q hq i j =
      if j = 0 then 1 else (q : ℝ) * realRoot P i ^ (j : ℕ) := by
  fin_cases j <;>
    simp [scalarSuborderEmbeddingMatrix, scalarSuborderEmbedding,
      scalarSuborderBasisVector, map_nsmul, orderBasis_apply]

/-- Auxiliary fact `scalarSuborderEmbeddingMatrix_eq` used in the proof of the surrounding result from the preprint. -/
lemma scalarSuborderEmbeddingMatrix_eq (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    scalarSuborderEmbeddingMatrix P q hq =
      orderEmbeddingMatrix P * Matrix.diagonal ![1, (q : ℝ), (q : ℝ)] := by
  ext i j
  fin_cases j <;>
    simp [scalarSuborderEmbeddingMatrix_apply, orderEmbeddingMatrix,
      Matrix.mul_diagonal, mul_comm]

/-- Auxiliary fact `scalarSuborderEmbeddingMatrix_det` used in the proof of the surrounding result from the preprint. -/
lemma scalarSuborderEmbeddingMatrix_det (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    (scalarSuborderEmbeddingMatrix P q hq).det =
      (q : ℝ) ^ 2 * (orderEmbeddingMatrix P).det := by
  rw [scalarSuborderEmbeddingMatrix_eq, Matrix.det_mul, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, pow_two, mul_comm]

/-- Auxiliary fact `scalarSuborderEmbeddingMatrix_det_pos` used in the proof of the surrounding result from the preprint. -/
lemma scalarSuborderEmbeddingMatrix_det_pos (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    0 < (scalarSuborderEmbeddingMatrix P q hq).det := by
  rw [scalarSuborderEmbeddingMatrix_det]
  exact mul_pos (sq_pos_of_ne_zero (by exact_mod_cast hq))
    (orderEmbeddingMatrix_det_pos P)

/-- Auxiliary fact `scalarSuborderEmbeddingMatrix_det_ne_zero` used in the proof of the surrounding result from the preprint. -/
lemma scalarSuborderEmbeddingMatrix_det_ne_zero (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    (scalarSuborderEmbeddingMatrix P q hq).det ≠ 0 :=
  ne_of_gt (scalarSuborderEmbeddingMatrix_det_pos P q hq)

end ScalarSuborders
end CubicPeriodicTori


/-!
# The concrete local unit calculation for the cubic orders

This section formalizes Proposition 4.4 of Dang--Gargava--Li for the primes
`(2,3,5)`.  The proof follows the paper: reduce the three canonical units
locally, use `b₁ b₂ b₃ = 1`, and apply the prime-power calculation of
Lemma 4.2 for the odd primes and Lemma 4.3 at `2`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace SuborderUnitLattice

open CubicOrderFamily ScalarSuborders

/-- The six congruences in Proposition 4.4, specialized to `(2,3,5)`.
The coefficients of an `CubicOrderFamily.Parameters` object are integers, so this
is the integral version of the predicate used by the final CRT construction. -/
def SatisfiesLocalConditions (c d r : ℕ) (a₁ a₂ : ℤ) : Prop :=
  a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c] ∧ a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c] ∧
  a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d] ∧ a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d] ∧
  a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r] ∧ a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]

/-- Reduction modulo `q` of the matrix of multiplication by `x` in the
power basis `(1,θ₀,θ₀²)`. -/
def reducedLeftMulMatrix (P : Parameters) (q : ℕ) (x : orderCarrier P) :
    Matrix (Fin 3) (Fin 3) (ZMod q) :=
  (Algebra.leftMulMatrix (orderBasis P) x).map
    (Int.castRingHom (ZMod q))

/-- Membership in `ℤ + qO` is exactly scalarity of multiplication by the
element after reduction modulo `q`. -/
lemma mem_scalarSuborder_iff_isScalar_reduced
    (P : Parameters) (q : ℕ) (x : orderCarrier P) :
    x ∈ scalarSuborder P q ↔
      PrimePowerCalculations.IsScalar (reducedLeftMulMatrix P q x) := by
  rw [mem_scalarSuborder_iff_repr_dvd]
  change (_ ∣ _ ∧ _ ∣ _) ↔ PrimePowerCalculations.IsScalar
    ((Algebra.leftMulMatrix (orderBasis P) x).map
      (Int.castRingHom (ZMod q)))
  rw [← PrimePowerCalculations.inScalarOrder_matrix_iff_isScalar_map]
  simp [PrimePowerCalculations.InScalarOrder, PrimePowerCalculations.matrixTail,
    Algebra.leftMulMatrix_eq_repr_mul]

/-- Multiplication by the second canonical unit `θ₀-a₁`. -/
lemma leftMulMatrix_orderThetaZeroSubOne (P : Parameters) :
    Algebra.leftMulMatrix (orderBasis P) (thetaZeroSubAOneInOrder P) =
      PrimePowerCalculations.shiftedCompanion ℤ (P.a₁ + P.a₂)
        (P.a₁ * P.a₂) P.a₁ := by
  rw [thetaZeroSubAOneInOrder, map_sub, leftMulMatrix_orderThetaZero]
  unfold PrimePowerCalculations.shiftedCompanion
  rw [AlgHom.commutes]
  rw [Algebra.algebraMap_eq_smul_one]

/-- Multiplication by the third canonical unit `θ₀-a₂`. -/
lemma leftMulMatrix_orderThetaZeroSubTwo (P : Parameters) :
    Algebra.leftMulMatrix (orderBasis P) (thetaZeroSubATwoInOrder P) =
      PrimePowerCalculations.shiftedCompanion ℤ (P.a₁ + P.a₂)
        (P.a₁ * P.a₂) P.a₂ := by
  rw [thetaZeroSubATwoInOrder, map_sub, leftMulMatrix_orderThetaZero]
  unfold PrimePowerCalculations.shiftedCompanion
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

/-- The local multiplication matrix of an canonical unit. -/
def reducedUnitMatrix (P : Parameters) (q : ℕ) (u : (orderCarrier P)ˣ) :
    (Matrix (Fin 3) (Fin 3) (ZMod q))ˣ :=
  reduceMatrixUnitHom q (leftMulUnitHom P u)

/-- Auxiliary fact `coe_reducedUnitMatrix` used in the proof of the surrounding result from the preprint. -/
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
      PrimePowerCalculations.IsScalar
        (reducedUnitMatrix P q u : Matrix (Fin 3) (Fin 3) (ZMod q)) := by
  rw [coe_reducedUnitMatrix]
  exact mem_scalarSuborder_iff_isScalar_reduced P q u

/-- Auxiliary fact `zmod_eq_of_modEq` used in the proof of the surrounding result from the preprint. -/
private lemma zmod_eq_of_modEq (q : ℕ) {a b : ℤ}
    (h : a ≡ b [ZMOD (q : ℤ)]) : (a : ZMod q) = (b : ZMod q) := by
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).2
    (Int.modEq_iff_dvd.mp h)

/-- Auxiliary fact `reduced_orderThetaZero_eq_common_of_zero_one` used in the proof of the surrounding result from the preprint. -/
lemma reduced_orderThetaZero_eq_common_of_zero_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (thetaZeroInOrder P) =
      PrimePowerCalculations.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderThetaZero,
    PrimePowerCalculations.map_companion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 0 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

/-- Auxiliary fact `reduced_orderThetaZero_eq_common_of_one_zero` used in the proof of the surrounding result from the preprint. -/
lemma reduced_orderThetaZero_eq_common_of_one_zero
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (thetaZeroInOrder P) =
      PrimePowerCalculations.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderThetaZero,
    PrimePowerCalculations.map_companion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 0 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

/-- Auxiliary fact `reduced_orderThetaZeroSubOne_eq_five_of_one_one` used in the proof of the surrounding result from the preprint. -/
lemma reduced_orderThetaZeroSubOne_eq_five_of_one_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (thetaZeroSubAOneInOrder P) =
      PrimePowerCalculations.shiftedCompanion (ZMod q) 2 1 1 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderThetaZeroSubOne,
    PrimePowerCalculations.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

/-- Auxiliary fact `reduced_orderThetaZeroSubOne_eq_common_of_zero_one` used in the proof of the surrounding result from the preprint. -/
lemma reduced_orderThetaZeroSubOne_eq_common_of_zero_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (thetaZeroSubAOneInOrder P) =
      PrimePowerCalculations.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderThetaZeroSubOne,
    PrimePowerCalculations.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 0 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  simp [PrimePowerCalculations.shiftedCompanion]

/-- Auxiliary fact `reduced_orderThetaZeroSubTwo_eq_common_of_one_zero` used in the proof of the surrounding result from the preprint. -/
lemma reduced_orderThetaZeroSubTwo_eq_common_of_one_zero
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (thetaZeroSubATwoInOrder P) =
      PrimePowerCalculations.companion (ZMod q) 1 0 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderThetaZeroSubTwo,
    PrimePowerCalculations.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 0 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  simp [PrimePowerCalculations.shiftedCompanion]

/-- Auxiliary fact `reduced_orderThetaZeroSubTwo_eq_five_of_one_one` used in the proof of the surrounding result from the preprint. -/
lemma reduced_orderThetaZeroSubTwo_eq_five_of_one_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedLeftMulMatrix P q (thetaZeroSubATwoInOrder P) =
      PrimePowerCalculations.shiftedCompanion (ZMod q) 2 1 1 := by
  rw [reducedLeftMulMatrix, leftMulMatrix_orderThetaZeroSubTwo,
    PrimePowerCalculations.map_shiftedCompanion]
  have ha₁ := zmod_eq_of_modEq q h₁
  have ha₂ := zmod_eq_of_modEq q h₂
  have ha₁' : (Int.castRingHom (ZMod q)) P.a₁ = 1 := by simpa using ha₁
  have ha₂' : (Int.castRingHom (ZMod q)) P.a₂ = 1 := by simpa using ha₂
  simp only [map_add, map_mul]
  rw [ha₁', ha₂']
  norm_num

/-- Auxiliary fact `common_two_isScalar_pow_iff` used in the proof of the surrounding result from the preprint. -/
private lemma common_two_isScalar_pow_iff (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    PrimePowerCalculations.IsScalar
        (PrimePowerCalculations.companion (ZMod (2 ^ c)) 1 0 ^ n) ↔
      7 * 2 ^ (c - 1) ∣ n := by
  have h := PrimePowerCalculations.integerTwo_power_law c hc n
  rw [PrimePowerCalculations.inScalarOrder_matrix_iff_isScalar_map,
    Matrix.map_pow, PrimePowerCalculations.map_integerCommonMatrix] at h
  exact h

/-- Auxiliary fact `common_three_isScalar_pow_iff` used in the proof of the surrounding result from the preprint. -/
private lemma common_three_isScalar_pow_iff (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    PrimePowerCalculations.IsScalar
        (PrimePowerCalculations.companion (ZMod (3 ^ d)) 1 0 ^ n) ↔
      8 * 3 ^ (d - 1) ∣ n := by
  have h := PrimePowerCalculations.integerThree_power_law d hd n
  rw [PrimePowerCalculations.inScalarOrder_matrix_iff_isScalar_map,
    Matrix.map_pow, PrimePowerCalculations.map_integerCommonMatrix] at h
  exact h

/-- Auxiliary fact `five_isScalar_pow_iff` used in the proof of the surrounding result from the preprint. -/
private lemma five_isScalar_pow_iff (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    PrimePowerCalculations.IsScalar
        (PrimePowerCalculations.shiftedCompanion (ZMod (5 ^ r)) 2 1 1 ^ n) ↔
      24 * 5 ^ (r - 1) ∣ n := by
  have h := PrimePowerCalculations.integerFive_power_law r hr n
  rw [PrimePowerCalculations.inScalarOrder_matrix_iff_isScalar_map,
    Matrix.map_pow, PrimePowerCalculations.map_integerFiveMatrix] at h
  exact h

/-- The `2`-primary instance of Lemma 4.3 for `b₁=θ₀`. -/
theorem thetaZero_nat_power_law_two (P : Parameters) (c : ℕ) (hc : 1 ≤ c)
    (h₁ : P.a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c])
    (h₂ : P.a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c]) (n : ℕ) :
    (((thetaZeroUnit P) ^ n : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (2 ^ c) ↔
      7 * 2 ^ (c - 1) ∣ n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 0 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₂
  have hred := reduced_orderThetaZero_eq_common_of_zero_one P (2 ^ c) h₁' h₂'
  change PrimePowerCalculations.IsScalar
      (reducedUnitMatrix P (2 ^ c) ((thetaZeroUnit P) ^ n)).val ↔ _
  rw [show reducedUnitMatrix P (2 ^ c) ((thetaZeroUnit P) ^ n) =
      (reducedUnitMatrix P (2 ^ c) (thetaZeroUnit P)) ^ n by
        simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]]
  rw [Units.val_pow_eq_pow_val, coe_reducedUnitMatrix,
    coe_thetaZeroUnit, hred]
  exact common_two_isScalar_pow_iff c hc n

/-- The `3`-primary instance of Lemma 4.2 for `b₁=θ₀`. -/
theorem thetaZero_nat_power_law_three (P : Parameters) (d : ℕ) (hd : 1 ≤ d)
    (h₁ : P.a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d])
    (h₂ : P.a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d]) (n : ℕ) :
    (((thetaZeroUnit P) ^ n : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (3 ^ d) ↔
      8 * 3 ^ (d - 1) ∣ n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 0 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₂
  have hred := reduced_orderThetaZero_eq_common_of_one_zero P (3 ^ d) h₁' h₂'
  change PrimePowerCalculations.IsScalar
      (reducedUnitMatrix P (3 ^ d) ((thetaZeroUnit P) ^ n)).val ↔ _
  rw [show reducedUnitMatrix P (3 ^ d) ((thetaZeroUnit P) ^ n) =
      (reducedUnitMatrix P (3 ^ d) (thetaZeroUnit P)) ^ n by
        simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]]
  rw [Units.val_pow_eq_pow_val, coe_reducedUnitMatrix,
    coe_thetaZeroUnit, hred]
  exact common_three_isScalar_pow_iff d hd n

/-- The `5`-primary instance of Lemma 4.2 for `b₂=θ₀-a₁`. -/
theorem thetaZeroSubOne_nat_power_law_five (P : Parameters) (r : ℕ)
    (hr : 1 ≤ r)
    (h₁ : P.a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r])
    (h₂ : P.a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]) (n : ℕ) :
    (((thetaZeroSubAOneUnit P) ^ n : (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (5 ^ r) ↔
      24 * 5 ^ (r - 1) ∣ n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₂
  have hred := reduced_orderThetaZeroSubOne_eq_five_of_one_one
    P (5 ^ r) h₁' h₂'
  change PrimePowerCalculations.IsScalar
      (reducedUnitMatrix P (5 ^ r) ((thetaZeroSubAOneUnit P) ^ n)).val ↔ _
  rw [show reducedUnitMatrix P (5 ^ r) ((thetaZeroSubAOneUnit P) ^ n) =
      (reducedUnitMatrix P (5 ^ r) (thetaZeroSubAOneUnit P)) ^ n by
        simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]]
  rw [Units.val_pow_eq_pow_val, coe_reducedUnitMatrix,
    coe_thetaZeroSubOneUnit, hred]
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

/-- Auxiliary fact `unit_inv_mem_scalarSuborder_iff` used in the proof of the surrounding result from the preprint. -/
lemma unit_inv_mem_scalarSuborder_iff (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) :
    (((u⁻¹ : (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) ↔
      ((u : orderCarrier P) ∈ scalarSuborder P q) := by
  constructor
  · intro h
    have hi := unit_inv_mem_of_mem P q (u⁻¹) h
    simpa using hi
  · exact unit_inv_mem_of_mem P q u

/-- Auxiliary fact `unit_neg_pow_mem_scalarSuborder_iff` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `int_power_law_of_nat` used in the proof of the surrounding result from the preprint. -/
private theorem int_power_law_of_nat
    (P : Parameters) (q N : ℕ) (u : (orderCarrier P)ˣ)
    (hnat : ∀ n : ℕ,
      UnitPowerMembership P q u n ↔ N ∣ n) (z : ℤ) :
    UnitPowerMembership P q u z ↔ (N : ℤ) ∣ z := by
  apply PrimePowerCalculations.int_power_law_of_nat_of_neg
    (UnitPowerMembership P q u) N hnat
  intro n
  exact unit_neg_pow_mem_scalarSuborder_iff P q u n

/-- Integral-exponent `2`-power law, as used in Proposition 4.4. -/
theorem thetaZero_int_power_law_two (P : Parameters) (c : ℕ) (hc : 1 ≤ c)
    (h₁ : P.a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c])
    (h₂ : P.a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c]) (z : ℤ) :
    UnitPowerMembership P (2 ^ c) (thetaZeroUnit P) z ↔
      (7 * 2 ^ (c - 1) : ℤ) ∣ z := by
  exact int_power_law_of_nat P (2 ^ c) (7 * 2 ^ (c - 1))
    (thetaZeroUnit P) (thetaZero_nat_power_law_two P c hc h₁ h₂) z

/-- Integral-exponent `3`-power law, as used in Proposition 4.4. -/
theorem thetaZero_int_power_law_three (P : Parameters) (d : ℕ) (hd : 1 ≤ d)
    (h₁ : P.a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d])
    (h₂ : P.a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d]) (z : ℤ) :
    UnitPowerMembership P (3 ^ d) (thetaZeroUnit P) z ↔
      (8 * 3 ^ (d - 1) : ℤ) ∣ z := by
  exact int_power_law_of_nat P (3 ^ d) (8 * 3 ^ (d - 1))
    (thetaZeroUnit P) (thetaZero_nat_power_law_three P d hd h₁ h₂) z

/-- Integral-exponent `5`-power law, as used in Proposition 4.4. -/
theorem thetaZeroSubOne_int_power_law_five (P : Parameters) (r : ℕ)
    (hr : 1 ≤ r)
    (h₁ : P.a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r])
    (h₂ : P.a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]) (z : ℤ) :
    UnitPowerMembership P (5 ^ r) (thetaZeroSubAOneUnit P) z ↔
      (24 * 5 ^ (r - 1) : ℤ) ∣ z := by
  exact int_power_law_of_nat P (5 ^ r) (24 * 5 ^ (r - 1))
    (thetaZeroSubAOneUnit P) (thetaZeroSubOne_nat_power_law_five P r hr h₁ h₂) z

/-! ### The three local reductions in the proof of Proposition 4.4 -/

private lemma thetaZero_units_product (P : Parameters) :
    thetaZeroUnit P * thetaZeroSubAOneUnit P * thetaZeroSubATwoUnit P = 1 := by
  apply Units.val_injective
  simpa using order_generators_mul P

/-- Auxiliary fact `thetaZeroSubTwoUnit_eq_inv_mul_inv` used in the proof of the surrounding result from the preprint. -/
private lemma thetaZeroSubTwoUnit_eq_inv_mul_inv (P : Parameters) :
    thetaZeroSubATwoUnit P = (thetaZeroUnit P)⁻¹ * (thetaZeroSubAOneUnit P)⁻¹ := by
  have h := thetaZero_units_product P
  have hc : thetaZeroSubATwoUnit P =
      (thetaZeroUnit P * thetaZeroSubAOneUnit P)⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  rw [hc, mul_inv_rev, mul_comm]

/-- Auxiliary fact `scalarSuborder.unit_mul_mem_iff_left` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `scalarSuborder.unit_mul_mem_iff_right` used in the proof of the surrounding result from the preprint. -/
private lemma scalarSuborder.unit_mul_mem_iff_right
    (P : Parameters) (q : ℕ) (u v : (orderCarrier P)ˣ)
    (hu : (u : orderCarrier P) ∈ scalarSuborder P q) :
    (((u * v : (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) ↔
      ((v : orderCarrier P) ∈ scalarSuborder P q) := by
  rw [mul_comm]
  exact scalarSuborder.unit_mul_mem_iff_left P q v u hu

/-- Auxiliary fact `reduced_thetaZero_eq_thetaZeroSubOne_of_zero_one` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_thetaZero_eq_thetaZeroSubOne_of_zero_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (thetaZeroUnit P) =
      reducedUnitMatrix P q (thetaZeroSubAOneUnit P) := by
  apply Units.val_injective
  rw [coe_reducedUnitMatrix, coe_reducedUnitMatrix,
    coe_thetaZeroUnit, coe_thetaZeroSubOneUnit,
    reduced_orderThetaZero_eq_common_of_zero_one P q h₁ h₂,
    reduced_orderThetaZeroSubOne_eq_common_of_zero_one P q h₁ h₂]

/-- Auxiliary fact `reduced_thetaZero_eq_thetaZeroSubTwo_of_one_zero` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_thetaZero_eq_thetaZeroSubTwo_of_one_zero
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (thetaZeroUnit P) =
      reducedUnitMatrix P q (thetaZeroSubATwoUnit P) := by
  apply Units.val_injective
  rw [coe_reducedUnitMatrix, coe_reducedUnitMatrix,
    coe_thetaZeroUnit, coe_thetaZeroSubTwoUnit,
    reduced_orderThetaZero_eq_common_of_one_zero P q h₁ h₂,
    reduced_orderThetaZeroSubTwo_eq_common_of_one_zero P q h₁ h₂]

/-- Auxiliary fact `reduced_thetaZeroSubOne_eq_thetaZeroSubTwo_of_one_one` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_thetaZeroSubOne_eq_thetaZeroSubTwo_of_one_one
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (thetaZeroSubAOneUnit P) =
      reducedUnitMatrix P q (thetaZeroSubATwoUnit P) := by
  apply Units.val_injective
  rw [coe_reducedUnitMatrix, coe_reducedUnitMatrix,
    coe_thetaZeroSubOneUnit, coe_thetaZeroSubTwoUnit,
    reduced_orderThetaZeroSubOne_eq_five_of_one_one P q h₁ h₂,
    reduced_orderThetaZeroSubTwo_eq_five_of_one_one P q h₁ h₂]

/-- Auxiliary fact `reducedUnitMatrix_map_mul` used in the proof of the surrounding result from the preprint. -/
private lemma reducedUnitMatrix_map_mul (P : Parameters) (q : ℕ)
    (u v : (orderCarrier P)ˣ) :
    reducedUnitMatrix P q (u * v) =
      reducedUnitMatrix P q u * reducedUnitMatrix P q v := by
  simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]

/-- Auxiliary fact `reducedUnitMatrix_map_zpow` used in the proof of the surrounding result from the preprint. -/
private lemma reducedUnitMatrix_map_zpow (P : Parameters) (q : ℕ)
    (u : (orderCarrier P)ˣ) (z : ℤ) :
    reducedUnitMatrix P q (u ^ z) = (reducedUnitMatrix P q u) ^ z := by
  simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]

/-- Auxiliary fact `reducedUnitMatrix_map_one` used in the proof of the surrounding result from the preprint. -/
private lemma reducedUnitMatrix_map_one (P : Parameters) (q : ℕ) :
    reducedUnitMatrix P q 1 = 1 := by
  simp [reducedUnitMatrix, reduceMatrixUnitHom, leftMulUnitHom]

/-- Auxiliary fact `reduced_product_two` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_product_two
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 0 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) (m n : ℤ) :
    reducedUnitMatrix P q ((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n) =
      reducedUnitMatrix P q ((thetaZeroUnit P) ^ (m + n)) := by
  rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_zpow,
    reducedUnitMatrix_map_zpow, reducedUnitMatrix_map_zpow,
    ← reduced_thetaZero_eq_thetaZeroSubOne_of_zero_one P q h₁ h₂,
    zpow_add]

/-- Auxiliary fact `reduced_thetaZeroSubOne_eq_thetaZero_neg_two` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_thetaZeroSubOne_eq_thetaZero_neg_two
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (thetaZeroSubAOneUnit P) =
      (reducedUnitMatrix P q (thetaZeroUnit P)) ^ (-2 : ℤ) := by
  let A := reducedUnitMatrix P q (thetaZeroUnit P)
  let B := reducedUnitMatrix P q (thetaZeroSubAOneUnit P)
  let C := reducedUnitMatrix P q (thetaZeroSubATwoUnit P)
  have hAC : A = C := reduced_thetaZero_eq_thetaZeroSubTwo_of_one_zero P q h₁ h₂
  have hprod : A * B * C = 1 := by
    have h := congrArg (fun u => reducedUnitMatrix P q u)
      (thetaZero_units_product P)
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

/-- Auxiliary fact `reduced_product_three` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_product_three
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 0 [ZMOD (q : ℤ)]) (m n : ℤ) :
    reducedUnitMatrix P q ((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n) =
      reducedUnitMatrix P q ((thetaZeroUnit P) ^ (m - 2 * n)) := by
  rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_zpow,
    reducedUnitMatrix_map_zpow, reducedUnitMatrix_map_zpow,
    reduced_thetaZeroSubOne_eq_thetaZero_neg_two P q h₁ h₂]
  rw [← zpow_mul, ← zpow_add]
  congr 2
  ring

/-- Auxiliary fact `reduced_thetaZero_eq_thetaZeroSubOne_neg_two` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_thetaZero_eq_thetaZeroSubOne_neg_two
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) :
    reducedUnitMatrix P q (thetaZeroUnit P) =
      (reducedUnitMatrix P q (thetaZeroSubAOneUnit P)) ^ (-2 : ℤ) := by
  let A := reducedUnitMatrix P q (thetaZeroUnit P)
  let B := reducedUnitMatrix P q (thetaZeroSubAOneUnit P)
  let C := reducedUnitMatrix P q (thetaZeroSubATwoUnit P)
  have hBC : B = C := reduced_thetaZeroSubOne_eq_thetaZeroSubTwo_of_one_one P q h₁ h₂
  have hprod : A * B * C = 1 := by
    have h := congrArg (fun u => reducedUnitMatrix P q u)
      (thetaZero_units_product P)
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

/-- Auxiliary fact `reduced_product_five` used in the proof of the surrounding result from the preprint. -/
private lemma reduced_product_five
    (P : Parameters) (q : ℕ)
    (h₁ : P.a₁ ≡ 1 [ZMOD (q : ℤ)])
    (h₂ : P.a₂ ≡ 1 [ZMOD (q : ℤ)]) (m n : ℤ) :
    reducedUnitMatrix P q ((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n) =
      reducedUnitMatrix P q ((thetaZeroSubAOneUnit P) ^ (n - 2 * m)) := by
  rw [reducedUnitMatrix_map_mul, reducedUnitMatrix_map_zpow,
    reducedUnitMatrix_map_zpow, reducedUnitMatrix_map_zpow,
    reduced_thetaZero_eq_thetaZeroSubOne_neg_two P q h₁ h₂]
  rw [← zpow_mul, ← zpow_add]
  congr 1
  ring

/-- First local line of the `3 × 2` matrix congruence: at `2`, the
congruence `b₁ ≡ b₂` changes `b₁^m b₂^n` into `b₁^(m+n)`. -/
theorem canonical_product_mem_two_iff
    (P : Parameters) (c : ℕ) (hc : 1 ≤ c)
    (h₁ : P.a₁ ≡ 0 [ZMOD (2 : ℤ) ^ c])
    (h₂ : P.a₂ ≡ 1 [ZMOD (2 : ℤ) ^ c]) (m n : ℤ) :
    ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P (2 ^ c)) ↔
      (7 * 2 ^ (c - 1) : ℤ) ∣ m + n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 0 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((2 ^ c : ℕ) : ℤ)] := by simpa using h₂
  have heq := congrArg Units.val
    (reduced_product_two P (2 ^ c) h₁' h₂' m n)
  rw [heq, ← unit_mem_scalarSuborder_iff]
  exact thetaZero_int_power_law_two P c hc h₁ h₂ (m + n)

/-- Second local line of the `3 × 2` matrix congruence.  This is the
paper's use of `b₃=b₁⁻¹b₂⁻¹` together with `b₁ ≡ b₃` at `3`. -/
theorem canonical_product_mem_three_iff
    (P : Parameters) (d : ℕ) (hd : 1 ≤ d)
    (h₁ : P.a₁ ≡ 1 [ZMOD (3 : ℤ) ^ d])
    (h₂ : P.a₂ ≡ 0 [ZMOD (3 : ℤ) ^ d]) (m n : ℤ) :
    ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P (3 ^ d)) ↔
      (8 * 3 ^ (d - 1) : ℤ) ∣ m - 2 * n := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 0 [ZMOD ((3 ^ d : ℕ) : ℤ)] := by simpa using h₂
  have heq := congrArg Units.val
    (reduced_product_three P (3 ^ d) h₁' h₂' m n)
  rw [heq, ← unit_mem_scalarSuborder_iff]
  exact thetaZero_int_power_law_three P d hd h₁ h₂ (m - 2 * n)

/-- Third local line of the `3 × 2` matrix congruence.  This is the
paper's use of `b₃=b₁⁻¹b₂⁻¹` together with `b₂ ≡ b₃` at `5`. -/
theorem canonical_product_mem_five_iff
    (P : Parameters) (r : ℕ) (hr : 1 ≤ r)
    (h₁ : P.a₁ ≡ 1 [ZMOD (5 : ℤ) ^ r])
    (h₂ : P.a₂ ≡ 1 [ZMOD (5 : ℤ) ^ r]) (m n : ℤ) :
    ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P (5 ^ r)) ↔
      (24 * 5 ^ (r - 1) : ℤ) ∣ n - 2 * m := by
  rw [unit_mem_scalarSuborder_iff]
  have h₁' : P.a₁ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₁
  have h₂' : P.a₂ ≡ 1 [ZMOD ((5 ^ r : ℕ) : ℤ)] := by simpa using h₂
  have heq := congrArg Units.val
    (reduced_product_five P (5 ^ r) h₁' h₂' m n)
  rw [heq, ← unit_mem_scalarSuborder_iff]
  exact thetaZeroSubOne_int_power_law_five P r hr h₁ h₂ (n - 2 * m)

/-- Lemma 4.1 for the concrete conductors `2^c,3^d,5^r`. -/
theorem mem_scalarSuborder_product_iff (P : Parameters)
    (c d r : ℕ) (x : orderCarrier P) :
    x ∈ scalarSuborder P (2 ^ c * 3 ^ d * 5 ^ r) ↔
      x ∈ scalarSuborder P (2 ^ c) ∧
      x ∈ scalarSuborder P (3 ^ d) ∧
      x ∈ scalarSuborder P (5 ^ r) := by
  simp only [mem_scalarSuborder_iff_repr_dvd]
  change PrimePowerCalculations.InScalarSuborder
      (((2 ^ c * 3 ^ d * 5 ^ r : ℕ) : ℤ)) ((orderBasis P).repr x) ↔
    PrimePowerCalculations.InScalarSuborder (((2 ^ c : ℕ) : ℤ)) ((orderBasis P).repr x) ∧
    PrimePowerCalculations.InScalarSuborder (((3 ^ d : ℕ) : ℤ)) ((orderBasis P).repr x) ∧
    PrimePowerCalculations.InScalarSuborder (((5 ^ r : ℕ) : ℤ)) ((orderBasis P).repr x)
  have h₂₃ : IsCoprime (((2 ^ c : ℕ) : ℤ)) (((3 ^ d : ℕ) : ℤ)) :=
    ((by decide : Nat.Coprime 2 3).pow c d).isCoprime
  have h₂₅ : IsCoprime (((2 ^ c : ℕ) : ℤ)) (((5 ^ r : ℕ) : ℤ)) :=
    ((by decide : Nat.Coprime 2 5).pow c r).isCoprime
  have h₃₅ : IsCoprime (((3 ^ d : ℕ) : ℤ)) (((5 ^ r : ℕ) : ℤ)) :=
    ((by decide : Nat.Coprime 3 5).pow d r).isCoprime
  simpa only [Nat.cast_mul] using
    (PrimePowerCalculations.inScalarSuborder_mul_three_iff h₂₃ h₂₅ h₃₅
      ((orderBasis P).repr x))

/-- Proposition 4.4 specialized to `(p₁,p₂,p₃)=(2,3,5)` and to the
canonical canonical units.  It identifies membership in the product-conductor
suborder with exactly the three exponent congruences in the paper. -/
theorem canonical_product_mem_iff_exponentConditions
    (P : Parameters) (c d r : ℕ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (hlocal : SatisfiesLocalConditions c d r P.a₁ P.a₂)
    (m n : ℤ) :
    ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P (2 ^ c * 3 ^ d * 5 ^ r)) ↔
      (m, n) ∈ PrimePowerCalculations.ExponentConditions c d r := by
  rcases hlocal with ⟨h₂₁, h₂₂, h₃₁, h₃₂, h₅₁, h₅₂⟩
  rw [mem_scalarSuborder_product_iff,
    canonical_product_mem_two_iff P c hc h₂₁ h₂₂,
    canonical_product_mem_three_iff P d hd h₃₁ h₃₂,
    canonical_product_mem_five_iff P r hr h₅₁ h₅₂]
  simp only [PrimePowerCalculations.ExponentConditions, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h₂, h₃, h₅⟩
    exact ⟨h₂, h₃, by simpa [neg_sub] using h₅.neg_right⟩
  · rintro ⟨h₂, h₃, h₅⟩
    exact ⟨h₂, h₃, by simpa [neg_sub] using h₅.neg_right⟩

/-! ### From a fundamental family to all order units -/

private def orderUnitMap (P : Parameters) :
    (orderCarrier P)ˣ →* (NumberField.RingOfIntegers (CubicField P))ˣ :=
  Units.map (orderCarrier P).val.toRingHom.toMonoidHom

/-- Auxiliary fact `cubicOrder_unitMap_eq_orderUnitMap` used in the proof of the surrounding result from the preprint. -/
private lemma cubicOrder_unitMap_eq_orderUnitMap (P : Parameters) :
    (cubicOrder P).unitMap = orderUnitMap P := rfl

/-- Auxiliary fact `orderUnitMap_injective` used in the proof of the surrounding result from the preprint. -/
private lemma orderUnitMap_injective (P : Parameters) :
    Function.Injective (orderUnitMap P) :=
  Units.map_injective Subtype.val_injective

/-- Auxiliary fact `orderUnitMap_neg_one` used in the proof of the surrounding result from the preprint. -/
@[simp] private lemma orderUnitMap_neg_one (P : Parameters) :
    orderUnitMap P (-1) = -1 := by
  apply Units.val_injective
  rfl

/-- Auxiliary fact `coe_orderUnitMap` used in the proof of the surrounding result from the preprint. -/
@[simp] private lemma coe_orderUnitMap (P : Parameters)
    (u : (orderCarrier P)ˣ) :
    ((orderUnitMap P u :
      (NumberField.RingOfIntegers (CubicField P))ˣ) :
        NumberField.RingOfIntegers (CubicField P)) =
      (u : orderCarrier P) := rfl

/-- Auxiliary fact `coe_orderUnitMap_zpow` used in the proof of the surrounding result from the preprint. -/
@[simp] private lemma coe_orderUnitMap_zpow (P : Parameters)
    (u : (orderCarrier P)ˣ) (z : ℤ) :
    (((orderUnitMap P u) ^ z :
      (NumberField.RingOfIntegers (CubicField P))ˣ) :
        NumberField.RingOfIntegers (CubicField P)) =
      ((u ^ z : (orderCarrier P)ˣ) : orderCarrier P) := by
  exact (congrArg Units.val (map_zpow (orderUnitMap P) u z).symm).trans
    (coe_orderUnitMap P (u ^ z))

private def canonicalImageSubgroup (P : Parameters) :
    Subgroup (NumberField.RingOfIntegers (CubicField P))ˣ where
  carrier := {x | ∃ m n : ℤ,
    x = (orderUnitMap P (thetaZeroUnit P)) ^ m *
      (orderUnitMap P (thetaZeroSubAOneUnit P)) ^ n}
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

/-- Auxiliary fact `closure_candidate_le_canonicalImageSubgroup` used in the proof of the surrounding result from the preprint. -/
private lemma closure_candidate_le_canonicalImageSubgroup (P : Parameters) :
    Subgroup.closure
        (Set.range ((cubicOrder P).mapUnitFamily (candidateUnitFamily P))) ≤
      canonicalImageSubgroup P := by
  apply (Subgroup.closure_le (canonicalImageSubgroup P)).2
  rintro x ⟨i, rfl⟩
  rw [Cusick.CubicOrder.mapUnitFamily, cubicOrder_unitMap_eq_orderUnitMap]
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
that every ambient cubic-order unit is a sign times an integral power product
of the two canonical units, the representation invoked at the start of the
proof of Proposition 4.4. -/
theorem exists_sign_mul_canonical_of_fundamental
    (P : Parameters)
    (hfund : (cubicOrder P).IsFundamentalFamily (candidateUnitFamily P))
    (x : (orderCarrier P)ˣ) :
    ∃ ε : (orderCarrier P)ˣ, (ε = 1 ∨ ε = -1) ∧
      ∃ m n : ℤ,
        x = ε * (thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n := by
  have hxsub : (cubicOrder P).unitMap x ∈ (cubicOrder P).unitSubgroup :=
    ⟨x, rfl⟩
  have hxsup : (cubicOrder P).unitMap x ∈
      Subgroup.closure (Set.range
        ((cubicOrder P).mapUnitFamily (candidateUnitFamily P))) ⊔
        NumberField.Units.torsion (CubicField P) := by
    rw [hfund]
    exact hxsub
  rcases Subgroup.mem_sup.mp hxsup with ⟨y, hy, z, hz, hyz⟩
  have hy' := closure_candidate_le_canonicalImageSubgroup P hy
  rcases hy' with ⟨m, n, rfl⟩
  have hz' := NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
    (Cusick.CubicOrder.degree_odd (K := CubicField P)) ⟨z, hz⟩
  have hzval : z = 1 ∨ z = -1 := by simpa using hz'
  rw [cubicOrder_unitMap_eq_orderUnitMap] at hyz
  rcases hzval with hzval | hzval
  · refine ⟨1, Or.inl rfl, m, n, ?_⟩
    apply Units.ext
    apply Subtype.ext
    have hv := congrArg Units.val hyz.symm
    change (((x : orderCarrier P) :
      NumberField.RingOfIntegers (CubicField P))) = _ at hv
    simpa [hzval, mul_assoc] using hv
  · refine ⟨-1, Or.inr rfl, m, n, ?_⟩
    apply Units.ext
    apply Subtype.ext
    have hv := congrArg Units.val hyz.symm
    change (((x : orderCarrier P) :
      NumberField.RingOfIntegers (CubicField P))) = _ at hv
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
        ∃ m n : ℤ, (m, n) ∈ PrimePowerCalculations.ExponentConditions c d r ∧
          x = ε * (thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n := by
  let q := 2 ^ c * 3 ^ d * 5 ^ r
  constructor
  · intro hx
    obtain ⟨ε, hε, m, n, hxrep⟩ :=
      exists_sign_mul_canonical_of_fundamental P hfund x
    have hεmem : (ε : orderCarrier P) ∈ scalarSuborder P q := by
      rcases hε with hε | hε <;> rw [hε] <;> simp
    have hproduct :
        ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
          (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) := by
      apply (scalarSuborder.unit_mul_mem_iff_right P q ε
        ((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n) hεmem).mp
      rw [hxrep] at hx
      simpa [q, mul_assoc] using hx
    have hexponents : (m, n) ∈ PrimePowerCalculations.ExponentConditions c d r :=
      (canonical_product_mem_iff_exponentConditions P c d r hc hd hr
        hlocal m n).mp hproduct
    exact ⟨ε, hε, m, n, hexponents, hxrep⟩
  · rintro ⟨ε, hε, m, n, hexponents, rfl⟩
    have hεmem : (ε : orderCarrier P) ∈ scalarSuborder P q := by
      rcases hε with hε | hε <;> rw [hε] <;> simp
    have hproduct :
        ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
          (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) :=
      (canonical_product_mem_iff_exponentConditions P c d r hc hd hr
        hlocal m n).mpr hexponents
    simpa [q, mul_assoc] using (scalarSuborder P q).mul_mem hεmem hproduct


end SuborderUnitLattice
end CubicPeriodicTori


/-!
# The explicit CRT family in the final arithmetic construction

This section contains the six local congruences and the separated family of
polynomial parameters used in Section 5.3.
-/

noncomputable section

namespace CubicPeriodicTori

open Filter Set Topology

/-- The six CRT congruences imposed on `(a₁,a₂)` at level `N` in the final
proof. -/
def SatisfiesLocalConditions (N a₁ a₂ : ℕ) : Prop :=
  Nat.ModEq (2 ^ N) a₁ 0 ∧ Nat.ModEq (2 ^ N) a₂ 1 ∧
  Nat.ModEq (3 ^ N) a₁ 1 ∧ Nat.ModEq (3 ^ N) a₂ 0 ∧
  Nat.ModEq (5 ^ N) a₁ 1 ∧ Nat.ModEq (5 ^ N) a₂ 1

/-! ### An explicit CRT family for Section 5.3 -/

private def twoPart (N : ℕ) := 2 ^ N
private def threePart (N : ℕ) := 3 ^ N
private def fivePart (N : ℕ) := 5 ^ N

/-- Auxiliary fact `two_three_coprime` used in the proof of the surrounding result from the preprint. -/
private lemma two_three_coprime (N : ℕ) :
    (twoPart N).Coprime (threePart N) := by
  exact (by decide : Nat.Coprime 2 3).pow N N

/-- Auxiliary fact `two_three_five_coprime` used in the proof of the surrounding result from the preprint. -/
private lemma two_three_five_coprime (N : ℕ) :
    (twoPart N * threePart N).Coprime (fivePart N) := by
  exact Nat.Coprime.mul_left
    ((by decide : Nat.Coprime 2 5).pow N N)
    ((by decide : Nat.Coprime 3 5).pow N N)

private def crt23 (N x2 x3 : ℕ) : ℕ :=
  Nat.chineseRemainder (two_three_coprime N) x2 x3

private def crt235 (N x2 x3 x5 : ℕ) : ℕ :=
  Nat.chineseRemainder (two_three_five_coprime N) (crt23 N x2 x3) x5

/-- Auxiliary fact `crt235_mod_two` used in the proof of the surrounding result from the preprint. -/
private lemma crt235_mod_two (N x2 x3 x5 : ℕ) :
    Nat.ModEq (twoPart N) (crt235 N x2 x3 x5) x2 := by
  have hprod := (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.1
  have h23 := (Nat.chineseRemainder
    (two_three_coprime N) x2 x3).property.1
  exact (hprod.of_dvd (dvd_mul_right (twoPart N) (threePart N))).trans h23

/-- Auxiliary fact `crt235_mod_three` used in the proof of the surrounding result from the preprint. -/
private lemma crt235_mod_three (N x2 x3 x5 : ℕ) :
    Nat.ModEq (threePart N) (crt235 N x2 x3 x5) x3 := by
  have hprod := (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.1
  have h23 := (Nat.chineseRemainder
    (two_three_coprime N) x2 x3).property.2
  exact (hprod.of_dvd (dvd_mul_left (threePart N) (twoPart N))).trans h23

/-- Auxiliary fact `crt235_mod_five` used in the proof of the surrounding result from the preprint. -/
private lemma crt235_mod_five (N x2 x3 x5 : ℕ) :
    Nat.ModEq (fivePart N) (crt235 N x2 x3 x5) x5 :=
  (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.2

/-- The common CRT modulus `2^N 3^N 5^N = 30^N`. -/
def crtModulus (N : ℕ) : ℕ := twoPart N * threePart N * fivePart N

/-- Auxiliary fact `crtModulus_eq` used in the proof of the surrounding result from the preprint. -/
lemma crtModulus_eq (N : ℕ) : crtModulus N = 30 ^ N := by
  simp [crtModulus, twoPart, threePart, fivePart, ← mul_pow]

/-- Auxiliary fact `crtModulus_pos` used in the proof of the surrounding result from the preprint. -/
lemma crtModulus_pos (N : ℕ) : 0 < crtModulus N := by
  rw [crtModulus_eq]
  positivity

/-- Auxiliary fact `crtModulus_tendsto` used in the proof of the surrounding result from the preprint. -/
lemma crtModulus_tendsto : Tendsto crtModulus atTop atTop := by
  convert tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : 1 < (30 : ℕ)) using 1
  funext N
  exact crtModulus_eq N

/-- Auxiliary fact `crt235_lt` used in the proof of the surrounding result from the preprint. -/
private lemma crt235_lt (N x2 x3 x5 : ℕ) :
    crt235 N x2 x3 x5 < crtModulus N := by
  exact Nat.chineseRemainder_lt_mul (two_three_five_coprime N)
    (crt23 N x2 x3) x5 (by simp [twoPart, threePart]) (by simp [fivePart])

/-- The first coefficient in the explicit CRT family.  A quadratic shift
makes the bounded CRT representative negligible after rescaling. -/
def localAOne (N : ℕ) : ℕ := crt235 N 0 1 1 + crtModulus N ^ 2

/-- The second coefficient in the explicit CRT family.  The shift by three
squared moduli makes `a₂-a₁` grow uniformly and forces a deterministic
asymptotic ratio while preserving all congruences. -/
def localATwo (N : ℕ) : ℕ := crt235 N 1 0 1 + 3 * crtModulus N ^ 2

/-- Auxiliary fact `localAOne_bounds` used in the proof of the surrounding result from the preprint. -/
lemma localAOne_bounds (N : ℕ) :
    crtModulus N ^ 2 ≤ localAOne N ∧
      localAOne N < crtModulus N ^ 2 + crtModulus N := by
  constructor
  · simp [localAOne]
  · have hr := crt235_lt N 0 1 1
    dsimp [localAOne]
    omega

/-- Auxiliary fact `localATwo_bounds` used in the proof of the surrounding result from the preprint. -/
lemma localATwo_bounds (N : ℕ) :
    3 * crtModulus N ^ 2 ≤ localATwo N ∧
      localATwo N < 3 * crtModulus N ^ 2 + crtModulus N := by
  constructor
  · simp [localATwo]
  · have hr := crt235_lt N 1 0 1
    dsimp [localATwo]
    omega

/-- Auxiliary fact `local_parameters_ordered` used in the proof of the surrounding result from the preprint. -/
lemma local_parameters_ordered (N : ℕ) :
    3 ≤ localAOne (N + 1) ∧ localAOne (N + 1) < localATwo (N + 1) := by
  have hM : 3 ≤ crtModulus (N + 1) := by
    rw [crtModulus_eq, pow_succ]
    nlinarith [pow_pos (by norm_num : 0 < (30 : ℕ)) N]
  have hMsq : crtModulus (N + 1) ≤ crtModulus (N + 1) ^ 2 := by
    nlinarith
  constructor
  · exact hM.trans (hMsq.trans (localAOne_bounds (N + 1)).1)
  · have hpos := crtModulus_pos (N + 1)
    have h1 := (localAOne_bounds (N + 1)).2
    have h2 := (localATwo_bounds (N + 1)).1
    nlinarith

/-- Auxiliary fact `local_conditions` used in the proof of the surrounding result from the preprint. -/
lemma local_conditions (N : ℕ) :
    SatisfiesLocalConditions N (localAOne N) (localATwo N) := by
  have hm2 : twoPart N ∣ crtModulus N :=
    dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hm3 : threePart N ∣ crtModulus N :=
    dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hm5 : fivePart N ∣ crtModulus N := dvd_mul_left _ _
  constructor
  · have h := (crt235_mod_two N 0 1 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm2).mul_left (crtModulus N))
    simpa [localAOne, twoPart, pow_two] using h
  constructor
  · have h := (crt235_mod_two N 1 0 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm2).mul_left (3 * crtModulus N))
    simpa [localATwo, twoPart, pow_two, Nat.mul_assoc] using h
  constructor
  · have h := (crt235_mod_three N 0 1 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm3).mul_left (crtModulus N))
    simpa [localAOne, threePart, pow_two] using h
  constructor
  · have h := (crt235_mod_three N 1 0 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm3).mul_left (3 * crtModulus N))
    simpa [localATwo, threePart, pow_two, Nat.mul_assoc] using h
  constructor
  · have h := (crt235_mod_five N 0 1 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm5).mul_left (crtModulus N))
    simpa [localAOne, fivePart, pow_two] using h
  · have h := (crt235_mod_five N 1 0 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm5).mul_left (3 * crtModulus N))
    simpa [localATwo, fivePart, pow_two, Nat.mul_assoc] using h

/-- Auxiliary fact `local_separation_lower` used in the proof of the surrounding result from the preprint. -/
lemma local_separation_lower (N : ℕ) :
    crtModulus N ^ 2 ≤
      min (localAOne N) (localATwo N - localAOne N) := by
  rw [le_min_iff]
  constructor
  · exact (localAOne_bounds N).1
  · have h1 := (localAOne_bounds N).2
    have h2 := (localATwo_bounds N).1
    have hp := crtModulus_pos N
    have hsum : localAOne N + crtModulus N ^ 2 ≤ localATwo N := by
      nlinarith
    omega

/-- Auxiliary fact `local_separation_tendsto` used in the proof of the surrounding result from the preprint. -/
lemma local_separation_tendsto :
    Tendsto (fun N ↦ min (localAOne N) (localATwo N - localAOne N))
      atTop atTop := by
  exact Filter.tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun N ↦
      (show crtModulus N ≤ crtModulus N ^ 2 by
        have := crtModulus_pos N
        nlinarith).trans (local_separation_lower N))
    crtModulus_tendsto

/-- The conductor of the suborder `ℤ + 2^c 3^d 5^r O`. -/
def suborderConductor (c d r : ℕ) : ℕ :=
  2 ^ c * 3 ^ d * 5 ^ r


end CubicPeriodicTori


/-!
# The bounded-matrix and subsequence step in the final proof

This section follows the final paragraph of Dang--Gargava--Li: root estimates
give a uniformly bounded determinant-one family of logarithmic unit bases,
and compactness supplies a convergent subsequence.  It intentionally does
not identify the limit.
-/

noncomputable section

namespace CubicPeriodicTori
namespace FinalCompactness

open Filter Set Topology
open CubicOrderFamily

/-- The explicit CRT pair chosen at level `N+1` in the final proof. -/
def parameters (N : ℕ) : Parameters where
  a₁ := localAOne (N + 1)
  a₂ := localATwo (N + 1)
  three_le := by exact_mod_cast (local_parameters_ordered N).1
  lt := by exact_mod_cast (local_parameters_ordered N).2

def scale (N : ℕ) : ℝ := crtModulus (N + 1)

/-- Auxiliary fact `scale_nat` used in the proof of the surrounding result from the preprint. -/
lemma scale_nat (N : ℕ) : scale N = (crtModulus (N + 1) : ℕ) := rfl

/-- Auxiliary fact `scale_ge_thirty` used in the proof of the surrounding result from the preprint. -/
lemma scale_ge_thirty (N : ℕ) : 30 ≤ scale N := by
  change (30 : ℝ) ≤ (crtModulus (N + 1) : ℕ)
  rw [crtModulus_eq, pow_succ]
  have hp : 1 ≤ 30 ^ N := Nat.one_le_pow N 30 (by norm_num)
  have hmul := Nat.mul_le_mul_left 30 hp
  simpa [mul_comm] using (show (30 : ℝ) * 1 ≤ 30 * (30 ^ N : ℕ) by
    exact_mod_cast hmul)

/-- Auxiliary fact `scale_pos` used in the proof of the surrounding result from the preprint. -/
lemma scale_pos (N : ℕ) : 0 < scale N := lt_of_lt_of_le (by norm_num) (scale_ge_thirty N)

/-- Auxiliary fact `scale_one_lt` used in the proof of the surrounding result from the preprint. -/
lemma scale_one_lt (N : ℕ) : 1 < scale N := lt_of_lt_of_le (by norm_num) (scale_ge_thirty N)

/-- Auxiliary fact `log_scale_pos` used in the proof of the surrounding result from the preprint. -/
lemma log_scale_pos (N : ℕ) : 0 < Real.log (scale N) :=
  Real.log_pos (scale_one_lt N)

/-- Auxiliary fact `exp_ten_lt_three_pow_ten` used in the proof of the surrounding result from the preprint. -/
private lemma exp_ten_lt_three_pow_ten : Real.exp 10 < (3 : ℝ) ^ 10 := by
  have hpow : Real.exp 1 ^ 10 < (3 : ℝ) ^ 10 :=
    pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
      (by norm_num : 10 ≠ 0)
  have hexp : Real.exp 10 = Real.exp 1 ^ 10 := by
    simpa using Real.exp_nat_mul 1 10
  rwa [hexp]

/-- Auxiliary fact `exp_ten_lt_scale_sq` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `a₁_lower` used in the proof of the surrounding result from the preprint. -/
private lemma a₁_lower (N : ℕ) : scale N ^ 2 ≤ (parameters N).a₁ := by
  change (scale N : ℝ) ^ 2 ≤ (localAOne (N + 1) : ℕ)
  rw [scale_nat]
  exact_mod_cast (localAOne_bounds (N + 1)).1

/-- Auxiliary fact `a₁_upper` used in the proof of the surrounding result from the preprint. -/
private lemma a₁_upper (N : ℕ) : ((parameters N).a₁ : ℝ) ≤ scale N ^ 2 + scale N := by
  have hnat : localAOne (N + 1) ≤
      crtModulus (N + 1) ^ 2 + crtModulus (N + 1) :=
    Nat.le_of_lt (localAOne_bounds (N + 1)).2
  change (localAOne (N + 1) : ℕ) ≤ scale N ^ 2 + scale N
  rw [scale_nat]
  exact_mod_cast hnat

/-- Auxiliary fact `a₂_lower` used in the proof of the surrounding result from the preprint. -/
private lemma a₂_lower (N : ℕ) : 3 * scale N ^ 2 ≤ (parameters N).a₂ := by
  change (3 : ℝ) * scale N ^ 2 ≤ (localATwo (N + 1) : ℕ)
  rw [scale_nat]
  exact_mod_cast (localATwo_bounds (N + 1)).1

/-- Auxiliary fact `a₂_upper` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `scale_sq_sub_one_ge_scale` used in the proof of the surrounding result from the preprint. -/
private lemma scale_sq_sub_one_ge_scale (N : ℕ) :
    scale N ≤ scale N ^ 2 - 1 := by
  have h := scale_ge_thirty N
  nlinarith

/-- Auxiliary fact `three_scale_sq_add_scale_le_cube` used in the proof of the surrounding result from the preprint. -/
private lemma three_scale_sq_add_scale_le_cube (N : ℕ) :
    3 * scale N ^ 2 + scale N ≤ scale N ^ 3 := by
  have h := scale_ge_thirty N
  nlinarith [sq_nonneg (scale N - 4)]

/-- Auxiliary fact `two_scale_sq_sub_scale_ge_scale` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `A_argument_bounds` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `B_argument_bounds` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `C_argument_bounds` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `D_argument_bounds` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `log_bounds_of_scale_le_of_le_cube` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `A_bounds` used in the proof of the surrounding result from the preprint. -/
lemma A_bounds (N : ℕ) :
    Real.log (scale N) ≤ A N ∧ A N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (A_argument_bounds N).1 (A_argument_bounds N).2

/-- Auxiliary fact `B_bounds` used in the proof of the surrounding result from the preprint. -/
lemma B_bounds (N : ℕ) :
    Real.log (scale N) ≤ B N ∧ B N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (B_argument_bounds N).1 (B_argument_bounds N).2

/-- Auxiliary fact `C_bounds` used in the proof of the surrounding result from the preprint. -/
lemma C_bounds (N : ℕ) :
    Real.log (scale N) ≤ C N ∧ C N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (C_argument_bounds N).1 (C_argument_bounds N).2

/-- Auxiliary fact `D_bounds` used in the proof of the surrounding result from the preprint. -/
lemma D_bounds (N : ℕ) :
    Real.log (scale N) ≤ D N ∧ D N ≤ 3 * Real.log (scale N) :=
  log_bounds_of_scale_le_of_le_cube N (D_argument_bounds N).1 (D_argument_bounds N).2

/-- Auxiliary fact `root0_product` used in the proof of the surrounding result from the preprint. -/
private lemma root0_product (N : ℕ) :
    root0 (parameters N) *
        (((parameters N).a₁ : ℝ) - root0 (parameters N)) *
        (((parameters N).a₂ : ℝ) - root0 (parameters N)) = 1 := by
  have h := realRoot_root (parameters N) (0 : Fin 3)
  rw [Polynomial.IsRoot, definingPolynomialR_eval] at h
  change root0 (parameters N) *
      (root0 (parameters N) - (parameters N).a₁) *
      (root0 (parameters N) - (parameters N).a₂) - 1 = 0 at h
  nlinarith

/-- Auxiliary fact `root1_product` used in the proof of the surrounding result from the preprint. -/
private lemma root1_product (N : ℕ) :
    root1 (parameters N) *
        (((parameters N).a₁ : ℝ) - root1 (parameters N)) *
        (((parameters N).a₂ : ℝ) - root1 (parameters N)) = 1 := by
  have h := realRoot_root (parameters N) (1 : Fin 3)
  rw [Polynomial.IsRoot, definingPolynomialR_eval] at h
  change root1 (parameters N) *
      (root1 (parameters N) - (parameters N).a₁) *
      (root1 (parameters N) - (parameters N).a₂) - 1 = 0 at h
  nlinarith

/-- Auxiliary fact `root0_log` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `root1_sub_log` used in the proof of the surrounding result from the preprint. -/
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

/-- The logarithmic basis of the two canonical units, with the first two real
places as coordinates, exactly as in Lemmas 3.2 and 3.5 of the paper. -/
def unitLogBasis (N : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.log (root0 (parameters N)), A N;
     C N, Real.log (((parameters N).a₁ : ℝ) - root1 (parameters N))]

/-- Auxiliary fact `unitLogBasis_eq` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `unitLogBasis_det` used in the proof of the surrounding result from the preprint. -/
lemma unitLogBasis_det (N : ℕ) :
    (unitLogBasis N).det = A N * D N + B N * C N + B N * D N := by
  rw [unitLogBasis_eq, Matrix.det_fin_two]
  simp
  ring

/-- Auxiliary fact `unitLogBasis_det_lower` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `unitLogBasis_det_pos` used in the proof of the surrounding result from the preprint. -/
lemma unitLogBasis_det_pos (N : ℕ) : 0 < (unitLogBasis N).det := by
  have hL := log_scale_pos N
  have hsq : 0 < Real.log (scale N) ^ 2 := sq_pos_of_pos hL
  exact lt_of_lt_of_le hsq (unitLogBasis_det_lower N)

/-- Auxiliary fact `unitLogBasis_entry_abs_le` used in the proof of the surrounding result from the preprint. -/
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
def gN (N : ℕ) : SL2R :=
  normalizeBasis (unitLogBasis N) (unitLogBasis_det_pos N)

/-- Auxiliary fact `log_scale_le_sqrt_det` used in the proof of the surrounding result from the preprint. -/
private lemma log_scale_le_sqrt_det (N : ℕ) :
    Real.log (scale N) ≤ Real.sqrt (unitLogBasis N).det := by
  calc
    Real.log (scale N) = Real.sqrt (Real.log (scale N) ^ 2) := by
      rw [Real.sqrt_sq (log_scale_pos N).le]
    _ ≤ Real.sqrt (unitLogBasis N).det :=
      Real.sqrt_le_sqrt (unitLogBasis_det_lower N)

/-- Uniform coordinate boundedness asserted in the paper's compactness step. -/
lemma gN_entry_abs_le (N : ℕ) (i j : Fin 2) :
    |(gN N : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 6 := by
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

end FinalCompactness
end CubicPeriodicTori


/-!
# Compactness of the normalized cubic-order matrices

This section isolates the paper's compactness step: the normalized logarithmic
matrices lie in a fixed coordinate box, hence admit a convergent subsequence.
Continuity of the determinant shows that the matrix limit is again in
`SL(2, ℝ)`.  No formula for the limit is used.
-/

noncomputable section

namespace CubicPeriodicTori
namespace FinalCompactness

open Filter Set Topology
open FinalCompactness

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The fixed coordinate box containing every normalized matrix `g_N`. -/
def matrixBox : Set Mat2R :=
  (Set.Icc (-6 : ℝ) 6).matrix

/-- Auxiliary fact `matrixBox_isCompact` used in the proof of the surrounding result from the preprint. -/
lemma matrixBox_isCompact : IsCompact matrixBox :=
  IsCompact.matrix isCompact_Icc

/-- Auxiliary fact `coe_gN_mem_matrixBox` used in the proof of the surrounding result from the preprint. -/
lemma coe_gN_mem_matrixBox (N : ℕ) :
    (gN N : Mat2R) ∈ matrixBox := by
  rw [matrixBox, Set.mem_matrix]
  intro i j
  exact abs_le.mp (gN_entry_abs_le N i j)

private instance : FirstCountableTopology Mat2R :=
  inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))

/-- In dimension two, determinant one makes the inverse an entrywise signed
permutation of the original matrix.  Thus the same uniform bound holds for
the inverse matrices, as asserted in the paper. -/
lemma coe_gN_inv_entry_abs_le (N : ℕ) (i j : Fin 2) :
    |((↑((gN N)⁻¹) : Mat2R) i j)| ≤ 6 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact gN_entry_abs_le N 1 1
  · change |-((↑(gN N) : Mat2R) 0 1)| ≤ 6
    simpa only [abs_neg] using gN_entry_abs_le N 0 1
  · change |-((↑(gN N) : Mat2R) 1 0)| ≤ 6
    simpa only [abs_neg] using gN_entry_abs_le N 1 0
  · exact gN_entry_abs_le N 0 0

/-- The paper-faithful compactness conclusion: the normalized cubic-order matrices
have a convergent strictly monotone subsequence.  The limit is deliberately
left unidentified. -/
theorem exists_gN_convergent_subsequence :
    ∃ (g₀ : SL2R) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        Tendsto (gN ∘ subseq) atTop (nhds g₀) := by
  obtain ⟨M, hM, subseq, hsubseq, hMlim⟩ :=
    matrixBox_isCompact.tendsto_subseq
      (x := fun N ↦ (gN N : Mat2R)) coe_gN_mem_matrixBox
  have hdetlim :
      Tendsto (fun N ↦ ((gN (subseq N) : Mat2R).det)) atTop
        (nhds M.det) := by
    exact ((continuous_id.matrix_det).tendsto M).comp hMlim
  have hdetone :
      Tendsto (fun N ↦ ((gN (subseq N) : Mat2R).det)) atTop
        (nhds (1 : ℝ)) := by
    simpa only [(gN _).property] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  have hdet : M.det = 1 := tendsto_nhds_unique hdetlim hdetone
  let g₀ : SL2R := ⟨M, hdet⟩
  refine ⟨g₀, subseq, hsubseq, ?_⟩
  apply tendsto_subtype_rng.2
  change Tendsto ((fun N ↦ (↑(gN N) : Mat2R)) ∘ subseq) atTop (nhds M)
  exact hMlim

end FinalCompactness
end CubicPeriodicTori


/-!
# The fixed change of basis and the matrices `g_N g`

The final paragraph of Dang--Gargava--Li multiplies the bounded canonical unit
matrix `g_N` by the fixed matrix `g` from Lemma 5.1. This section records that
factorization and transfers the compactness subsequence to `g_N g`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace FinalCompactness

open Filter Topology
open FinalCompactness FinalCompactness

/-- The fixed integral exponent change from Lemma 5.1, over `ℝ`. -/
def exponentChangeReal : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-8, 16; -16, 8]

/-- Auxiliary fact `exponentChangeReal_eq` used in the proof of the surrounding result from the preprint. -/
lemma exponentChangeReal_eq :
    exponentChangeReal = !![-8, 16; -16, 8] := by
  rfl

/-- Auxiliary fact `exponentChangeReal_det` used in the proof of the surrounding result from the preprint. -/
lemma exponentChangeReal_det : exponentChangeReal.det = 192 := by
  rw [exponentChangeReal_eq, Matrix.det_fin_two]
  norm_num

/-- Auxiliary fact `exponentChangeReal_det_pos` used in the proof of the surrounding result from the preprint. -/
lemma exponentChangeReal_det_pos : 0 < exponentChangeReal.det := by
  rw [exponentChangeReal_det]
  norm_num

/-- The fixed determinant-one representative of the paper's matrix `g`. -/
def fixedMatrix : SL2R :=
  normalizeBasis exponentChangeReal exponentChangeReal_det_pos

/-- The determinant-one normalization of the paper's matrix `g_N g`. -/
def gN_mul_fixedMatrix (N : ℕ) : SL2R := gN N * fixedMatrix

/-- Auxiliary fact `normalize_unitLogBasis_mul_fixedMatrix` used in the proof of the surrounding result from the preprint. -/
lemma normalize_unitLogBasis_mul_fixedMatrix (N : ℕ) :
    normalizeBasis (unitLogBasis N * exponentChangeReal)
        (by simpa [Matrix.det_mul] using
          mul_pos (unitLogBasis_det_pos N) exponentChangeReal_det_pos) =
      gN_mul_fixedMatrix N := by
  rw [normalizeBasis_mul]
  rfl

/-- Compactness for the paper's actual matrices `g_N g`; the limit remains
unidentified, exactly as in the paper. -/
theorem exists_gN_mul_fixedMatrix_convergent_subsequence :
    ∃ (g₀ : SL2R) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        Tendsto (gN_mul_fixedMatrix ∘ subseq) atTop (nhds g₀) := by
  obtain ⟨g₀, φ, hφ, hlim⟩ := exists_gN_convergent_subsequence
  refine ⟨g₀ * fixedMatrix, φ, hφ, ?_⟩
  change Tendsto (fun n ↦ gN (φ n) * fixedMatrix) atTop
    (nhds (g₀ * fixedMatrix))
  exact hlim.mul tendsto_const_nhds

end FinalCompactness
end CubicPeriodicTori


/-!
# Logarithms of the canonical units

Elementary logarithmic identities used to turn the exponent-lattice basis
of Proposition 4.4 into the actual period basis in Lemma 2.6.
-/

noncomputable section

namespace CubicPeriodicTori
namespace UnitLogarithms

open CubicOrderFamily FinalCompactness

variable {A : Type*} [CommRing A]

/-- Auxiliary fact `unitLog_mul` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `unitLog_inv` used in the proof of the surrounding result from the preprint. -/
lemma unitLog_inv (σ : Fin 3 → A →+* ℝ) (x : Aˣ) :
    OrderPeriods.unitLog σ x⁻¹ = -OrderPeriods.unitLog σ x := by
  have h := unitLog_mul σ x x⁻¹
  have hone : OrderPeriods.unitLog σ (1 : Aˣ) = 0 := by
    funext i
    fin_cases i <;> simp [OrderPeriods.unitLog]
  rw [mul_inv_cancel, hone] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Auxiliary fact `unitLog_zpow` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `unitLog_canonical_product` used in the proof of the surrounding result from the preprint. -/
lemma unitLog_canonical_product (P : Parameters) (m n : ℤ) :
    OrderPeriods.unitLog (orderEmbedding P)
        ((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n) =
      m • OrderPeriods.unitLog (orderEmbedding P) (thetaZeroUnit P) +
        n • OrderPeriods.unitLog (orderEmbedding P) (thetaZeroSubAOneUnit P) := by
  rw [unitLog_mul, unitLog_zpow, unitLog_zpow]

/-- Auxiliary fact `unitLog_thetaZero_eq_column_zero` used in the proof of the surrounding result from the preprint. -/
lemma unitLog_thetaZero_eq_column_zero (N : ℕ) :
    OrderPeriods.unitLog (orderEmbedding (parameters N))
        (thetaZeroUnit (parameters N)) =
      fun i ↦ unitLogBasis N i 0 := by
  funext i
  fin_cases i
  · simp only [OrderPeriods.unitLog, Matrix.cons_val_zero, coe_thetaZeroUnit,
      orderEmbedding_orderThetaZero]
    change Real.log |root0 (parameters N)| = Real.log (root0 (parameters N))
    rw [abs_of_pos (root0_strictBounds _).1]
  · simp only [OrderPeriods.unitLog, Matrix.cons_val_one, coe_thetaZeroUnit,
      orderEmbedding_orderThetaZero]
    change Real.log |root1 (parameters N)| = C N
    rw [abs_of_pos]
    · rfl
    · have ha : (3 : ℝ) ≤ (parameters N).a₁ := by
        exact_mod_cast (parameters N).three_le
      linarith [(root1_strictBounds (parameters N)).1]

/-- Auxiliary fact `unitLog_thetaZeroSubOne_eq_column_one` used in the proof of the surrounding result from the preprint. -/
lemma unitLog_thetaZeroSubOne_eq_column_one (N : ℕ) :
    OrderPeriods.unitLog (orderEmbedding (parameters N))
        (thetaZeroSubAOneUnit (parameters N)) =
      fun i ↦ unitLogBasis N i 1 := by
  funext i
  fin_cases i
  · change Real.log |orderEmbedding (parameters N) 0
        (thetaZeroSubAOneInOrder (parameters N))| = unitLogBasis N 0 1
    rw [thetaZeroSubAOneInOrder, map_sub, orderEmbedding_orderThetaZero]
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
        (thetaZeroSubAOneInOrder (parameters N))| = unitLogBasis N 1 1
    rw [thetaZeroSubAOneInOrder, map_sub, orderEmbedding_orderThetaZero]
    have hcast : orderEmbedding (parameters N) 1
        (algebraMap ℤ (orderCarrier (parameters N)) (parameters N).a₁) =
        ((parameters N).a₁ : ℝ) :=
      map_intCast (orderEmbedding (parameters N) 1) (parameters N).a₁
    rw [hcast]
    change Real.log |root1 (parameters N) - (parameters N).a₁| =
      Real.log (((parameters N).a₁ : ℝ) - root1 (parameters N))
    rw [abs_of_neg (sub_neg.mpr (root1_strictBounds _).2), neg_sub]

/-- Auxiliary fact `unitLog_canonical_product_eq_mulVec` used in the proof of the surrounding result from the preprint. -/
lemma unitLog_canonical_product_eq_mulVec (N : ℕ) (m n : ℤ) :
    OrderPeriods.unitLog (orderEmbedding (parameters N))
        ((thetaZeroUnit (parameters N)) ^ m *
          (thetaZeroSubAOneUnit (parameters N)) ^ n) =
      (unitLogBasis N).mulVec ![(m : ℝ), (n : ℝ)] := by
  rw [unitLog_canonical_product,
    unitLog_thetaZero_eq_column_zero, unitLog_thetaZeroSubOne_eq_column_one]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end UnitLogarithms
end CubicPeriodicTori


/-!
# Units and logarithms of the scalar suborders

This section gives the exact order/unit correspondence needed to apply Lemma
2.6 after Propositions 3.4 and 4.3.  A unit of `ℤ + qO` maps to an ambient
unit of `O`; conversely an ambient unit restricts precisely when its value
lies in `ℤ + qO`.  Closure under inversion is the elementary lemma proved
as part of the local-unit argument in `SuborderUnitLattice`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace SuborderUnitLattice

open CubicOrderFamily ScalarSuborders

/-- Inclusion of the scalar suborder induces inclusion of its unit group
into the ambient cubic-order unit group. -/
def ambientUnitMap (P : Parameters) (q : ℕ) :
    (scalarSuborder P q)ˣ →* (orderCarrier P)ˣ :=
  Units.map (scalarSuborder P q).val.toRingHom.toMonoidHom

/-- Auxiliary fact `coe_ambientUnitMap` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    ((ambientUnitMap P q x : (orderCarrier P)ˣ) : orderCarrier P) =
      (x : scalarSuborder P q) :=
  rfl

/-- Auxiliary fact `ambientUnitMap_injective` used in the proof of the surrounding result from the preprint. -/
lemma ambientUnitMap_injective (P : Parameters) (q : ℕ) :
    Function.Injective (ambientUnitMap P q) := by
  intro x y hxy
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val hxy

/-- Auxiliary fact `ambientUnitMap_value_mem` used in the proof of the surrounding result from the preprint. -/
lemma ambientUnitMap_value_mem (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    ((ambientUnitMap P q x : (orderCarrier P)ˣ) : orderCarrier P) ∈
      scalarSuborder P q :=
  (x : scalarSuborder P q).property

/-- Restriction of an ambient unit whose value lies in the scalar suborder.
The inverse belongs to the scalar suborder by the inversion step of
Proposition 4.4. -/
def restrictUnit (P : Parameters) (q : ℕ) (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    (scalarSuborder P q)ˣ where
  val := ⟨x, hx⟩
  inv := ⟨((x⁻¹ : (orderCarrier P)ˣ) : orderCarrier P),
    (SuborderUnitLattice.unit_inv_mem_scalarSuborder_iff P q x).2 hx⟩
  val_inv := by
    apply Subtype.ext
    exact x.val_inv
  inv_val := by
    apply Subtype.ext
    exact x.inv_val

/-- Auxiliary fact `coe_restrictUnit` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma coe_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    ((restrictUnit P q x hx : (scalarSuborder P q)ˣ) :
      scalarSuborder P q) = ⟨x, hx⟩ :=
  rfl

/-- Auxiliary fact `ambientUnitMap_restrictUnit` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma ambientUnitMap_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    ambientUnitMap P q (restrictUnit P q x hx) = x := by
  apply Units.ext
  rfl

/-- Auxiliary fact `restrictUnit_ambientUnitMap` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma restrictUnit_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    restrictUnit P q (ambientUnitMap P q x)
      (ambientUnitMap_value_mem P q x) = x := by
  apply Units.ext
  rfl

/-- Exact characterization of the range of unit inclusion. -/
theorem mem_range_ambientUnitMap_iff (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ) :
    x ∈ Set.range (ambientUnitMap P q) ↔
      (x : orderCarrier P) ∈ scalarSuborder P q := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ambientUnitMap_value_mem P q y
  · intro hx
    exact ⟨restrictUnit P q x hx, ambientUnitMap_restrictUnit P q x hx⟩

/-- Ambient units whose values lie in `ℤ + qO`. -/
def ambientUnitsInScalarSuborder (P : Parameters) (q : ℕ) :
    Subgroup (orderCarrier P)ˣ where
  carrier := {x | (x : orderCarrier P) ∈ scalarSuborder P q}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    exact (scalarSuborder P q).mul_mem hx hy
  inv_mem' := by
    intro x hx
    exact (SuborderUnitLattice.unit_inv_mem_scalarSuborder_iff P q x).2 hx

/-- Auxiliary fact `mem_ambientUnitsInScalarSuborder_iff` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma mem_ambientUnitsInScalarSuborder_iff
    (P : Parameters) (q : ℕ) (x : (orderCarrier P)ˣ) :
    x ∈ ambientUnitsInScalarSuborder P q ↔
      (x : orderCarrier P) ∈ scalarSuborder P q :=
  Iff.rfl

/-- Units of the scalar suborder are exactly the ambient units whose values
belong to that suborder. -/
def unitsEquivAmbientUnitsInScalarSuborder (P : Parameters) (q : ℕ) :
    (scalarSuborder P q)ˣ ≃*
      ambientUnitsInScalarSuborder P q where
  toFun x := ⟨ambientUnitMap P q x, ambientUnitMap_value_mem P q x⟩
  invFun x := restrictUnit P q x x.property
  left_inv x := by
    apply Units.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    exact ambientUnitMap_restrictUnit P q x x.property
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (ambientUnitMap P q) x y

/-- Auxiliary fact `unitsEquivAmbientUnitsInScalarSuborder_apply` used in the proof of the surrounding result from the preprint. -/
@[simp] lemma unitsEquivAmbientUnitsInScalarSuborder_apply
    (P : Parameters) (q : ℕ) (x : (scalarSuborder P q)ˣ) :
    (unitsEquivAmbientUnitsInScalarSuborder P q x : (orderCarrier P)ˣ) =
      ambientUnitMap P q x :=
  rfl

/-- Unit logarithms are unchanged by inclusion into the ambient cubic order. -/
lemma unitLog_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    OrderPeriods.unitLog (scalarSuborderEmbedding P q) x =
      OrderPeriods.unitLog (orderEmbedding P) (ambientUnitMap P q x) :=
  rfl

/-- The same compatibility in the restriction direction. -/
lemma unitLog_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    OrderPeriods.unitLog (scalarSuborderEmbedding P q)
        (restrictUnit P q x hx) =
      OrderPeriods.unitLog (orderEmbedding P) x :=
  rfl

/-- The displayed scalar-suborder basis starts with `1`, as required by the
converse direction of the matrix period criterion. -/
lemma scalarSuborderBasis_zero (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    scalarSuborderBasis P q hq 0 = 1 := by
  rw [scalarSuborderBasis_apply]
  rfl

/-- Every restricted real embedding is injective. -/
lemma scalarSuborderEmbedding_injective (P : Parameters) (q : ℕ)
    (i : Fin 3) :
    Function.Injective (scalarSuborderEmbedding P q i) := by
  intro x y hxy
  apply Subtype.ext
  exact ((rootEmbedding P i).injective.comp
    (FaithfulSMul.algebraMap_injective (orderCarrier P) (CubicField P))) hxy

/-- The particular injectivity fact requested by `OrderPeriods`. -/
lemma scalarSuborderEmbedding_zero_injective (P : Parameters) (q : ℕ) :
    Function.Injective (scalarSuborderEmbedding P q 0) :=
  scalarSuborderEmbedding_injective P q 0

end SuborderUnitLattice
end CubicPeriodicTori


/-!
# Density of shapes of periodic tori in the cubic case

The remainder proves Theorem 1.1 of

Nguyen-Thi Dang, Nihar Gargava, and Jialun Li,
*Density of shapes of periodic tori in the cubic case*, arXiv:2502.12754.

The definitions below make the two homogeneous spaces, the period lattice,
and its normalized shape explicit.  The proof is organized according to
Sections 2--5 of the paper. The banana argument used in Proposition 5.2 is
proved separately as `SL2Banana.banana_expanding_horocycle_dense`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace Proposition52

open Filter Set Topology

/-- The elementary multiplicative-independence fact behind both irrational
rotation arguments in Proposition 5.2. -/
lemma irrational_log_three_div_log_five :
    Irrational (Real.log 3 / Real.log 5) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hrel : (b : ℝ) * Real.log 3 = (a : ℝ) * Real.log 5 := by
    have hc := (div_eq_div_iff hlog5.ne' (Int.cast_ne_zero.mpr hb)).mp hab
    simpa [mul_comm] using hc
  have hratpos : 0 < (a : ℝ) / (b : ℝ) := by
    rw [← hab]
    exact div_pos hlog3 hlog5
  have impossible (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
      (h : (n : ℝ) * Real.log 3 = (m : ℝ) * Real.log 5) : False := by
    have hlogs : Real.log ((3 : ℝ) ^ n) = Real.log ((5 : ℝ) ^ m) := by
      simpa [Real.log_pow] using h
    have hpowsR : (3 : ℝ) ^ n = (5 : ℝ) ^ m :=
      Real.log_injOn_pos (pow_pos (by norm_num : (0 : ℝ) < 3) _)
        (pow_pos (by norm_num : (0 : ℝ) < 5) _) hlogs
    have hpowsN : 3 ^ n = 5 ^ m := by exact_mod_cast hpowsR
    have hcop : Nat.Coprime (3 ^ n) (5 ^ m) :=
      (by decide : Nat.Coprime 3 5).pow n m
    rw [hpowsN] at hcop
    have hone : 5 ^ m = 1 := (Nat.coprime_self (5 ^ m)).mp hcop
    exact (ne_of_gt (one_lt_pow₀ (by norm_num) hm.ne')) hone
  rcases div_pos_iff.mp hratpos with hpos | hneg
  · have haI : (0 : ℤ) < a := by exact_mod_cast hpos.1
    have hbI : (0 : ℤ) < b := by exact_mod_cast hpos.2
    have haCast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
      simpa [abs_of_pos haI]
    have hbCast : ((b.natAbs : ℕ) : ℝ) = (b : ℝ) := by
      simpa [abs_of_pos hbI]
    apply impossible a.natAbs b.natAbs
      (Int.natAbs_pos.mpr haI.ne') (Int.natAbs_pos.mpr hbI.ne')
    simpa [haCast, hbCast] using hrel
  · have haI : a < (0 : ℤ) := by exact_mod_cast hneg.1
    have hbI : b < (0 : ℤ) := by exact_mod_cast hneg.2
    have haCast : ((a.natAbs : ℕ) : ℝ) = -(a : ℝ) := by
      simpa [abs_of_neg haI]
    have hbCast : ((b.natAbs : ℕ) : ℝ) = -(b : ℝ) := by
      simpa [abs_of_neg hbI]
    apply impossible a.natAbs b.natAbs
      (Int.natAbs_pos.mpr haI.ne) (Int.natAbs_pos.mpr hbI.ne)
    have hnegrel := congrArg Neg.neg hrel
    simpa [haCast, hbCast] using hnegrel

/-- Auxiliary fact `irrational_scaled_logs` used in the proof of the surrounding result from the preprint. -/
lemma irrational_scaled_logs (s3 s5 : ℕ) (hs3 : 0 < s3) (hs5 : 0 < s5) :
    Irrational (((s3 : ℝ) * Real.log 3) / ((s5 : ℝ) * Real.log 5)) := by
  have hscaled : Irrational
      ((((s3 : ℝ) * (Real.log 3 / Real.log 5)) / (s5 : ℝ))) :=
    (irrational_log_three_div_log_five.natCast_mul hs3.ne').div_natCast hs5.ne'
  convert hscaled using 1
  have hlog5 : Real.log 5 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hs5R : (s5 : ℝ) ≠ 0 := by exact_mod_cast hs5.ne'
  field_simp

/-- Auxiliary fact `irrational_log_nat_div_log_nat` used in the proof of the surrounding result from the preprint. -/
lemma irrational_log_nat_div_log_nat {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hab : a.Coprime b) : Irrational (Real.log a / Real.log b) := by
  rw [irrational_iff_ne_rational]
  intro m n hn hq
  have hloga : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hrel : (n : ℝ) * Real.log a = (m : ℝ) * Real.log b := by
    have hc := (div_eq_div_iff hlogb.ne' (Int.cast_ne_zero.mpr hn)).mp hq
    simpa [mul_comm] using hc
  have hratpos : 0 < (m : ℝ) / (n : ℝ) := by
    rw [← hq]
    exact div_pos hloga hlogb
  have impossible (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
      (h : (v : ℝ) * Real.log a = (u : ℝ) * Real.log b) : False := by
    have hlogs : Real.log ((a : ℝ) ^ v) = Real.log ((b : ℝ) ^ u) := by
      simpa [Real.log_pow] using h
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans ha)
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans hb)
    have hpowsR : (a : ℝ) ^ v = (b : ℝ) ^ u :=
      Real.log_injOn_pos (pow_pos haR _) (pow_pos hbR _) hlogs
    have hpowsN : a ^ v = b ^ u := by exact_mod_cast hpowsR
    have hcop : Nat.Coprime (a ^ v) (b ^ u) := hab.pow v u
    rw [hpowsN] at hcop
    have hone : b ^ u = 1 := (Nat.coprime_self (b ^ u)).mp hcop
    exact (ne_of_gt (one_lt_pow₀ hb hu.ne')) hone
  rcases div_pos_iff.mp hratpos with hpos | hneg
  · have hmI : (0 : ℤ) < m := by exact_mod_cast hpos.1
    have hnI : (0 : ℤ) < n := by exact_mod_cast hpos.2
    have hmCast : ((m.natAbs : ℕ) : ℝ) = (m : ℝ) := by simpa [abs_of_pos hmI]
    have hnCast : ((n.natAbs : ℕ) : ℝ) = (n : ℝ) := by simpa [abs_of_pos hnI]
    apply impossible m.natAbs n.natAbs
      (Int.natAbs_pos.mpr hmI.ne') (Int.natAbs_pos.mpr hnI.ne')
    simpa [hmCast, hnCast] using hrel
  · have hmI : m < (0 : ℤ) := by exact_mod_cast hneg.1
    have hnI : n < (0 : ℤ) := by exact_mod_cast hneg.2
    have hmCast : ((m.natAbs : ℕ) : ℝ) = -(m : ℝ) := by simpa [abs_of_neg hmI]
    have hnCast : ((n.natAbs : ℕ) : ℝ) = -(n : ℝ) := by simpa [abs_of_neg hnI]
    apply impossible m.natAbs n.natAbs
      (Int.natAbs_pos.mpr hmI.ne) (Int.natAbs_pos.mpr hnI.ne)
    have hnegrel := congrArg Neg.neg hrel
    simpa [hmCast, hnCast] using hnegrel

/-- Auxiliary fact `irrational_log_five_div_log_two` used in the proof of the surrounding result from the preprint. -/
lemma irrational_log_five_div_log_two :
    Irrational (Real.log 5 / Real.log 2) :=
  irrational_log_nat_div_log_nat (by norm_num) (by norm_num) (by norm_num)

/-- If `A/B` is irrational and both numbers are positive, nonnegative
integral combinations `p A - q B` approximate every real target.  The proof
uses the dense forward orbit on the circle of length `B`, then continuously
lifts it to a fundamental interval chosen around the target. -/
lemma exists_nonnegative_irrational_approximation
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hirr : Irrational (A / B))
    (t : ℝ) :
    ∃ p q : ℕ → ℕ,
      Tendsto (fun n ↦ (p n : ℝ) * A - (q n : ℝ) * B) atTop (nhds t) := by
  letI : Fact (0 < B) := ⟨hB⟩
  have hdZ : DenseRange (fun z : ℤ ↦ z • (A : AddCircle B)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  have hdN : DenseRange (fun n : ℕ ↦ n • (A : AddCircle B)) :=
    denseRange_zsmul_iff_nsmul.mp hdZ
  obtain ⟨P, hP⟩ := exists_nat_gt ((t + B / 2) / A)
  have hPA : t + B / 2 < (P : ℝ) * A := by
    calc
      t + B / 2 = ((t + B / 2) / A) * A :=
        (div_mul_cancel₀ _ hA.ne').symm
      _ < (P : ℝ) * A := mul_lt_mul_of_pos_right hP hA
  let target : AddCircle B := (t - (P : ℝ) * A : ℝ)
  have htarget : target ∈ closure (Set.range fun n : ℕ ↦
      n • (A : AddCircle B)) := by
    rw [hdN.closure_eq]
    exact Set.mem_univ _
  rcases mem_closure_iff_seq_limit.mp htarget with ⟨x, hx, hxlim⟩
  choose k hk using hx
  have hklim : Tendsto (fun n ↦ k n • (A : AddCircle B)) atTop
      (nhds target) := by
    simpa only [hk] using hxlim
  let p : ℕ → ℕ := fun n ↦ P + k n
  have hplim : Tendsto (fun n ↦ p n • (A : AddCircle B)) atTop
      (nhds (t : AddCircle B)) := by
    have hcP : Tendsto (fun _ : ℕ ↦ P • (A : AddCircle B)) atTop
        (nhds (P • (A : AddCircle B))) := tendsto_const_nhds
    have hsum := hcP.add hklim
    simpa [p, target, add_nsmul, add_assoc] using hsum
  let a : ℝ := t - B / 2
  have ht_mem : t ∈ Set.Ico a (a + B) := by
    constructor <;> dsimp [a] <;> linarith
  have ha_mem : a ∈ Set.Ico a (a + B) :=
    ⟨le_rfl, lt_add_of_pos_right _ hB⟩
  have hcoe_ne : (t : AddCircle B) ≠ (a : AddCircle B) := by
    intro h
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht_mem ha_mem).mp h
    dsimp [a] at heq
    linarith
  let r : ℕ → ℝ := fun n ↦
    (AddCircle.equivIco B a (p n • (A : AddCircle B)) : ℝ)
  have hrlim : Tendsto r atTop (nhds t) := by
    have hc := (AddCircle.continuousAt_equivIco B a hcoe_ne).tendsto.comp hplim
    have heq : AddCircle.equivIco B a (t : AddCircle B) = ⟨t, ht_mem⟩ := by
      apply (AddCircle.equivIco B a).symm.injective
      rw [(AddCircle.equivIco B a).symm_apply_apply]
      change (t : AddCircle B) = (t : AddCircle B)
      rfl
    have hc' := continuous_subtype_val.continuousAt.tendsto.comp hc
    change Tendsto (fun n ↦
      ((AddCircle.equivIco B a (p n • (A : AddCircle B))) : ℝ)) atTop (nhds t)
    convert hc' using 1
    · funext n
      rfl
    · rw [heq]
  have hmultiple (n : ℕ) :
      ∃ z : ℤ, (z : ℝ) * B = (p n : ℝ) * A - r n := by
    have hcoe : (r n : AddCircle B) = ((p n : ℕ) : ℝ) * A := by
      change ((AddCircle.equivIco B a (p n • (A : AddCircle B)) : ℝ) :
          AddCircle B) = _
      have he := (AddCircle.equivIco B a).symm_apply_apply
        (p n • (A : AddCircle B))
      change ((AddCircle.equivIco B a (p n • (A : AddCircle B)) : ℝ) :
          AddCircle B) = p n • (A : AddCircle B) at he
      simpa using he
    have hmem : (r n - (p n : ℝ) * A) ∈ AddSubgroup.zmultiples B :=
      QuotientAddGroup.eq_iff_sub_mem.mp hcoe
    rcases AddSubgroup.mem_zmultiples_iff.mp hmem with ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    rw [Int.cast_neg, neg_mul, ← zsmul_eq_mul]
    rw [hz]
    ring
  choose z hz using hmultiple
  have hz_nonneg (n : ℕ) : 0 ≤ z n := by
    have hr_lt : r n < a + B := (AddCircle.equivIco B a _).property.2
    have hdiff : 0 < (p n : ℝ) * A - r n := by
      have hp_le : (P : ℝ) ≤ p n := by
        exact_mod_cast Nat.le_add_right P (k n)
      have hpA : (P : ℝ) * A ≤ (p n : ℝ) * A :=
        mul_le_mul_of_nonneg_right hp_le hA.le
      dsimp [a] at hr_lt
      linarith
    have hzB : (0 : ℝ) < (z n : ℝ) * B := hz n ▸ hdiff
    have hzpos : (0 : ℝ) < (z n : ℝ) := by
      rcases mul_pos_iff.mp hzB with hpos | hneg
      · exact hpos.1
      · exact False.elim (not_lt_of_ge hB.le hneg.2)
    exact_mod_cast hzpos.le
  let q : ℕ → ℕ := fun n ↦ (z n).toNat
  refine ⟨p, q, ?_⟩
  convert hrlim using 1
  funext n
  have hzcast : (((q n : ℕ) : ℝ)) = (z n : ℝ) := by
    norm_cast
    exact Int.toNat_of_nonneg (hz_nonneg n)
  rw [hzcast, hz n]
  ring

/-- Auxiliary fact `exists_nonnegative_irrational_close` used in the proof of the surrounding result from the preprint. -/
lemma exists_nonnegative_irrational_close
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hirr : Irrational (A / B))
    (t : ℝ) {e : ℝ} (he : 0 < e) :
    ∃ p q : ℕ, |(p : ℝ) * A - (q : ℝ) * B - t| < e := by
  obtain ⟨p, q, hlim⟩ :=
    exists_nonnegative_irrational_approximation hA hB hirr t
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim e he
  refine ⟨p N, q N, ?_⟩
  have hh := hN N le_rfl
  rw [Real.dist_eq] at hh
  convert hh using 1 <;> ring

/-! ### The corrected congruence calculation in Lemma 5.1 -/

/-- Equation (7), reindexed by `C=c-4`, `D=d-2`, and `R=r-1`. -/
def exponentLattice (C D R : ℕ) : Set (ℤ × ℤ) :=
  {mn |
    (7 * 2 ^ (C + 3) : ℤ) ∣ mn.1 + mn.2 ∧
    (8 * 3 ^ (D + 1) : ℤ) ∣ mn.1 - 2 * mn.2 ∧
    (24 * 5 ^ R : ℤ) ∣ 2 * mn.1 - mn.2}

/-- The right side of Lemma 5.1.  The displayed fixed matrix is
`g = 8 * [[-1,2],[-2,1]]`. -/
def parametrizedExponentLattice (C D R : ℕ) : Set (ℤ × ℤ) :=
  {mn | ∃ x y : ℤ,
    (7 * 2 ^ C : ℤ) ∣ 3 ^ D * x - 5 ^ R * y ∧
    mn =
      (8 * (-(3 ^ D * x) + 2 * (5 ^ R * y)),
       8 * (-2 * (3 ^ D * x) + 5 ^ R * y))}

/-- Corrected Lemma 5.1.  This coordinate proof avoids the two typos in the
printed Smith-normal-form calculation. -/
theorem exponentLattice_eq_parametrized (C D R : ℕ) :
    exponentLattice C D R = parametrizedExponentLattice C D R := by
  ext mn
  rcases mn with ⟨m, n⟩
  simp only [exponentLattice, parametrizedExponentLattice, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hSum, hSecond, hThird⟩
    rcases hSum with ⟨k, hk⟩
    rcases hSecond with ⟨x, hx⟩
    rcases hThird with ⟨y, hy⟩
    have hx' : m - 2 * n = 24 * (3 ^ D * x) := by
      calc
        m - 2 * n = (8 * 3 ^ (D + 1)) * x := hx
        _ = 24 * (3 ^ D * x) := by rw [pow_succ]; ring
    have hy' : 2 * m - n = 24 * (5 ^ R * y) := by
      calc
        2 * m - n = (24 * 5 ^ R) * y := hy
        _ = 24 * (5 ^ R * y) := by ring
    have hcoprime : IsCoprime (7 * 2 ^ C : ℤ) 3 := by
      have h37 : IsCoprime (3 : ℤ) 7 :=
        ⟨5, -2, by norm_num⟩
      have h32 : IsCoprime (3 : ℤ) 2 :=
        ⟨1, -1, by norm_num⟩
      exact (h37.mul_right h32.pow_right).symm
    have hk' : m + n = 8 * ((7 * 2 ^ C) * k) := by
      calc
        m + n = (7 * 2 ^ (C + 3)) * k := hk
        _ = 8 * ((7 * 2 ^ C) * k) := by
          rw [show C + 3 = C + 1 + 1 + 1 by omega]
          repeat' rw [pow_succ]
          ring
    have hlinear :
        3 * (5 ^ R * y - 3 ^ D * x) = (7 * 2 ^ C) * k := by
      omega
    have hremaining : (7 * 2 ^ C : ℤ) ∣ 3 ^ D * x - 5 ^ R * y := by
      apply hcoprime.dvd_of_dvd_mul_left
      refine ⟨-k, ?_⟩
      calc
        3 * (3 ^ D * x - 5 ^ R * y) =
            -(3 * (5 ^ R * y - 3 ^ D * x)) := by ring
        _ = -((7 * 2 ^ C) * k) := by rw [hlinear]
        _ = (7 * 2 ^ C) * (-k) := by ring
    refine ⟨x, y, hremaining, ?_⟩
    apply Prod.ext <;> simp only
    · omega
    · omega
  · rintro ⟨x, y, hremaining, hmn⟩
    have hm : m = 8 * (-(3 ^ D * x) + 2 * (5 ^ R * y)) :=
      congrArg Prod.fst hmn
    have hn : n = 8 * (-2 * (3 ^ D * x) + 5 ^ R * y) :=
      congrArg Prod.snd hmn
    subst m
    subst n
    rcases hremaining with ⟨k, hk⟩
    constructor
    · refine ⟨-3 * k, ?_⟩
      calc
        8 * (-(3 ^ D * x) + 2 * (5 ^ R * y)) +
            8 * (-2 * (3 ^ D * x) + 5 ^ R * y) =
            -24 * (3 ^ D * x - 5 ^ R * y) := by ring
        _ = -24 * ((7 * 2 ^ C) * k) := by rw [hk]
        _ = (7 * 2 ^ (C + 3)) * (-3 * k) := by
          rw [show C + 3 = C + 1 + 1 + 1 by omega]
          repeat' rw [pow_succ]
          ring
    constructor
    · refine ⟨x, ?_⟩
      rw [pow_succ]
      ring
    · refine ⟨y, ?_⟩
      ring

/-! ### The auxiliary lattices in Proposition 5.2 -/

/-- We remove the shifts in the paper: `(C,D,R)` below corresponds to
`(c,d,r) = (C+4,D+2,R+1)` in its notation.  This also repairs the implicit
index shift in the horospherical part of the printed proof. -/
abbrev Index := ℕ × ℕ × ℕ

def modulus (C : ℕ) : ℕ := 7 * 2 ^ C

def firstScale (D : ℕ) : ℕ := 3 ^ D

def secondScale (R : ℕ) : ℕ := 5 ^ R

/-- Auxiliary fact `modulus_pos` used in the proof of the surrounding result from the preprint. -/
lemma modulus_pos (C : ℕ) : 0 < modulus C := by
  simp [modulus]

instance (C : ℕ) : NeZero (modulus C) := ⟨(modulus_pos C).ne'⟩

/-- Auxiliary fact `firstScale_coprime_modulus` used in the proof of the surrounding result from the preprint. -/
lemma firstScale_coprime_modulus (C D : ℕ) :
    (firstScale D).Coprime (modulus C) := by
  apply Nat.Coprime.pow_left D
  apply Nat.Coprime.mul_right
  · norm_num
  · exact (by norm_num : Nat.Coprime 3 2).pow_right C

/-- Auxiliary fact `five_coprime_modulus` used in the proof of the surrounding result from the preprint. -/
lemma five_coprime_modulus (C : ℕ) : (5 : ℕ).Coprime (modulus C) := by
  apply Nat.Coprime.mul_right
  · norm_num
  · exact (by norm_num : Nat.Coprime 5 2).pow_right C

/-- A simultaneous positive period for `3` and `5` modulo `7 * 2^C`. -/
def periodExponent (C : ℕ) : ℕ := Nat.totient (modulus C)

/-- Auxiliary fact `periodExponent_pos` used in the proof of the surrounding result from the preprint. -/
lemma periodExponent_pos (C : ℕ) : 0 < periodExponent C := by
  exact Nat.totient_pos.mpr (modulus_pos C)

/-- Auxiliary fact `three_pow_periodExponent_modEq` used in the proof of the surrounding result from the preprint. -/
lemma three_pow_periodExponent_modEq (C : ℕ) :
    Nat.ModEq (modulus C) (3 ^ periodExponent C) 1 := by
  simpa [firstScale, periodExponent] using
    (Nat.ModEq.pow_totient (firstScale_coprime_modulus C 1))

/-- Auxiliary fact `five_pow_periodExponent_modEq` used in the proof of the surrounding result from the preprint. -/
lemma five_pow_periodExponent_modEq (C : ℕ) :
    Nat.ModEq (modulus C) (5 ^ periodExponent C) 1 := by
  exact Nat.ModEq.pow_totient (five_coprime_modulus C)

/-- `3^D`, regarded as a unit modulo `7 * 2^C`. -/
def firstScaleUnit (C D : ℕ) : (ZMod (modulus C))ˣ :=
  ((ZMod.isUnit_iff_coprime (firstScale D) (modulus C)).2
    (firstScale_coprime_modulus C D)).unit

/-- The representative `f` characterized by
`3^D f = 5^R (mod 7 * 2^C)`. -/
def residue (C D R : ℕ) : ℕ :=
  (((firstScaleUnit C D)⁻¹ : ZMod (modulus C)) * secondScale R).val

/-- Auxiliary fact `residue_lt` used in the proof of the surrounding result from the preprint. -/
lemma residue_lt (C D R : ℕ) : residue C D R < modulus C :=
  ZMod.val_lt _

/-- Auxiliary fact `residue_spec_zmod` used in the proof of the surrounding result from the preprint. -/
lemma residue_spec_zmod (C D R : ℕ) :
    (firstScale D : ZMod (modulus C)) * residue C D R = secondScale R := by
  rw [show (residue C D R : ZMod (modulus C)) =
      ((firstScaleUnit C D)⁻¹ : ZMod (modulus C)) * secondScale R by
        exact ZMod.natCast_zmod_val _]
  rw [show (firstScale D : ZMod (modulus C)) =
      (firstScaleUnit C D : ZMod (modulus C)) by
        exact (IsUnit.unit_spec _).symm]
  simp

/-- Auxiliary fact `residue_spec` used in the proof of the surrounding result from the preprint. -/
lemma residue_spec (C D R : ℕ) :
    Nat.ModEq (modulus C) (firstScale D * residue C D R)
      (secondScale R) := by
  exact (ZMod.natCast_eq_natCast_iff
    (firstScale D * residue C D R) (secondScale R) (modulus C)).mp
      (by simpa only [Nat.cast_mul] using residue_spec_zmod C D R)

/-- The integral congruence kernel before diagonal scaling. -/
def congruenceSolutions (C D R : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (firstScale D : ZMod (modulus C)) * v 0 =
    (secondScale R : ZMod (modulus C)) * v 1}

/-- The explicit column basis `(q,0),(f,1)` of the congruence kernel. -/
def congruenceBasis (C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(modulus C : ℤ), (residue C D R : ℤ); 0, 1]

/-- Auxiliary fact `congruenceSolutions_eq_range_mulVec` used in the proof of the surrounding result from the preprint. -/
lemma congruenceSolutions_eq_range_mulVec (C D R : ℕ) :
    congruenceSolutions C D R =
      Set.range (congruenceBasis C D R).mulVec := by
  ext v
  constructor
  · intro hv
    have hA : IsUnit (firstScale D : ZMod (modulus C)) :=
      (ZMod.isUnit_iff_coprime (firstScale D) (modulus C)).2
        (firstScale_coprime_modulus C D)
    have hyz : (v 0 : ZMod (modulus C)) =
        (residue C D R : ZMod (modulus C)) * v 1 := by
      apply hA.mul_left_cancel
      calc
        (firstScale D : ZMod (modulus C)) * v 0 =
            (secondScale R : ZMod (modulus C)) * v 1 := hv
        _ = ((firstScale D : ZMod (modulus C)) * residue C D R) *
            v 1 := by rw [residue_spec_zmod]
        _ = (firstScale D : ZMod (modulus C)) *
            ((residue C D R : ZMod (modulus C)) * v 1) := by ring
    have hdiv : (modulus C : ℤ) ∣
        (residue C D R : ℤ) * v 1 - v 0 := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact_mod_cast hyz
    rcases hdiv with ⟨k, hk⟩
    refine ⟨![(-k), v 1], ?_⟩
    funext i
    fin_cases i
    · simp [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linarith
    · simp [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rintro ⟨z, rfl⟩
    simp only [congruenceSolutions, Set.mem_setOf_eq]
    simp [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [← mul_assoc, residue_spec_zmod]

/-- The fixed integral change of exponent coordinates in Lemma 5.1. -/
def exponentChange : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-8, 16; -16, 8]

/-- An explicit column basis of the three-congruence exponent lattice. -/
def exponentBasis (C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  exponentChange *
    !![((firstScale D * modulus C : ℕ) : ℤ),
        ((firstScale D * residue C D R : ℕ) : ℤ);
       0, ((secondScale R : ℕ) : ℤ)]

/-- Auxiliary fact `exponentBasis_apply` used in the proof of the surrounding result from the preprint. -/
lemma exponentBasis_apply (C D R : ℕ) :
    exponentBasis C D R =
      !![-8 * ((firstScale D * modulus C : ℕ) : ℤ),
          -8 * ((firstScale D * residue C D R : ℕ) : ℤ) +
            16 * ((secondScale R : ℕ) : ℤ);
         -16 * ((firstScale D * modulus C : ℕ) : ℤ),
          -16 * ((firstScale D * residue C D R : ℕ) : ℤ) +
            8 * ((secondScale R : ℕ) : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentBasis, exponentChange, Matrix.mul_apply, Fin.sum_univ_two]

/-- Equation (7) and corrected Lemma 5.1, combined into an actual basis
statement rather than an equality of parametrized sets. -/
theorem exponentLattice_eq_range_exponentBasis (C D R : ℕ) :
    exponentLattice C D R = Set.range (fun z : Fin 2 → ℤ ↦
      ((exponentBasis C D R).mulVec z 0,
       (exponentBasis C D R).mulVec z 1)) := by
  rw [exponentLattice_eq_parametrized]
  ext mn
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    have hcong : ![x, y] ∈ congruenceSolutions C D R := by
      simp only [congruenceSolutions, Set.mem_setOf_eq]
      have hcast :
          (((firstScale D : ℤ) * x : ℤ) : ZMod (modulus C)) =
            (((secondScale R : ℤ) * y : ℤ) : ZMod (modulus C)) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        simpa [firstScale, secondScale, modulus, sub_eq_neg_add,
          add_comm, add_left_comm, add_assoc] using hxy.neg_right
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast] using hcast
    rw [congruenceSolutions_eq_range_mulVec] at hcong
    rcases hcong with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hx := congrFun hz 0
    have hy := congrFun hz 1
    simp [congruenceBasis, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at hx hy
    have hx' := hx.symm
    have hy' := hy.symm
    subst x
    subst y
    apply Prod.ext <;> simp only
    ·
      simp [exponentBasis_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        firstScale, secondScale]
      ring
    ·
      simp [exponentBasis_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        firstScale, secondScale]
      ring
  · rintro ⟨z, rfl⟩
    let x : ℤ := (modulus C : ℤ) * z 0 + (residue C D R : ℤ) * z 1
    let y : ℤ := z 1
    refine ⟨x, y, ?_, ?_⟩
    · have hspec :
          (((firstScale D : ℤ) * (residue C D R : ℤ) : ℤ) :
              ZMod (modulus C)) = (secondScale R : ℤ) := by
        push_cast
        simpa only [Nat.cast_mul] using residue_spec_zmod C D R
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hspec
      rcases hspec with ⟨k, hk⟩
      refine ⟨(firstScale D : ℤ) * z 0 - k * z 1, ?_⟩
      dsimp [x, y]
      change (firstScale D : ℤ) *
          ((modulus C : ℤ) * z 0 + (residue C D R : ℤ) * z 1) -
        (secondScale R : ℤ) * z 1 =
          (modulus C : ℤ) * ((firstScale D : ℤ) * z 0 - k * z 1)
      have hneg : (firstScale D : ℤ) * (residue C D R : ℤ) -
          (secondScale R : ℤ) = -(modulus C : ℤ) * k := by
        linarith [hk]
      calc
        (firstScale D : ℤ) *
              ((modulus C : ℤ) * z 0 + (residue C D R : ℤ) * z 1) -
            (secondScale R : ℤ) * z 1 =
            (modulus C : ℤ) * ((firstScale D : ℤ) * z 0) +
              ((firstScale D : ℤ) * (residue C D R : ℤ) -
                (secondScale R : ℤ)) * z 1 := by ring
        _ = (modulus C : ℤ) * ((firstScale D : ℤ) * z 0 - k * z 1) := by
          rw [hneg]
          ring
    · apply Prod.ext <;> simp only
      · simp [x, y, exponentBasis_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, firstScale, secondScale]
        ring
      · simp [x, y, exponentBasis_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, firstScale, secondScale]
        ring

/-- The basis obtained after applying `diag(3^D,5^R)`. -/
def lambdaBasis (C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(firstScale D * modulus C : ℕ),
      (firstScale D * residue C D R : ℕ);
     0, (secondScale R : ℕ)]

/-- Auxiliary fact `lambdaBasis_det` used in the proof of the surrounding result from the preprint. -/
lemma lambdaBasis_det (C D R : ℕ) :
    (lambdaBasis C D R).det =
      (firstScale D * modulus C * secondScale R : ℕ) := by
  simp [lambdaBasis, Matrix.det_fin_two]

/-- Auxiliary fact `lambdaBasis_det_pos` used in the proof of the surrounding result from the preprint. -/
lemma lambdaBasis_det_pos (C D R : ℕ) :
    0 < (lambdaBasis C D R).det := by
  rw [lambdaBasis_det]
  norm_num [firstScale, secondScale, modulus]

/-- The normalized shape of the paper's auxiliary lattice
`Λ_{C+4,D+2,R+1}`. -/
def lambdaShape (C D R : ℕ) : ShapeSpace :=
  (normalizeBasis (lambdaBasis C D R) (lambdaBasis_det_pos C D R) :
    ShapeSpace)

/-- Auxiliary fact `normalize_left` used in the proof of the surrounding result from the preprint. -/
private lemma normalize_left (A B Q : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hQ : 0 < Q) :
    (Real.sqrt (A * Q * B))⁻¹ * (A * Q) = Real.sqrt (A * Q / B) := by
  rw [← (sq_eq_sq₀ (by positivity) (by positivity))]
  rw [Real.sq_sqrt (by positivity), inv_mul_eq_div, div_pow]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- Auxiliary fact `normalize_bottom` used in the proof of the surrounding result from the preprint. -/
private lemma normalize_bottom (A B Q : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hQ : 0 < Q) :
    (Real.sqrt (A * Q * B))⁻¹ * B = (Real.sqrt (A * Q / B))⁻¹ := by
  rw [← (sq_eq_sq₀ (by positivity) (by positivity))]
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [inv_mul_eq_div, div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- A canonical determinant-one representative of the same auxiliary shape. -/
def canonicalLambdaMatrix (C D R : ℕ) : SL2R :=
  let x := Real.sqrt
    (((firstScale D : ℕ) : ℝ) * modulus C / secondScale R)
  ⟨!![x, x * ((residue C D R : ℕ) : ℝ) / modulus C;
      0, x⁻¹], by
    have hx : x ≠ 0 := by
      dsimp [x]
      apply ne_of_gt
      apply Real.sqrt_pos.2
      exact div_pos (mul_pos (by norm_num [firstScale]) (by
        exact_mod_cast modulus_pos C)) (by norm_num [secondScale])
    simp [Matrix.det_fin_two, hx]⟩

/-- Auxiliary fact `lambdaShape_eq_canonical` used in the proof of the surrounding result from the preprint. -/
lemma lambdaShape_eq_canonical (C D R : ℕ) :
    lambdaShape C D R = (canonicalLambdaMatrix C D R : ShapeSpace) := by
  apply congrArg (fun g : SL2R ↦ (g : ShapeSpace))
  apply Subtype.ext
  have hA : 0 < (((firstScale D : ℕ) : ℝ)) := by norm_num [firstScale]
  have hB : 0 < (((secondScale R : ℕ) : ℝ)) := by norm_num [secondScale]
  have hQ : 0 < (((modulus C : ℕ) : ℝ)) := by exact_mod_cast modulus_pos C
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [normalizeBasis, lambdaBasis, lambdaBasis_det, canonicalLambdaMatrix]
      using normalize_left (((firstScale D : ℕ) : ℝ))
        (((secondScale R : ℕ) : ℝ)) (((modulus C : ℕ) : ℝ)) hA hB hQ
  · simp [normalizeBasis, lambdaBasis, canonicalLambdaMatrix]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hA),
      ne_of_gt (Real.sqrt_pos.2 hB), ne_of_gt (Real.sqrt_pos.2 hQ),
      Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, Real.sq_sqrt hQ.le]
    rw [Real.sq_sqrt hQ.le, Real.sq_sqrt hA.le]
    ring
  · simp [normalizeBasis, lambdaBasis, canonicalLambdaMatrix]
  · simpa [normalizeBasis, lambdaBasis, lambdaBasis_det, canonicalLambdaMatrix]
      using normalize_bottom (((firstScale D : ℕ) : ℝ))
        (((secondScale R : ℕ) : ℝ)) (((modulus C : ℕ) : ℝ)) hA hB hQ

def aspectLog (C D R : ℕ) : ℝ :=
  Real.log ((((firstScale D : ℕ) : ℝ) * modulus C) / secondScale R)

/-- Auxiliary fact `aspectLog_eq` used in the proof of the surrounding result from the preprint. -/
lemma aspectLog_eq (C D R : ℕ) :
    aspectLog C D R =
      (D : ℝ) * Real.log 3 + Real.log (modulus C) - (R : ℝ) * Real.log 5 := by
  have hA : (((firstScale D : ℕ) : ℝ)) ≠ 0 := by norm_num [firstScale]
  have hB : (((secondScale R : ℕ) : ℝ)) ≠ 0 := by norm_num [secondScale]
  have hQ : (((modulus C : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (modulus_pos C).ne'
  rw [aspectLog, Real.log_div (mul_ne_zero hA hQ) hB,
    Real.log_mul hA hQ]
  simp [firstScale, secondScale, Real.log_pow]

/-- Canonical upper-triangular coordinates on the shape space. -/
def timeMatrix (C f : ℕ) (x : ℝ) : SL2R :=
  ⟨!![Real.exp (x / 2),
      Real.exp (x / 2) * ((f : ℕ) : ℝ) / modulus C;
      0, Real.exp (-x / 2)], by
    simp [Matrix.det_fin_two, ← Real.exp_add]
    ring_nf⟩

/-- Auxiliary fact `canonicalLambdaMatrix_eq_timeMatrix` used in the proof of the surrounding result from the preprint. -/
lemma canonicalLambdaMatrix_eq_timeMatrix (C D R : ℕ) :
    canonicalLambdaMatrix C D R =
      timeMatrix C (residue C D R) (aspectLog C D R) := by
  apply Subtype.ext
  have hratio : 0 < ((((firstScale D : ℕ) : ℝ) * modulus C) / secondScale R) :=
    div_pos (mul_pos (by norm_num [firstScale]) (by exact_mod_cast modulus_pos C))
      (by norm_num [secondScale])
  ext i j
  fin_cases i <;> fin_cases j
  · change Real.sqrt _ = Real.exp (Real.log _ / 2)
    rw [Real.exp_half, Real.exp_log hratio]
  · change Real.sqrt _ * _ / _ = Real.exp (Real.log _ / 2) * _ / _
    rw [Real.exp_half, Real.exp_log hratio]
  · rfl
  · change (Real.sqrt _)⁻¹ = Real.exp (-Real.log _ / 2)
    rw [show -Real.log ((((firstScale D : ℕ) : ℝ) * modulus C) /
          secondScale R) / 2 =
        -(Real.log ((((firstScale D : ℕ) : ℝ) * modulus C) /
          secondScale R) / 2) by ring,
      Real.exp_neg, Real.exp_half, Real.exp_log hratio]

/-- Auxiliary fact `lambdaShape_eq_timeMatrix` used in the proof of the surrounding result from the preprint. -/
lemma lambdaShape_eq_timeMatrix (C D R : ℕ) :
    lambdaShape C D R =
      (timeMatrix C (residue C D R) (aspectLog C D R) : ShapeSpace) := by
  rw [lambdaShape_eq_canonical, canonicalLambdaMatrix_eq_timeMatrix]

/-- Auxiliary fact `continuous_timeMatrix` used in the proof of the surrounding result from the preprint. -/
lemma continuous_timeMatrix (C f : ℕ) : Continuous (timeMatrix C f) := by
  refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
  exact continuous_matrix fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp [timeMatrix] <;> fun_prop

/-- Auxiliary fact `continuous_timeShape` used in the proof of the surrounding result from the preprint. -/
lemma continuous_timeShape (C f : ℕ) :
    Continuous (fun x : ℝ ↦ (timeMatrix C f x : ShapeSpace)) := by
  exact continuous_quot_mk.comp (continuous_timeMatrix C f)

def lambdaShapes : Set ShapeSpace :=
  Set.range fun i : Index ↦ lambdaShape i.1 i.2.1 i.2.2

def omega : Set ShapeSpace := closure lambdaShapes

/-- `a(t) = diag(exp(t/2), exp(-t/2))`. -/
def diagonalFlow (t : ℝ) : SL2R :=
  ⟨!![Real.exp (t / 2), 0; 0, Real.exp (-t / 2)], by
    simp [Matrix.det_fin_two, ← Real.exp_add]
    ring_nf⟩

/-- Auxiliary fact `timeMatrix_add` used in the proof of the surrounding result from the preprint. -/
lemma timeMatrix_add (C f : ℕ) (x t : ℝ) :
    timeMatrix C f (x + t) = diagonalFlow t * timeMatrix C f x := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two,
      ← Real.exp_add]
    ring
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two]
    rw [show (x + t) / 2 = t / 2 + x / 2 by ring, Real.exp_add]
    ring
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two,
      ← Real.exp_add]
    ring

/-- `u(s) = [[1,s],[0,1]]`. -/
def horocycle (s : ℝ) : SL2R :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- Auxiliary fact `timeMatrix_zero` used in the proof of the surrounding result from the preprint. -/
lemma timeMatrix_zero (C f : ℕ) :
    timeMatrix C f 0 = horocycle ((f : ℝ) / modulus C) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [timeMatrix, horocycle]

def squareShape : ShapeSpace := (1 : SL2R)

/-- Representatives of the subgroup generated by `5` modulo `7 * 2^C`,
chosen in `[0,7 * 2^C)`.  This is the set `S_C` in Section 5.2. -/
def residueMesh (C : ℕ) : Set ℕ :=
  {f | f < modulus C ∧ ∃ R : ℕ, Nat.ModEq (modulus C) (5 ^ R) f}

/-- The exponent data in equation (10).  The modular-period fields preserve
the congruence kernel; `log_tendsto` is the irrational-rotation
approximation of the required diagonal displacement. -/
private structure DiagonalExponentApproximation (C D R : ℕ) (t : ℝ) where
  s3 : ℕ
  s5 : ℕ
  s3_pos : 0 < s3
  s5_pos : 0 < s5
  period3 : Nat.ModEq (modulus C) (3 ^ s3) 1
  period5 : Nat.ModEq (modulus C) (5 ^ s5) 1
  p : ℕ → ℕ
  q : ℕ → ℕ
  log_tendsto : Tendsto
    (fun n ↦ ((p n * s3 : ℕ) : ℝ) * Real.log 3 -
      ((q n * s5 : ℕ) : ℝ) * Real.log 5)
    atTop (𝓝 t)

def DiagonalExponentApproximation.Dindex
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) : ℕ :=
  D + h.s3 * h.p n

def DiagonalExponentApproximation.Rindex
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) : ℕ :=
  R + h.s5 * h.q n

/-- Auxiliary fact `DiagonalExponentApproximation.firstScale_modEq` used in the proof of the surrounding result from the preprint. -/
lemma DiagonalExponentApproximation.firstScale_modEq
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) :
    Nat.ModEq (modulus C) (firstScale (h.Dindex n)) (firstScale D) := by
  calc
    firstScale (h.Dindex n) = 3 ^ D * (3 ^ h.s3) ^ h.p n := by
      simp [firstScale, Dindex, pow_add, pow_mul]
    _ ≡ 3 ^ D * 1 ^ h.p n [MOD modulus C] :=
      (h.period3.pow (h.p n)).mul_left _
    _ = firstScale D := by simp [firstScale]

/-- Auxiliary fact `DiagonalExponentApproximation.secondScale_modEq` used in the proof of the surrounding result from the preprint. -/
lemma DiagonalExponentApproximation.secondScale_modEq
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) :
    Nat.ModEq (modulus C) (secondScale (h.Rindex n)) (secondScale R) := by
  calc
    secondScale (h.Rindex n) = 5 ^ R * (5 ^ h.s5) ^ h.q n := by
      simp [secondScale, Rindex, pow_add, pow_mul]
    _ ≡ 5 ^ R * 1 ^ h.q n [MOD modulus C] :=
      (h.period5.pow (h.q n)).mul_left _
    _ = secondScale R := by simp [secondScale]

/-- Auxiliary fact `DiagonalExponentApproximation.residue_eq` used in the proof of the surrounding result from the preprint. -/
lemma DiagonalExponentApproximation.residue_eq
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) : residue C (h.Dindex n) (h.Rindex n) = residue C D R := by
  apply Nat.ModEq.eq_of_lt_of_lt _ (residue_lt _ _ _) (residue_lt _ _ _)
  rw [← ZMod.natCast_eq_natCast_iff]
  have hfirst : (firstScale (h.Dindex n) : ZMod (modulus C)) =
      firstScale D :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.firstScale_modEq n)
  have hsecond : (secondScale (h.Rindex n) : ZMod (modulus C)) =
      secondScale R :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.secondScale_modEq n)
  have hunit : IsUnit (firstScale D : ZMod (modulus C)) :=
    (ZMod.isUnit_iff_coprime _ _).2 (firstScale_coprime_modulus C D)
  apply hunit.mul_left_cancel
  calc
    (firstScale D : ZMod (modulus C)) *
        residue C (h.Dindex n) (h.Rindex n) =
        (firstScale (h.Dindex n) : ZMod (modulus C)) *
          residue C (h.Dindex n) (h.Rindex n) := by rw [hfirst]
    _ = secondScale (h.Rindex n) := residue_spec_zmod _ _ _
    _ = secondScale R := hsecond
    _ = (firstScale D : ZMod (modulus C)) * residue C D R :=
      (residue_spec_zmod C D R).symm

/-- The irrational-rotation existence statement used for equation (10). -/
def HasDiagonalExponentData : Prop :=
  ∀ (C D R : ℕ) (t : ℝ),
    Nonempty (DiagonalExponentApproximation C D R t)

/-- Irrational rotation supplies all exponent sequences in equation (10). -/
theorem hasDiagonalExponentData : HasDiagonalExponentData := by
  intro C D R t
  let s := periodExponent C
  have hs : 0 < s := periodExponent_pos C
  have hA : 0 < (s : ℝ) * Real.log 3 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  have hB : 0 < (s : ℝ) * Real.log 5 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  obtain ⟨p, q, hlim⟩ := exists_nonnegative_irrational_approximation hA hB
    (irrational_scaled_logs s s hs hs) t
  refine ⟨{
    s3 := s
    s5 := s
    s3_pos := hs
    s5_pos := hs
    period3 := three_pow_periodExponent_modEq C
    period5 := five_pow_periodExponent_modEq C
    p := p
    q := q
    log_tendsto := ?_ }⟩
  convert hlim using 1
  funext n
  push_cast
  ring

/-- The algebraic and continuity calculation turning equation (10) into
convergence of normalized lattice shapes. -/
def DiagonalExponentDataIsSound : Prop :=
  ∀ (C D R : ℕ) (t : ℝ) (h : DiagonalExponentApproximation C D R t),
    Tendsto
      (fun n ↦ lambdaShape C (h.Dindex n) (h.Rindex n)) atTop
      (𝓝 (diagonalFlow t • lambdaShape C D R))

/-- Auxiliary fact `DiagonalExponentApproximation.aspectLog_tendsto` used in the proof of the surrounding result from the preprint. -/
lemma DiagonalExponentApproximation.aspectLog_tendsto
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t) :
    Tendsto (fun n ↦ aspectLog C (h.Dindex n) (h.Rindex n)) atTop
      (nhds (aspectLog C D R + t)) := by
  have ht := h.log_tendsto.const_add (aspectLog C D R)
  convert ht using 1
  funext n
  rw [aspectLog_eq, aspectLog_eq]
  dsimp [Dindex, Rindex]
  push_cast
  ring

/-- The algebraic/continuity content of equation (10). -/
theorem diagonalExponentData_isSound : DiagonalExponentDataIsSound := by
  intro C D R t h
  have ht := (continuous_timeShape C (residue C D R)).continuousAt.tendsto.comp
    h.aspectLog_tendsto
  convert ht using 1
  · funext n
    rw [lambdaShape_eq_timeMatrix, h.residue_eq]
    rfl
  · apply congrArg nhds
    rw [lambdaShape_eq_timeMatrix, timeMatrix_add]
    rfl

/-- The exponent data in equation (12) for a mesh point `f/(7 * 2^C)`. -/
private structure HorosphereExponentApproximation (C f : ℕ)
    (hf : f ∈ residueMesh C) where
  rf : ℕ
  s3 : ℕ
  s5 : ℕ
  residue_power : Nat.ModEq (modulus C) (5 ^ rf) f
  s3_pos : 0 < s3
  s5_pos : 0 < s5
  period3 : Nat.ModEq (modulus C) (3 ^ s3) 1
  period5 : Nat.ModEq (modulus C) (5 ^ s5) 1
  p : ℕ → ℕ
  q : ℕ → ℕ
  log_tendsto : Tendsto
    (fun n ↦ (rf : ℝ) * Real.log 5 +
      ((q n * s5 : ℕ) : ℝ) * Real.log 5 -
      ((p n * s3 : ℕ) : ℝ) * Real.log 3 - Real.log (modulus C))
    atTop (𝓝 0)

def HorosphereExponentApproximation.Dindex
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) : ℕ :=
  h.s3 * h.p n

def HorosphereExponentApproximation.Rindex
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) : ℕ :=
  h.rf + h.s5 * h.q n

/-- Auxiliary fact `HorosphereExponentApproximation.firstScale_modEq` used in the proof of the surrounding result from the preprint. -/
lemma HorosphereExponentApproximation.firstScale_modEq
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) :
    Nat.ModEq (modulus C) (firstScale (h.Dindex n)) 1 := by
  calc
    firstScale (h.Dindex n) = (3 ^ h.s3) ^ h.p n := by
      simp [firstScale, Dindex, pow_mul]
    _ ≡ 1 ^ h.p n [MOD modulus C] := h.period3.pow (h.p n)
    _ = 1 := one_pow _

/-- Auxiliary fact `HorosphereExponentApproximation.secondScale_modEq` used in the proof of the surrounding result from the preprint. -/
lemma HorosphereExponentApproximation.secondScale_modEq
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) :
    Nat.ModEq (modulus C) (secondScale (h.Rindex n)) f := by
  calc
    secondScale (h.Rindex n) = 5 ^ h.rf * (5 ^ h.s5) ^ h.q n := by
      simp [secondScale, Rindex, pow_add, pow_mul]
    _ ≡ f * 1 ^ h.q n [MOD modulus C] :=
      h.residue_power.mul (h.period5.pow (h.q n))
    _ = f := by simp

/-- Auxiliary fact `HorosphereExponentApproximation.residue_eq` used in the proof of the surrounding result from the preprint. -/
lemma HorosphereExponentApproximation.residue_eq
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) :
    residue C (h.Dindex n) (h.Rindex n) = f := by
  apply Nat.ModEq.eq_of_lt_of_lt _ (residue_lt _ _ _) hf.1
  rw [← ZMod.natCast_eq_natCast_iff]
  calc
    (residue C (h.Dindex n) (h.Rindex n) : ZMod (modulus C)) =
        (firstScale (h.Dindex n) : ZMod (modulus C)) *
          residue C (h.Dindex n) (h.Rindex n) := by
            rw [(ZMod.natCast_eq_natCast_iff _ _ _).2
              (h.firstScale_modEq n)]
            simp
    _ = secondScale (h.Rindex n) := residue_spec_zmod _ _ _
    _ = f :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.secondScale_modEq n)

/-- Irrational rotation supplies the positive exponent sequences in (12). -/
def HasHorosphereExponentData : Prop :=
  ∀ (C f : ℕ) (hf : f ∈ residueMesh C),
    Nonempty (HorosphereExponentApproximation C f hf)

/-- Irrational rotation also supplies the corrected exponent sequences in
equation (12). -/
theorem hasHorosphereExponentData : HasHorosphereExponentData := by
  intro C f hf
  rcases hf.2 with ⟨rf, hrf⟩
  let s := periodExponent C
  have hs : 0 < s := periodExponent_pos C
  have hA : 0 < (s : ℝ) * Real.log 3 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  have hB : 0 < (s : ℝ) * Real.log 5 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  let target := (rf : ℝ) * Real.log 5 - Real.log (modulus C)
  obtain ⟨p, q, hlim⟩ := exists_nonnegative_irrational_approximation hA hB
    (irrational_scaled_logs s s hs hs) target
  refine ⟨{
    rf := rf
    s3 := s
    s5 := s
    residue_power := hrf
    s3_pos := hs
    s5_pos := hs
    period3 := three_pow_periodExponent_modEq C
    period5 := five_pow_periodExponent_modEq C
    p := p
    q := q
    log_tendsto := ?_ }⟩
  have ht := hlim.neg.const_add target
  convert ht using 1
  · funext n
    dsimp [target]
    push_cast
    ring
  · dsimp [target]
    ring

/-- The corrected algebraic conclusion of equation (12).  Our index `C` is
the paper's `c-4`, so the sequence here represents
`Λ_{C+4,D_n+2,R_n+1}` rather than the misindexed printed expression. -/
def HorosphereExponentDataIsSound : Prop :=
  ∀ (C f : ℕ) (hf : f ∈ residueMesh C)
      (h : HorosphereExponentApproximation C f hf),
    Tendsto
      (fun n ↦ lambdaShape C (h.Dindex n) (h.Rindex n)) atTop
      (𝓝 (horocycle ((f : ℝ) / modulus C) • squareShape))

/-- Auxiliary fact `HorosphereExponentApproximation.aspectLog_tendsto` used in the proof of the surrounding result from the preprint. -/
lemma HorosphereExponentApproximation.aspectLog_tendsto
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) :
    Tendsto (fun n ↦ aspectLog C (h.Dindex n) (h.Rindex n)) atTop
      (nhds 0) := by
  have ht := h.log_tendsto.neg
  convert ht using 1
  · funext n
    rw [aspectLog_eq]
    dsimp [Dindex, Rindex]
    push_cast
    ring
  · simp

/-- The algebraic/continuity content of equation (12). -/
theorem horosphereExponentData_isSound : HorosphereExponentDataIsSound := by
  intro C f hf h
  have ht := (continuous_timeShape C f).continuousAt.tendsto.comp
    h.aspectLog_tendsto
  convert ht using 1
  · funext n
    rw [lambdaShape_eq_timeMatrix, h.residue_eq]
    rfl
  · apply congrArg nhds
    rw [timeMatrix_zero]
    simp [squareShape]

def HasDiagonalShapeSequences : Prop :=
  ∀ (C D R : ℕ) (t : ℝ), ∃ Dn Rn : ℕ → ℕ,
    Tendsto (fun n ↦ lambdaShape C (Dn n) (Rn n)) atTop
      (𝓝 (diagonalFlow t • lambdaShape C D R))

def HasHorosphereMeshSequences : Prop :=
  ∀ (C f : ℕ), f ∈ residueMesh C → ∃ Dn Rn : ℕ → ℕ,
    Tendsto (fun n ↦ lambdaShape C (Dn n) (Rn n)) atTop
      (𝓝 (horocycle ((f : ℝ) / modulus C) • squareShape))

/-- Auxiliary fact `hasDiagonalShapeSequences_of_exponent_data` used in the proof of the surrounding result from the preprint. -/
theorem hasDiagonalShapeSequences_of_exponent_data
    (hexists : HasDiagonalExponentData)
    (hsound : DiagonalExponentDataIsSound) :
    HasDiagonalShapeSequences := by
  intro C D R t
  let h := (hexists C D R t).some
  exact ⟨h.Dindex, h.Rindex, hsound C D R t h⟩

/-- Auxiliary fact `hasHorosphereMeshSequences_of_exponent_data` used in the proof of the surrounding result from the preprint. -/
theorem hasHorosphereMeshSequences_of_exponent_data
    (hexists : HasHorosphereExponentData)
    (hsound : HorosphereExponentDataIsSound) :
    HasHorosphereMeshSequences := by
  intro C f hf
  let h := (hexists C f hf).some
  exact ⟨h.Dindex, h.Rindex, hsound C f hf h⟩

/-- The bounded-gap assertion about `S_C/(7 * 2^C)`.  In the paper this is
proved from
`S_C = {56k+j | j ∈ {1,5,9,13,25,45}}`, whose gaps are at most `20`. -/
def MeshApproximatesUnitInterval : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ Cn fn : ℕ → ℕ,
    (∀ n, fn n ∈ residueMesh (Cn n)) ∧
    Tendsto (fun n ↦ ((fn n : ℕ) : ℝ) / modulus (Cn n)) atTop (𝓝 s)

/-- The required residue mesh is dense.  It is enough to use powers `5^R`
before reduction: irrationality of `log 5 / log 2` makes
`5^R / (7 * 2^C)` approach every point of `[0,1]` from below. -/
theorem meshApproximatesUnitInterval : MeshApproximatesUnitInterval := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · let Cn : ℕ → ℕ := fun n ↦ n
    let fn : ℕ → ℕ := fun _ ↦ 1
    refine ⟨Cn, fn, ?_, ?_⟩
    · intro n
      refine ⟨?_, 0, ?_⟩
      · have hone : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        dsimp [fn, Cn, modulus]
        omega
      · exact Nat.ModEq.refl _
    · have hden : Tendsto (fun n : ℕ ↦ (modulus n : ℝ)) atTop atTop := by
        have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
        have hm := Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 7) hp
        simpa [modulus, Nat.cast_mul, Nat.cast_pow] using hm
      have hz : Tendsto (fun n : ℕ ↦ (1 : ℝ) / modulus n) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      simpa [fn, Cn] using hz
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have heps (n : ℕ) : 0 < (1 : ℝ) / (n + 1) := by positivity
    have hchoice : ∀ n : ℕ, ∃ p q : ℕ,
        |(p : ℝ) * Real.log 5 - (q : ℝ) * Real.log 2 -
          (Real.log s + Real.log 7 - 3 * (1 / ((n : ℝ) + 1)))| <
            1 / ((n : ℝ) + 1) := by
      intro n
      exact exists_nonnegative_irrational_close hlog5 hlog2
        irrational_log_five_div_log_two _ (heps n)
    choose p q hpq using hchoice
    let Cn : ℕ → ℕ := q
    let fn : ℕ → ℕ := fun n ↦ 5 ^ p n
    let L : ℕ → ℝ := fun n ↦
      (p n : ℝ) * Real.log 5 - (q n : ℝ) * Real.log 2 - Real.log 7
    have hL (n : ℕ) :
        |L n - Real.log s| < 4 * (1 / ((n : ℝ) + 1)) := by
      dsimp [L]
      have hn := hpq n
      rw [abs_lt] at hn ⊢
      constructor <;> linarith
    have hdelta : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop
        (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hfour : Tendsto (fun n : ℕ ↦ 4 * ((1 : ℝ) / (n + 1))) atTop
        (nhds 0) := by
      simpa using hdelta.const_mul 4
    have hLlim : Tendsto L atTop (nhds (Real.log s)) := by
      have hlower : Tendsto
          (fun n : ℕ ↦ Real.log s - 4 * ((1 : ℝ) / (n + 1))) atTop
          (nhds (Real.log s)) := by simpa using tendsto_const_nhds.sub hfour
      have hupper : Tendsto
          (fun n : ℕ ↦ Real.log s + 4 * ((1 : ℝ) / (n + 1))) atTop
          (nhds (Real.log s)) := by simpa using tendsto_const_nhds.add hfour
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
      · exact Filter.Eventually.of_forall fun n ↦ by
          have := (abs_lt.mp (hL n)).1.le
          linarith
      · exact Filter.Eventually.of_forall fun n ↦ by
          have := (abs_lt.mp (hL n)).2.le
          linarith
    have hexp (n : ℕ) :
        Real.exp (L n) = ((fn n : ℕ) : ℝ) / modulus (Cn n) := by
      have hratio : 0 < (((5 : ℝ) ^ p n) / (7 * 2 ^ q n)) := by positivity
      simp only [fn, Cn, modulus, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul]
      rw [← Real.exp_log hratio]
      congr 1
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (by positivity),
        Real.log_pow, Real.log_pow]
      dsimp [L, fn, Cn, modulus]
      push_cast
      ring
    refine ⟨Cn, fn, ?_, ?_⟩
    · intro n
      refine ⟨?_, p n, Nat.ModEq.refl _⟩
      have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs.1 hs.2
      have hLneg : L n < 0 := by
        have hup := (abs_lt.mp (hpq n)).2
        dsimp [L]
        linarith [heps n]
      have hratio : ((fn n : ℕ) : ℝ) / modulus (Cn n) < 1 := by
        rw [← hexp]
        simpa using Real.exp_lt_one_iff.mpr hLneg
      have hcast : ((fn n : ℕ) : ℝ) < modulus (Cn n) :=
        (div_lt_one (by exact_mod_cast modulus_pos (Cn n))).mp hratio
      exact_mod_cast hcast
    · have he := (Real.continuous_exp.tendsto (Real.log s)).comp hLlim
      rw [Real.exp_log hspos] at he
      convert he using 1
      funext n
      exact (hexp n).symm

/-- Auxiliary fact `lambdaShape_mem_lambdaShapes` used in the proof of the surrounding result from the preprint. -/
lemma lambdaShape_mem_lambdaShapes (C D R : ℕ) :
    lambdaShape C D R ∈ lambdaShapes := by
  exact ⟨(C, D, R), rfl⟩

/-- Auxiliary fact `diagonal_generator_mem_omega` used in the proof of the surrounding result from the preprint. -/
lemma diagonal_generator_mem_omega (h : HasDiagonalShapeSequences)
    (C D R : ℕ) (t : ℝ) :
    diagonalFlow t • lambdaShape C D R ∈ omega := by
  rcases h C D R t with ⟨Dn, Rn, hn⟩
  exact IsClosed.mem_of_tendsto isClosed_closure hn
    (Filter.Eventually.of_forall fun n ↦
      subset_closure (lambdaShape_mem_lambdaShapes C (Dn n) (Rn n)))

/-- Auxiliary fact `horosphere_mesh_point_mem_omega` used in the proof of the surrounding result from the preprint. -/
lemma horosphere_mesh_point_mem_omega (h : HasHorosphereMeshSequences)
    (C f : ℕ) (hf : f ∈ residueMesh C) :
    horocycle ((f : ℝ) / modulus C) • squareShape ∈ omega := by
  rcases h C f hf with ⟨Dn, Rn, hn⟩
  exact IsClosed.mem_of_tendsto isClosed_closure hn
    (Filter.Eventually.of_forall fun n ↦
      subset_closure (lambdaShape_mem_lambdaShapes C (Dn n) (Rn n)))

/-- Auxiliary fact `continuous_horocycle_square` used in the proof of the surrounding result from the preprint. -/
lemma continuous_horocycle_square :
    Continuous (fun s : ℝ ↦ horocycle s • squareShape) := by
  have hh : Continuous horocycle := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_matrix fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  exact continuous_smul.comp (hh.prodMk continuous_const)

/-- The approximation statement proved on the generators in the diagonal
part of Proposition 5.2. -/
def DiagonalGeneratorApproximation : Prop :=
  ∀ t : ℝ, ∀ C D R : ℕ,
    diagonalFlow t • lambdaShape C D R ∈ omega

/-- The conclusion of the residue-mesh argument in the horospherical part. -/
def ContainsHorosphericalPiece : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, horocycle s • squareShape ∈ omega

/-- Auxiliary fact `diagonalGeneratorApproximation_of_shape_sequences` used in the proof of the surrounding result from the preprint. -/
lemma diagonalGeneratorApproximation_of_shape_sequences
    (h : HasDiagonalShapeSequences) :
    DiagonalGeneratorApproximation := by
  intro t C D R
  exact diagonal_generator_mem_omega h C D R t

/-- Auxiliary fact `containsHorosphericalPiece_of_mesh` used in the proof of the surrounding result from the preprint. -/
lemma containsHorosphericalPiece_of_mesh
    (hseq : HasHorosphereMeshSequences)
    (hmesh : MeshApproximatesUnitInterval) :
    ContainsHorosphericalPiece := by
  intro s hs
  rcases hmesh s hs with ⟨Cn, fn, hfn, hlim⟩
  apply IsClosed.mem_of_tendsto isClosed_closure
    (continuous_horocycle_square.continuousAt.tendsto.comp hlim)
  exact Filter.Eventually.of_forall fun n ↦
    horosphere_mesh_point_mem_omega hseq (Cn n) (fn n) (hfn n)

/-- The expanding half-horocycle appearing in Margulis' banana argument. -/
def bananaSet : Set ShapeSpace :=
  {x | ∃ t ∈ Set.Ici (0 : ℝ), ∃ s ∈ Set.Icc (0 : ℝ) 1,
    x = ((diagonalFlow t * horocycle s : SL2R) : ShapeSpace)}

/-- Margulis' banana trick, equivalently the expanding-horocycle input used
in the proof of Proposition 5.2.  Its elementary proof is isolated in
`BananaLemma.lean`. -/
theorem banana_dense : Dense bananaSet := by
  change Dense SL2Banana.bananaExpandingStrip
  exact SL2Banana.banana_expanding_horocycle_dense

/-- Closed-subset form of the banana trick.  Unlike `banana_dense`, this is a
formal consequence and needs no additional dynamical input. -/
theorem banana_lemma (Ω : Set ShapeSpace)
    (hΩ : IsClosed Ω)
    (hdiag : ∀ t : ℝ, Set.MapsTo (diagonalFlow t • ·) Ω Ω)
    (hhoro : ∀ s ∈ Set.Icc (0 : ℝ) 1, horocycle s • squareShape ∈ Ω) :
    Ω = Set.univ := by
  have hbanana : bananaSet ⊆ Ω := by
    rintro x ⟨t, ht, s, hs, rfl⟩
    have hu := hhoro s hs
    have ha := hdiag t hu
    simpa [squareShape, mul_smul] using ha
  have hdense : Dense Ω := Dense.mono hbanana banana_dense
  calc
    Ω = closure Ω := hΩ.closure_eq.symm
    _ = Set.univ := dense_iff_closure_eq.mp hdense

/-- Auxiliary fact `diagonal_mapsTo_omega` used in the proof of the surrounding result from the preprint. -/
lemma diagonal_mapsTo_omega (h : DiagonalGeneratorApproximation) :
    ∀ t : ℝ, Set.MapsTo (diagonalFlow t • ·) omega omega := by
  intro t
  have hpreclosed : IsClosed ((diagonalFlow t • ·) ⁻¹' omega) :=
    isClosed_closure.preimage (continuous_const_smul (diagonalFlow t))
  have hgenerators : lambdaShapes ⊆ (diagonalFlow t • ·) ⁻¹' omega := by
    rintro _ ⟨⟨C, D, R⟩, rfl⟩
    exact h t C D R
  exact closure_minimal hgenerators hpreclosed

/-- Proposition 5.2 follows from its two approximation steps and the
banana lemma. -/
theorem proposition_5_2
    (hdiag : DiagonalGeneratorApproximation)
    (hhoro : ContainsHorosphericalPiece) :
    Dense lambdaShapes := by
  rw [dense_iff_closure_eq]
  exact banana_lemma omega isClosed_closure
    (diagonal_mapsTo_omega hdiag) hhoro

/-- **Dang--Gargava--Li, Proposition 5.2.** The auxiliary lattices
`Λ_{c,d,r}` have dense shapes in `SL(2, ℝ) / SL(2, ℤ)`. -/
theorem auxiliary_shapes_dense : Dense lambdaShapes := by
  have hdiagSeq := hasDiagonalShapeSequences_of_exponent_data
    hasDiagonalExponentData diagonalExponentData_isSound
  have hhoroSeq := hasHorosphereMeshSequences_of_exponent_data
    hasHorosphereExponentData horosphereExponentData_isSound
  exact proposition_5_2
    (diagonalGeneratorApproximation_of_shape_sequences hdiagSeq)
    (containsHorosphericalPiece_of_mesh hhoroSeq meshApproximatesUnitInterval)

end Proposition52

/-! ### Proposition 4.4 in the shifted coordinates of Lemma 5.1 -/

namespace SuborderUnitLattice

open CubicOrderFamily ScalarSuborders

/-- Auxiliary fact `exponentConditions_shifted_eq_exponentLattice` used in the proof of the surrounding result from the preprint. -/
lemma exponentConditions_shifted_eq_exponentLattice (C D R : ℕ) :
    PrimePowerCalculations.ExponentConditions (C + 4) (D + 2) (R + 1) =
      Proposition52.exponentLattice C D R := by
  ext mn
  rcases mn with ⟨m, n⟩
  simp only [PrimePowerCalculations.ExponentConditions,
    Proposition52.exponentLattice, Set.mem_setOf_eq]
  have hC : C + 4 - 1 = C + 3 := by omega
  have hD : D + 2 - 1 = D + 1 := by omega
  have hR : R + 1 - 1 = R := by omega
  rw [hC, hD, hR]

/-- Proposition 4.4 in precisely the shifted lattice notation used by
Lemma 5.1 and the final density argument. -/
theorem canonical_product_mem_iff_exponentLattice
    (P : Parameters) (C D R : ℕ)
    (hlocal : SatisfiesLocalConditions (C + 4) (D + 2) (R + 1)
      P.a₁ P.a₂)
    (m n : ℤ) :
    ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P
          (2 ^ (C + 4) * 3 ^ (D + 2) * 5 ^ (R + 1))) ↔
      (m, n) ∈ Proposition52.exponentLattice C D R := by
  rw [canonical_product_mem_iff_exponentConditions P
    (C + 4) (D + 2) (R + 1) (by omega) (by omega) (by omega) hlocal]
  exact Set.ext_iff.mp (exponentConditions_shifted_eq_exponentLattice C D R)
    (m, n)

/-- Full Proposition 4.4 in the shifted notation of Lemma 5.1: this is the
classification of all ambient order units lying in the scalar suborder. -/
theorem unit_mem_scalarSuborder_iff_exists_sign_exponentLattice
    (P : Parameters) (C D R : ℕ)
    (hfund : (cubicOrder P).IsFundamentalFamily (candidateUnitFamily P))
    (hlocal : SatisfiesLocalConditions (C + 4) (D + 2) (R + 1)
      P.a₁ P.a₂)
    (x : (orderCarrier P)ˣ) :
    ((x : orderCarrier P) ∈ scalarSuborder P
        (2 ^ (C + 4) * 3 ^ (D + 2) * 5 ^ (R + 1))) ↔
      ∃ ε : (orderCarrier P)ˣ, (ε = 1 ∨ ε = -1) ∧
        ∃ m n : ℤ, (m, n) ∈ Proposition52.exponentLattice C D R ∧
          x = ε * (thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n := by
  rw [unit_mem_scalarSuborder_iff_exists_sign_exponents P
    (C + 4) (D + 2) (R + 1) (by omega) (by omega) (by omega)
    hfund hlocal]
  constructor
  · rintro ⟨ε, hε, m, n, hmn, hx⟩
    exact ⟨ε, hε, m, n,
      (Set.ext_iff.mp (exponentConditions_shifted_eq_exponentLattice C D R)
        (m, n)).mp hmn, hx⟩
  · rintro ⟨ε, hε, m, n, hmn, hx⟩
    exact ⟨ε, hε, m, n,
      (Set.ext_iff.mp (exponentConditions_shifted_eq_exponentLattice C D R)
        (m, n)).mpr hmn, hx⟩

end SuborderUnitLattice

/-! ### Sections 2--5: the scalar-order period matrix -/

namespace PeriodsOfSuborders

open CubicOrderFamily ScalarSuborders FinalCompactness
open Proposition52

/-- The conductor used for the scalar suborder in Proposition 4.4. -/
def conductor (C D R : ℕ) : ℕ :=
  2 ^ (C + 4) * 3 ^ (D + 2) * 5 ^ (R + 1)

/-- Auxiliary fact `unitLog_sign` used in the proof of the surrounding result from the preprint. -/
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

/-- Auxiliary fact `cast_exponentBasis_mulVec` used in the proof of the surrounding result from the preprint. -/
lemma cast_exponentBasis_mulVec (C D R : ℕ) (z : Fin 2 → ℤ) :
    (fun i ↦ (((exponentBasis C D R).mulVec z i : ℤ) : ℝ)) =
      (exponentChangeReal * lambdaBasis C D R).mulVec
        (fun i ↦ (z i : ℝ)) := by
  rw [← exponentBasis_cast_eq]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The period matrix obtained successively from Proposition 3.4,
Proposition 4.4, and Lemma 5.1. -/
def periodMatrix (N C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  unitLogBasis N * exponentChangeReal * lambdaBasis C D R

/-- Auxiliary fact `periodMatrix_det_pos` used in the proof of the surrounding result from the preprint. -/
lemma periodMatrix_det_pos (N C D R : ℕ) :
    0 < (periodMatrix N C D R).det := by
  simp only [periodMatrix, Matrix.det_mul]
  exact mul_pos (mul_pos (unitLogBasis_det_pos N)
    exponentChangeReal_det_pos) (lambdaBasis_det_pos C D R)

/-- Auxiliary fact `periodMatrix_mulVec` used in the proof of the surrounding result from the preprint. -/
lemma periodMatrix_mulVec (N C D R : ℕ) (z : Fin 2 → ℤ) :
    (periodMatrix N C D R).mulVec (fun i ↦ (z i : ℝ)) =
      (unitLogBasis N).mulVec
        (fun i ↦ (((exponentBasis C D R).mulVec z i : ℤ) : ℝ)) := by
  rw [periodMatrix, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← cast_exponentBasis_mulVec]

/-- Propositions 3.4 and 4.4, followed by Lemma 5.1, identify the complete
logarithmic unit lattice of the scalar order with the columns of
`periodMatrix`. -/
lemma unitLogs_iff_periodMatrix (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : SuborderUnitLattice.SatisfiesLocalConditions
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
        (((SuborderUnitLattice.ambientUnitMap P q x : (orderCarrier P)ˣ) :
          orderCarrier P) ∈ scalarSuborder P q) :=
      SuborderUnitLattice.ambientUnitMap_value_mem P q x
    have hclass :=
      (SuborderUnitLattice.unit_mem_scalarSuborder_iff_exists_sign_exponentLattice
        P C D R hfund hlocal (SuborderUnitLattice.ambientUnitMap P q x)).mp hxmem
    obtain ⟨ε, hε, m, n, hmn, hx⟩ := hclass
    rw [exponentLattice_eq_range_exponentBasis] at hmn
    obtain ⟨z, hz⟩ := hmn
    refine ⟨z, ?_⟩
    have hm : m = (exponentBasis C D R).mulVec z 0 :=
      (congrArg Prod.fst hz).symm
    have hn : n = (exponentBasis C D R).mulVec z 1 :=
      (congrArg Prod.snd hz).symm
    dsimp only [P, q] at *
    rw [SuborderUnitLattice.unitLog_ambientUnitMap, hx,
      UnitLogarithms.unitLog_mul, UnitLogarithms.unitLog_mul,
      unitLog_sign (parameters N) ε hε, zero_add]
    rw [← UnitLogarithms.unitLog_mul,
      UnitLogarithms.unitLog_canonical_product_eq_mulVec,
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
        ((((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n :
            (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) :=
      (SuborderUnitLattice.canonical_product_mem_iff_exponentLattice
        P C D R hlocal m n).mpr hmn
    let x : (scalarSuborder P q)ˣ := SuborderUnitLattice.restrictUnit P q
      ((thetaZeroUnit P) ^ m * (thetaZeroSubAOneUnit P) ^ n) hmem
    refine ⟨x, ?_⟩
    rw [SuborderUnitLattice.unitLog_restrictUnit,
      UnitLogarithms.unitLog_canonical_product_eq_mulVec,
      periodMatrix_mulVec]
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Lemma 2.6 applied to the scalar cubic order. -/
theorem normalized_periodMatrix_mem (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : SuborderUnitLattice.SatisfiesLocalConditions
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
    (SuborderUnitLattice.scalarSuborderBasis_zero (parameters N) q hq)
    (SuborderUnitLattice.scalarSuborderEmbedding_zero_injective (parameters N) q)
    (scalarSuborderEmbeddingMatrix_det_ne_zero (parameters N) q hq)
    (periodMatrix N C D R) (periodMatrix_det_pos N C D R)
  exact unitLogs_iff_periodMatrix N C D R hfund hlocal

/-- Auxiliary fact `normalized_periodMatrix_eq_gN_mul_fixedMatrix_smul` used in the proof of the surrounding result from the preprint. -/
lemma normalized_periodMatrix_eq_gN_mul_fixedMatrix_smul
    (N C D R : ℕ) :
    (normalizeBasis (periodMatrix N C D R)
        (periodMatrix_det_pos N C D R) : ShapeSpace) =
      gN_mul_fixedMatrix N • lambdaShape C D R := by
  have hUE : 0 < (unitLogBasis N * exponentChangeReal).det := by
    simpa only [Matrix.det_mul] using
      mul_pos (unitLogBasis_det_pos N) exponentChangeReal_det_pos
  change
    (normalizeBasis
      ((unitLogBasis N * exponentChangeReal) * lambdaBasis C D R)
      _ : ShapeSpace) = gN_mul_fixedMatrix N • lambdaShape C D R
  rw [normalizeBasis_mul (unitLogBasis N * exponentChangeReal)
    (lambdaBasis C D R) hUE (lambdaBasis_det_pos C D R)]
  rw [normalize_unitLogBasis_mul_fixedMatrix]
  rfl

/-- The paper's period statement, assuming the output of Proposition
3.4 and the local congruences entering Proposition 4.4. -/
theorem shape_of_suborder_of_fundamental (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : SuborderUnitLattice.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    gN_mul_fixedMatrix N • lambdaShape C D R ∈ periodicTorusShapes := by
  rw [← normalized_periodMatrix_eq_gN_mul_fixedMatrix_smul]
  exact normalized_periodMatrix_mem N C D R hfund hlocal

/-- For the CRT family, Proposition 3.4 follows from Cusick's regulator
inequality once `N ≥ 1`; hence the period statement requires only the local
conditions. -/
theorem shape_of_suborder (N C D R : ℕ) (hN : 1 ≤ N)
    (hlocal : SuborderUnitLattice.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    gN_mul_fixedMatrix N • lambdaShape C D R ∈ periodicTorusShapes := by
  have hlogs := parameters_logs_gt_ten N hN
  have hfund :=
    CubicOrderFamily.FundamentalUnits.candidateUnitFamily_isFundamental_of_large
      (P := parameters N) hlogs.1 hlogs.2
  exact shape_of_suborder_of_fundamental N C D R hfund hlocal

end PeriodsOfSuborders

open Filter Set Topology
open Proposition52

/-! ### Completion of the proof of Theorem 1.1 -/

open CubicOrderFamily FinalCompactness

/-- CRT congruences imposed at level `N+1` descend to the three (possibly
different) conductor exponents used in Proposition 4.4. -/
private lemma localConditions_for_order
    (N C D R : ℕ)
    (hlocal : SatisfiesLocalConditions (N + 1)
      (localAOne (N + 1)) (localATwo (N + 1)))
    (hC : C + 4 ≤ N + 1) (hD : D + 2 ≤ N + 1)
    (hR : R + 1 ≤ N + 1) :
    SuborderUnitLattice.SatisfiesLocalConditions (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂ := by
  rcases hlocal with ⟨h21, h22, h31, h32, h51, h52⟩
  have hd2 : 2 ^ (C + 4) ∣ 2 ^ (N + 1) := pow_dvd_pow 2 hC
  have hd3 : 3 ^ (D + 2) ∣ 3 ^ (N + 1) := pow_dvd_pow 3 hD
  have hd5 : 5 ^ (R + 1) ∣ 5 ^ (N + 1) := pow_dvd_pow 5 hR
  change
    ((localAOne (N + 1) : ℤ) ≡ 0 [ZMOD (2 : ℤ) ^ (C + 4)]) ∧
    ((localATwo (N + 1) : ℤ) ≡ 1 [ZMOD (2 : ℤ) ^ (C + 4)]) ∧
    ((localAOne (N + 1) : ℤ) ≡ 1 [ZMOD (3 : ℤ) ^ (D + 2)]) ∧
    ((localATwo (N + 1) : ℤ) ≡ 0 [ZMOD (3 : ℤ) ^ (D + 2)]) ∧
    ((localAOne (N + 1) : ℤ) ≡ 1 [ZMOD (5 : ℤ) ^ (R + 1)]) ∧
    ((localATwo (N + 1) : ℤ) ≡ 1 [ZMOD (5 : ℤ) ^ (R + 1)])
  constructor
  · exact_mod_cast h21.of_dvd hd2
  constructor
  · exact_mod_cast h22.of_dvd hd2
  constructor
  · exact_mod_cast h31.of_dvd hd3
  constructor
  · exact_mod_cast h32.of_dvd hd3
  constructor
  · exact_mod_cast h51.of_dvd hd5
  · exact_mod_cast h52.of_dvd hd5

/-- An element of `SL₂(ℝ)` carries a dense set of shapes to a dense set. -/
private lemma transformed_lambdaShapes_dense (h : Dense lambdaShapes)
    (g : SL2R) :
    Dense ((fun x : ShapeSpace => g • x) '' lambdaShapes) := by
  have hsurj : Function.Surjective (fun x : ShapeSpace => g • x) :=
    (MulAction.toPerm g).surjective
  exact hsurj.denseRange.dense_image (continuous_const_smul g) h

/-- **Dang--Gargava--Li, Theorem 1.1.** The shapes of periodic tori in
`M \ SL(3, ℝ) / SL(3, ℤ)` are dense in `SL(2, ℝ) / SL(2, ℤ)`. -/
theorem density_of_shapes_of_periodic_tori :
    Dense periodicTorusShapes := by
  -- This is the compactness subsequence `g_N g → g₀` in the final paragraph.
  obtain ⟨g₀, subseq, hsubseq, hg⟩ :=
    exists_gN_mul_fixedMatrix_convergent_subsequence
  let selected : ℕ → ℕ := fun n ↦ subseq (n + 1)
  have hselected_one (n : ℕ) : 1 ≤ selected n := by
    have hle : n + 1 ≤ subseq (n + 1) := hsubseq.id_le (n + 1)
    exact (Nat.le_add_left 1 n).trans hle
  have hg_shifted :
      Tendsto (fun n ↦ gN_mul_fixedMatrix (selected n)) atTop (𝓝 g₀) := by
    change Tendsto (fun n ↦ (gN_mul_fixedMatrix ∘ subseq) (n + 1)) atTop
      (𝓝 g₀)
    exact (Filter.tendsto_add_atTop_iff_nat 1).2 hg

  -- Every fixed lattice from Proposition 5.2 occurs for all sufficiently
  -- large members of the same CRT subsequence.
  have hlimit_mem (C D R : ℕ) :
      g₀ • lambdaShape C D R ∈ closure periodicTorusShapes := by
    let threshold := max (C + 4) (max (D + 2) (R + 1))
    let shapes : ℕ → ShapeSpace := fun n ↦
      gN_mul_fixedMatrix (selected n) • lambdaShape C D R
    have hshapes : Tendsto shapes atTop (𝓝 (g₀ • lambdaShape C D R)) :=
      hg_shifted.smul tendsto_const_nhds
    apply mem_closure_of_tendsto hshapes
    filter_upwards [eventually_ge_atTop threshold] with n hn
    apply PeriodsOfSuborders.shape_of_suborder (selected n) C D R (hselected_one n)
    apply localConditions_for_order (selected n) C D R
      (local_conditions (selected n + 1)) <;>
      have hsubseq_bound : n + 1 ≤ selected n := hsubseq.id_le (n + 1) <;>
      omega

  -- Proposition 5.2 is dense, and multiplication by `g₀` is a homeomorphism.
  have hclosure : Dense (closure periodicTorusShapes) := by
    apply Dense.mono ?_
      (transformed_lambdaShapes_dense
        Proposition52.auxiliary_shapes_dense g₀)
    intro x hx
    rcases hx with ⟨y, ⟨⟨C, D, R⟩, rfl⟩, rfl⟩
    exact hlimit_mem C D R
  rw [dense_iff_closure_eq] at hclosure ⊢
  simpa only [closure_closure] using hclosure

end CubicPeriodicTori
