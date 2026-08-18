import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Foundational dynamics and period-lattice definitions

This module contains the homogeneous spaces, diagonal action, period basis,
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

lemma flow_smul_sign_smul (u : FlowParameter) (m : signDiagonal)
    (x : CubicLatticeSpace) :
    u • (m • x) = m • (u • x) := by
  change diagonalEmbedding u • ((m : SL3R) • x) =
    (m : SL3R) • (diagonalEmbedding u • x)
  rw [← mul_smul, ← mul_smul, diagonalEmbedding_commutes_sign]

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
