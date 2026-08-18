import ABCOrders
import SuborderUnits
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Scalar suborders of the ABC order

This file supplies the concrete rank-three order used in the arithmetic
realization.  For a positive natural number `q`, `scalarSuborder P q` is
the order `ℤ + q ℤ[α]`.  Its displayed basis is `1, qα, qα²`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ArithmeticConstruction

open ABCOrders

/-- The scalar suborder `ℤ + q O` of the ABC order `O = ℤ[α]`. -/
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

lemma mem_scalarSuborder_iff (P : Parameters) (q : ℕ) (x : orderCarrier P) :
    x ∈ scalarSuborder P q ↔
      ∃ a : ℤ, ∃ y : orderCarrier P,
        x = algebraMap ℤ (orderCarrier P) a + q • y :=
  Iff.rfl

/-- Coordinate form of membership in `ℤ + qO`: the `α` and `α²`
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

lemma orderAlpha_pow_three (P : Parameters) :
    orderAlpha P ^ 3 =
      1 - algebraMap ℤ (orderCarrier P) (P.a₁ * P.a₂) * orderAlpha P +
        algebraMap ℤ (orderCarrier P) (P.a₁ + P.a₂) * orderAlpha P ^ 2 := by
  have h := order_generators_mul P
  simp only [orderAlphaSubOne, orderAlphaSubTwo] at h
  simp only [map_mul, map_add]
  linear_combination h

lemma orderAlpha_pow_three_eq_basis (P : Parameters) :
    orderAlpha P ^ 3 =
      orderBasis P 0 + (-(P.a₁ * P.a₂)) • orderBasis P 1 +
        (P.a₁ + P.a₂) • orderBasis P 2 := by
  rw [orderAlpha_pow_three]
  simp [orderBasis_apply, Algebra.smul_def]
  ring

/-- Multiplication by `α` in the power basis is the companion matrix of
`X³ - (a₁+a₂)X² + a₁a₂X - 1`. -/
lemma leftMulMatrix_orderAlpha (P : Parameters) :
    Algebra.leftMulMatrix (orderBasis P) (orderAlpha P) =
      SuborderUnits.companion ℤ (P.a₁ + P.a₂) (P.a₁ * P.a₂) := by
  have hα : orderAlpha P = orderBasis P 1 := by
    simpa using (orderBasis_apply P 1).symm
  have hAlphaSq : orderAlpha P * orderAlpha P = orderBasis P 2 := by
    rw [orderBasis_apply]
    norm_num
    ring
  have hAlphaCube : orderAlpha P * (orderAlpha P * orderAlpha P) =
      orderBasis P 0 + (-(P.a₁ * P.a₂)) • orderBasis P 1 +
        (P.a₁ + P.a₂) • orderBasis P 2 := by
    rw [← orderAlpha_pow_three_eq_basis P]
    ring
  have hrα (i : Fin 3) :
      (orderBasis P).repr (orderAlpha P) i = if i = 1 then 1 else 0 := by
    rw [hα]
    simp only [Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, one_mul, eq_comm]
  have hrAlphaSq (i : Fin 3) :
      (orderBasis P).repr (orderAlpha P * orderAlpha P) i =
        if i = 2 then 1 else 0 := by
    rw [hAlphaSq]
    simp only [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hrAlphaCube (i : Fin 3) :
      (orderBasis P).repr (orderAlpha P * (orderAlpha P * orderAlpha P)) i =
        (if i = 0 then 1 else 0) +
          (-(P.a₁ * P.a₂)) * (if i = 1 then 1 else 0) +
            (P.a₁ + P.a₂) * (if i = 2 then 1 else 0) := by
    rw [hAlphaCube, map_add, map_add, map_zsmul, map_zsmul]
    simp only [Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, one_mul, eq_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul, SuborderUnits.companion,
      orderBasis_apply, pow_two, hrα, hrAlphaSq, hrAlphaCube]

/-- The family `1, qα, qα²`, regarded as elements of `ℤ + qO`. -/
def scalarSuborderBasisVector (P : Parameters) (q : ℕ) :
    Fin 3 → scalarSuborder P q :=
  ![⟨1, 1, 0, by simp⟩,
    ⟨q • orderAlpha P, 0, orderAlpha P, by simp⟩,
    ⟨q • orderAlpha P ^ 2, 0, orderAlpha P ^ 2, by simp⟩]

@[simp] lemma coe_scalarSuborderBasisVector_zero (P : Parameters) (q : ℕ) :
    (scalarSuborderBasisVector P q 0 : orderCarrier P) = 1 := rfl

@[simp] lemma coe_scalarSuborderBasisVector_one (P : Parameters) (q : ℕ) :
    (scalarSuborderBasisVector P q 1 : orderCarrier P) = q • orderAlpha P := rfl

@[simp] lemma coe_scalarSuborderBasisVector_two (P : Parameters) (q : ℕ) :
    (scalarSuborderBasisVector P q 2 : orderCarrier P) =
      q • orderAlpha P ^ 2 := rfl

lemma coe_scalarSuborderBasisVector (P : Parameters) (q : ℕ) (i : Fin 3) :
    (scalarSuborderBasisVector P q i : orderCarrier P) =
      (if i = 0 then 1 else q • orderBasis P i) := by
  fin_cases i <;> simp [scalarSuborderBasisVector]

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

/-- The integral basis `1, qα, qα²` of `ℤ + qℤ[α]`. -/
def scalarSuborderBasis (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    Module.Basis (Fin 3) ℤ (scalarSuborder P q) :=
  Module.Basis.mk (scalarSuborderBasisVector_linearIndependent P q hq)
    (scalarSuborderBasisVector_span P q)

@[simp] lemma scalarSuborderBasis_apply (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) (i : Fin 3) :
    scalarSuborderBasis P q hq i = scalarSuborderBasisVector P q i :=
  Module.Basis.mk_apply _ _ i

/-- The same scalar suborder, now placed directly inside the maximal order. -/
def scalarSuborderInIntegers (P : Parameters) (q : ℕ) :
    Subalgebra ℤ (NumberField.RingOfIntegers (ABCField P)) :=
  (scalarSuborder P q).map (orderCarrier P).val

/-- Inclusion identifies the nested model of the scalar suborder with its
image in the maximal order. -/
def scalarSuborderEquivInIntegers (P : Parameters) (q : ℕ) :
    scalarSuborder P q ≃ₐ[ℤ] scalarSuborderInIntegers P q :=
  Subalgebra.equivMapOfInjective (scalarSuborder P q) (orderCarrier P).val
    (by exact Subtype.val_injective)

/-- `ℤ + qℤ[α]`, bundled as a cubic order for the regulator interface. -/
def scalarCubicOrder (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    Cusick.CubicOrder (ABCField P) where
  carrier := scalarSuborderInIntegers P q
  basis := (scalarSuborderBasis P q hq).map
    (scalarSuborderEquivInIntegers P q).toLinearEquiv

/-- The ordered real embeddings restricted to the scalar suborder. -/
def scalarSuborderEmbedding (P : Parameters) (q : ℕ) (i : Fin 3) :
    scalarSuborder P q →+* ℝ :=
  (orderEmbedding P i).comp (scalarSuborder P q).val

@[simp] lemma scalarSuborderEmbedding_apply (P : Parameters) (q : ℕ)
    (i : Fin 3) (x : scalarSuborder P q) :
    scalarSuborderEmbedding P q i x = orderEmbedding P i (x : orderCarrier P) :=
  rfl

/-- The Minkowski embedding matrix of the basis `1, qα, qα²`. -/
def scalarSuborderEmbeddingMatrix (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => scalarSuborderEmbedding P q i (scalarSuborderBasis P q hq j)

@[simp] lemma scalarSuborderEmbeddingMatrix_apply (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) (i j : Fin 3) :
    scalarSuborderEmbeddingMatrix P q hq i j =
      if j = 0 then 1 else (q : ℝ) * realRoot P i ^ (j : ℕ) := by
  fin_cases j <;>
    simp [scalarSuborderEmbeddingMatrix, scalarSuborderEmbedding,
      scalarSuborderBasisVector, map_nsmul, orderBasis_apply]

lemma scalarSuborderEmbeddingMatrix_eq (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    scalarSuborderEmbeddingMatrix P q hq =
      orderEmbeddingMatrix P * Matrix.diagonal ![1, (q : ℝ), (q : ℝ)] := by
  ext i j
  fin_cases j <;>
    simp [scalarSuborderEmbeddingMatrix_apply, orderEmbeddingMatrix,
      Matrix.mul_diagonal, mul_comm]

lemma scalarSuborderEmbeddingMatrix_det (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    (scalarSuborderEmbeddingMatrix P q hq).det =
      (q : ℝ) ^ 2 * (orderEmbeddingMatrix P).det := by
  rw [scalarSuborderEmbeddingMatrix_eq, Matrix.det_mul, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, pow_two, mul_comm]

lemma scalarSuborderEmbeddingMatrix_det_pos (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    0 < (scalarSuborderEmbeddingMatrix P q hq).det := by
  rw [scalarSuborderEmbeddingMatrix_det]
  exact mul_pos (sq_pos_of_ne_zero (by exact_mod_cast hq))
    (orderEmbeddingMatrix_det_pos P)

lemma scalarSuborderEmbeddingMatrix_det_ne_zero (P : Parameters) (q : ℕ)
    (hq : q ≠ 0) :
    (scalarSuborderEmbeddingMatrix P q hq).det ≠ 0 :=
  ne_of_gt (scalarSuborderEmbeddingMatrix_det_pos P q hq)

end ArithmeticConstruction
end CubicPeriodicTori
