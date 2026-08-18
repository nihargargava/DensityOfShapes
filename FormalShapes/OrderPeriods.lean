import DynamicsCore
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
The exact matrix criterion underlying Lemma 2.6 of the paper, used by the
arithmetic realization in `paper_construction`.
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

@[simp] lemma embeddingSL_apply (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0)
    (i j : Fin 3) :
    embeddingSL b σ hdet i j =
      ![(embeddingMatrix b σ).det⁻¹, 1, 1] i * σ i (b j) := by
  simp [embeddingSL, embeddingMatrix, Matrix.diagonal_mul]

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

lemma real_sign_mul_self_eq_abs (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]
    ring
  · simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx]
    ring

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

@[simp] lemma orientedUnitSign_apply (b : Module.Basis (Fin 3) ℤ A)
    (σ : Fin 3 → A →+* ℝ) (hdet : (embeddingMatrix b σ).det ≠ 0)
    (x : Aˣ) (hx : (Algebra.leftMulMatrix b (x : A)).det = 1)
    (i j : Fin 3) :
    ((orientedUnitSign b σ hdet x hx : signDiagonal) : SL3R) i j =
      Matrix.diagonal (fun k ↦ Real.sign (σ k (x : A))) i j := rfl

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
