import CusickRegulator
import Mathlib.RingTheory.Localization.NormTrace
open scoped NumberField
noncomputable section
namespace Cusick.CubicOrder
open NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem
variable {K : Type*} [Field K] [NumberField K] [Fact (Module.finrank ℚ K = 3)]
  (O : Cusick.CubicOrder K) [NumberField.IsTotallyReal K]

open scoped Classical in
noncomputable def pairPlace3 : Fin 2 ≃ {w : InfinitePlace K // w ≠ w₀} :=
  (finCongr O.unitRank_eq_two.symm).trans (NumberField.Units.equivFinRank K)

open scoped Classical in
noncomputable def threePlace : Fin 3 ≃ InfinitePlace K :=
  (finSuccEquiv 2).trans ((Equiv.optionSubtype w₀).symm (O.pairPlace3)).val

open scoped Classical in
noncomputable def placeAlgHomEquiv : InfinitePlace K ≃ (K →ₐ[ℚ] ℂ) where
  toFun w := w.embedding.toRatAlgHom
  invFun φ := InfinitePlace.mk φ.toRingHom
  left_inv w := InfinitePlace.mk_embedding w
  right_inv φ := by
    apply AlgHom.ext
    intro x
    exact RingHom.congr_fun (InfinitePlace.embedding_mk_eq_of_isReal
      (NumberField.IsTotallyReal.complexEmbedding_isReal φ.toRingHom)) x

open scoped Classical in
noncomputable def realConjugate (x : K) (i : Fin 3) : ℝ :=
  InfinitePlace.embedding_of_isReal
    (NumberField.IsTotallyReal.isReal (O.threePlace i)) x

lemma map_discr_roi2 (b : Fin 3 → 𝓞 K) :
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
lemma power_discriminant_eq_conjugates (u : (𝓞 K)ˣ) :
    ((Algebra.discr ℤ (fun i : Fin 3 => (u : 𝓞 K) ^ (i : ℕ))).natAbs : ℝ) =
      ((O.realConjugate (u : K) 0 - O.realConjugate (u : K) 1) *
       (O.realConjugate (u : K) 0 - O.realConjugate (u : K) 2) *
       (O.realConjugate (u : K) 1 - O.realConjugate (u : K) 2)) ^ 2 := by
  let x : K := (u : K)
  let e : Fin 3 ≃ (K →ₐ[ℚ] ℂ) := O.threePlace.trans (placeAlgHomEquiv (K := K))
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
  have hdiscQ := map_discr_roi2 (fun i : Fin 3 => (u : 𝓞 K) ^ (i : ℕ))
  have hdiscR :
      ((Algebra.discr ℤ (fun i : Fin 3 => (u : 𝓞 K) ^ (i : ℕ)) : ℤ) : ℝ) =
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

end Cusick.CubicOrder

namespace Cusick.CubicOrder
open NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem
variable {K : Type*} [Field K] [NumberField K] [Fact (Module.finrank ℚ K = 3)]
  (O : Cusick.CubicOrder K) [NumberField.IsTotallyReal K]

open scoped Classical in
lemma abs_realConjugate (u : (𝓞 K)ˣ) (i : Fin 3) :
    |O.realConjugate (u : K) i| = O.threePlace i (u : K) := by
  simpa [realConjugate, Real.norm_eq_abs] using
    (InfinitePlace.norm_embedding_of_isReal
      (NumberField.IsTotallyReal.isReal (O.threePlace i)) (u : K))

open scoped Classical in
lemma abs_prod_realConjugates (u : (𝓞 K)ˣ) :
    |O.realConjugate (u : K) 0 * O.realConjugate (u : K) 1 *
      O.realConjugate (u : K) 2| = 1 := by
  rw [abs_mul, abs_mul, O.abs_realConjugate u 0,
    O.abs_realConjugate u 1, O.abs_realConjugate u 2]
  rw [← Fin.prod_univ_three (fun i : Fin 3 => O.threePlace i (u : K))]
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

end Cusick.CubicOrder
