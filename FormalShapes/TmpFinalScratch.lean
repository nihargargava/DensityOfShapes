import TmpShort
import TmpConj
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
open scoped NumberField IntermediateField
noncomputable section
namespace Cusick.CubicOrder
open NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem
variable {K : Type*} [Field K] [NumberField K] [Fact (Module.finrank ℚ K = 3)]
  (O : Cusick.CubicOrder K) [NumberField.IsTotallyReal K]

-- imported tmp short names pairPlace, fundLog, exists_short_unit
-- imported tmp conj names pairPlace3, threePlace, realConjugate, etc

open scoped Classical in
lemma test_logs_three_eq_shortQ (u : (𝓞 K)ˣ) :
    Real.log |O.realConjugate (u : K) 0| ^ 2 +
      Real.log |O.realConjugate (u : K) 1| ^ 2 +
      Real.log |O.realConjugate (u : K) 2| ^ 2 =
    2 * (Real.log ((O.pairPlace 0).val u)^2 +
      Real.log ((O.pairPlace 0).val u) * Real.log ((O.pairPlace 1).val u) +
      Real.log ((O.pairPlace 1).val u)^2) := by
  have hpair : O.pairPlace3 = O.pairPlace := by
    simp [pairPlace3, pairPlace]
  have h0 : O.threePlace 0 = w₀ := by
    simp [threePlace]
  have h1 : O.threePlace 1 = (O.pairPlace 0).val := by
    rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) by rfl]
    simp only [threePlace, Equiv.trans_apply, finSuccEquiv_succ, hpair,
      Equiv.optionSubtype_symm_apply_apply_some]
  have h2 : O.threePlace 2 = (O.pairPlace 1).val := by
    rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) by rfl]
    simp only [threePlace, Equiv.trans_apply, finSuccEquiv_succ, hpair,
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
lemma test_degree (u : (𝓞 K)ˣ)
    (hpos : 0 < 2 *
      (Real.log ((O.pairPlace 0).val u)^2 +
       Real.log ((O.pairPlace 0).val u) * Real.log ((O.pairPlace 1).val u) +
       Real.log ((O.pairPlace 1).val u)^2)) :
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
      rw [show (w (u : K)) = w x by rfl, ← hq]
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
lemma test_order_power (v : O.carrierˣ)
    (hdeg : (minpoly ℚ (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K))).natDegree = 3) :
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
  have hsigned : Algebra.discr ℤ b = P.det ^ 2 * O.signedDiscriminant := by
    have hdisc := Algebra.discr_of_matrix_vecMul
      (fun i => (O.basis i : 𝓞 K)) P
    rw [hfamily] at hdisc
    simpa only [signedDiscriminant] using hdisc
  have hbK : (fun i => (b i : K)) =
      (fun i : Fin 3 => (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) ^ (i : ℕ))) := by
    funext i
    rfl
  have hbne : Algebra.discr ℤ b ≠ 0 := by
    intro hbzero
    have hmap := map_discr_roi2 b
    rw [hbzero, map_zero, hbK] at hmap
    -- use exact local copy from OrderPower? add inline via basis omitted? imported? no
    have hne : Algebra.discr ℚ
        (fun i : Fin 3 =>
          (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)) ^ (i : ℕ)) ≠ 0 := by
      have hxint : IsIntegral ℚ (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)) :=
        IsIntegral.of_finite ℚ _
      have hprim : ℚ⟮algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)⟯ = ⊤ := by
        apply (Field.primitive_element_iff_minpoly_natDegree_eq ℚ _).2
        exact hdeg.trans (Fact.out : Module.finrank ℚ K = 3).symm
      have hadj : Algebra.adjoin ℚ {algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)} = ⊤ := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxint.isAlgebraic]
        exact congrArg IntermediateField.toSubalgebra hprim
      let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hxint hadj
      have hpbdim : pb.dim = 3 := by simpa [pb] using hdeg
      let bas : Module.Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr hpbdim)
      have hbasi (i : Fin 3) : bas i =
          (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)) ^ (i : ℕ) := by
        change (pb.basis.reindex (finCongr hpbdim)) i = _
        rw [Module.Basis.coe_reindex]
        simp only [Function.comp_apply]
        rw [PowerBasis.basis_eq_pow]
        rw [show pb.gen = algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K) by
          exact PowerBasis.ofAdjoinEqTop_gen hxint hadj]
        have hi : (((finCongr hpbdim).symm i : Fin pb.dim) : ℕ) = (i : ℕ) := by rfl
        rw [hi]
      have hf : (fun i : Fin 3 =>
          (algebraMap (𝓞 K) K ((v : O.carrier) : 𝓞 K)) ^ (i : ℕ)) =
          (bas : Fin 3 → K) := by funext i; exact (hbasi i).symm
      rw [hf]
      exact Algebra.discr_not_zero_of_basis ℚ bas
    exact hne hmap.symm
  have hP : P.det ≠ 0 := by
    intro hPzero
    apply hbne
    rw [hsigned, hPzero]
    norm_num
  have hPabs : 1 ≤ P.det.natAbs := (Int.natAbs_pos.mpr hP).nat_succ_le
  have habs : (Algebra.discr ℤ b).natAbs =
      P.det.natAbs ^ 2 * O.discriminant := by
    rw [hsigned, Int.natAbs_mul, Int.natAbs_pow]
    rfl
  change O.discriminant ≤ (Algebra.discr ℤ b).natAbs
  rw [habs]
  exact Nat.le_mul_of_pos_left O.discriminant (by positivity)

open scoped Classical in
lemma test_preimage {u : (𝓞 K)ˣ} (hu : u ∈ O.unitSubgroup) :
    ∃ v : O.carrierˣ, O.unitMap v = u := hu

lemma test_disc_four : 4 ≤ O.discriminant := by
  have hreal : (4 : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
    have h := NumberField.abs_discr_ge' (K := K)
    rw [(Fact.out : Module.finrank ℚ K = 3),
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h
    norm_num at h ⊢
    exact le_trans (by norm_num) h
  have hz : (4 : ℤ) ≤ |NumberField.discr K| := by exact_mod_cast hreal
  rw [← Int.natCast_natAbs] at hz
  have hn : 4 ≤ (NumberField.discr K).natAbs := by exact_mod_cast hz
  rw [O.discriminant_eq_index_sq_mul]
  calc
    4 ≤ (NumberField.discr K).natAbs := hn
    _ ≤ O.additiveIndex ^ 2 * (NumberField.discr K).natAbs := by
      have hi : 0 < O.additiveIndex := Nat.pos_of_ne_zero O.additiveIndex_ne_zero
      have hi2 : 1 ≤ O.additiveIndex ^ 2 := by nlinarith
      simpa using Nat.mul_le_mul_right (NumberField.discr K).natAbs hi2

end Cusick.CubicOrder
