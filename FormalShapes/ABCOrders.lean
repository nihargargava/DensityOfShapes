import CusickRegulator
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Analysis.Polynomial.Order
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.Resultant.Basic

noncomputable section

namespace ABCOrders

open Polynomial

def abcPolynomial (a₁ a₂ : ℤ) : Polynomial ℤ :=
  X * (X - C a₁) * (X - C a₂) - 1

lemma abcPolynomial_monic (a₁ a₂ : ℤ) :
    (abcPolynomial a₁ a₂).Monic := by
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

lemma abcPolynomial_natDegree (a₁ a₂ : ℤ) :
    (abcPolynomial a₁ a₂).natDegree = 3 := by
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
  rw [abcPolynomial,
    natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlt),
    hp12.natDegree_mul (monic_X_sub_C a₂),
    monic_X.natDegree_mul (monic_X_sub_C a₁),
    natDegree_X, natDegree_X_sub_C, natDegree_X_sub_C]

lemma abcPolynomial_eval (a₁ a₂ x : ℤ) :
    (abcPolynomial a₁ a₂).eval x = x * (x - a₁) * (x - a₂) - 1 := by
  simp [abcPolynomial]

lemma abcPolynomial_eval_one_ne_zero {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    (abcPolynomial a₁ a₂).eval 1 ≠ 0 := by
  rw [abcPolynomial_eval]
  have h₁ : 2 ≤ a₁ - 1 := by omega
  have h₂ : 3 ≤ a₂ - 1 := by omega
  have hmul : 6 ≤ (a₁ - 1) * (a₂ - 1) := by nlinarith
  nlinarith

lemma abcPolynomial_eval_neg_one_ne_zero {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    (abcPolynomial a₁ a₂).eval (-1) ≠ 0 := by
  rw [abcPolynomial_eval]
  have h₁ : 0 < 1 + a₁ := by omega
  have h₂ : 0 < 1 + a₂ := by omega
  have hmul : 0 < (1 + a₁) * (1 + a₂) := mul_pos h₁ h₂
  nlinarith

def abcPolynomialQ (a₁ a₂ : ℤ) : Polynomial ℚ :=
  (abcPolynomial a₁ a₂).map (Int.castRingHom ℚ)

def abcPolynomialR (a₁ a₂ : ℤ) : Polynomial ℝ :=
  (abcPolynomial a₁ a₂).map (Int.castRingHom ℝ)

/-- Parameters for the ABC family, bundled so their inequalities are available
to the typeclass system when constructing the number field. -/
structure Parameters where
  a₁ : ℤ
  a₂ : ℤ
  three_le : 3 ≤ a₁
  lt : a₁ < a₂

lemma abcPolynomialR_eval (a₁ a₂ : ℤ) (x : ℝ) :
    (abcPolynomialR a₁ a₂).eval x =
      x * (x - a₁) * (x - a₂) - 1 := by
  simp [abcPolynomialR, abcPolynomial]

/-- The three separated real roots used to identify the ABC field as totally
real.  The intervals are the ones used in the paper. -/
lemma exists_three_real_roots {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    ∃ r₀ r₁ r₂ : ℝ,
      r₀ ∈ Set.Icc 0 1 ∧
      r₁ ∈ Set.Icc ((a₁ : ℝ) - 1) a₁ ∧
      r₂ ∈ Set.Icc (a₂ : ℝ) (a₂ + 1) ∧
      (abcPolynomialR a₁ a₂).IsRoot r₀ ∧
      (abcPolynomialR a₁ a₂).IsRoot r₁ ∧
      (abcPolynomialR a₁ a₂).IsRoot r₂ := by
  let p := abcPolynomialR a₁ a₂
  have ha₁r : (3 : ℝ) ≤ a₁ := by exact_mod_cast ha₁
  have ha₂r : (a₁ : ℝ) < a₂ := by exact_mod_cast ha₂
  have h0 : p.eval 0 ≤ 0 := by simp [p, abcPolynomialR_eval]
  have h1 : 0 ≤ p.eval 1 := by
    rw [show p.eval 1 =
      (1 : ℝ) * (1 - a₁) * (1 - a₂) - 1 by
        simp [p, abcPolynomialR_eval]]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha₁r) (sub_nonneg.mpr ha₂r.le)]
  have hz₀ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    p.continuous.continuousOn ⟨h0, h1⟩
  rcases hz₀ with ⟨r₀, hr₀I, hr₀⟩
  have hmidL : 0 ≤ p.eval ((a₁ : ℝ) - 1) := by
    rw [show p.eval ((a₁ : ℝ) - 1) =
      ((a₁ : ℝ) - 1) * (((a₁ : ℝ) - 1) - a₁) *
        (((a₁ : ℝ) - 1) - a₂) - 1 by
          simp [p, abcPolynomialR_eval]]
    have ha₁m : 0 ≤ (a₁ : ℝ) - 1 := by linarith
    have hgap : 0 ≤ (a₂ : ℝ) - a₁ + 1 := by linarith
    nlinarith [mul_nonneg ha₁m hgap]
  have hmidR : p.eval (a₁ : ℝ) ≤ 0 := by simp [p, abcPolynomialR_eval]
  have hz₁ := intermediate_value_Icc'
    (by norm_num : (a₁ : ℝ) - 1 ≤ a₁)
    p.continuous.continuousOn ⟨hmidR, hmidL⟩
  rcases hz₁ with ⟨r₁, hr₁I, hr₁⟩
  have hrightL : p.eval (a₂ : ℝ) ≤ 0 := by simp [p, abcPolynomialR_eval]
  have hrightR : 0 ≤ p.eval ((a₂ : ℝ) + 1) := by
    rw [show p.eval ((a₂ : ℝ) + 1) =
      ((a₂ : ℝ) + 1) * (((a₂ : ℝ) + 1) - a₁) *
        (((a₂ : ℝ) + 1) - a₂) - 1 by
          simp [p, abcPolynomialR_eval]]
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
  r₀_root : (abcPolynomialR P.a₁ P.a₂).IsRoot r₀
  r₁_root : (abcPolynomialR P.a₁ P.a₂).IsRoot r₁
  r₂_root : (abcPolynomialR P.a₁ P.a₂).IsRoot r₂

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

@[simp] lemma root0_eq (P : Parameters) : root0 P = (rootTriple P).r₀ := rfl
@[simp] lemma root1_eq (P : Parameters) : root1 P = (rootTriple P).r₁ := rfl
@[simp] lemma root2_eq (P : Parameters) : root2 P = (rootTriple P).r₂ := rfl

lemma realRoot_root (P : Parameters) (i : Fin 3) :
    (abcPolynomialR P.a₁ P.a₂).IsRoot (realRoot P i) := by
  fin_cases i
  · exact (rootTriple P).r₀_root
  · exact (rootTriple P).r₁_root
  · exact (rootTriple P).r₂_root

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

lemma root0_strictBounds (P : Parameters) : 0 < root0 P ∧ root0 P < 1 := by
  have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hroot := (rootTriple P).r₀_root
  rw [Polynomial.IsRoot, abcPolynomialR_eval] at hroot
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

lemma root1_strictBounds (P : Parameters) :
    (P.a₁ : ℝ) - 1 < root1 P ∧ root1 P < P.a₁ := by
  have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hroot := (rootTriple P).r₁_root
  rw [Polynomial.IsRoot, abcPolynomialR_eval] at hroot
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

lemma root2_strictBounds (P : Parameters) :
    (P.a₂ : ℝ) < root2 P ∧ root2 P < P.a₂ + 1 := by
  have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  have hroot := (rootTriple P).r₂_root
  rw [Polynomial.IsRoot, abcPolynomialR_eval] at hroot
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

lemma roots_strict_order (P : Parameters) :
    root0 P < root1 P ∧ root1 P < root2 P := by
  constructor
  · have ha₁ : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
    linarith [(root0_strictBounds P).2, (root1_strictBounds P).1]
  · have ha₂ : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
    linarith [(root1_strictBounds P).2, (root2_strictBounds P).1]

lemma abcPolynomialQ_eval₂_real_eq
    (a₁ a₂ : ℤ) (x : ℝ) :
    Polynomial.eval₂ (algebraMap ℚ ℝ) x (abcPolynomialQ a₁ a₂) =
      (abcPolynomialR a₁ a₂).eval x := by
  simp [abcPolynomialQ, abcPolynomialR, abcPolynomial,
    Polynomial.eval₂_eq_eval_map]

lemma abcPolynomialQ_monic (a₁ a₂ : ℤ) :
    (abcPolynomialQ a₁ a₂).Monic :=
  (abcPolynomial_monic a₁ a₂).map (Int.castRingHom ℚ)

lemma abcPolynomialQ_natDegree (a₁ a₂ : ℤ) :
    (abcPolynomialQ a₁ a₂).natDegree = 3 := by
  rw [abcPolynomialQ, (abcPolynomial_monic a₁ a₂).natDegree_map]
  exact abcPolynomial_natDegree a₁ a₂

lemma abcPolynomialQ_irreducible {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    Irreducible (abcPolynomialQ a₁ a₂) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [abcPolynomialQ_natDegree]
  · intro x hx
    have hroot : aeval x (abcPolynomial a₁ a₂) = 0 := by
      rw [IsRoot, abcPolynomialQ, eval_map] at hx
      simpa [aeval_def] using hx
    obtain ⟨z, rfl, hz⟩ := exists_integer_of_is_root_of_monic
      (abcPolynomial_monic a₁ a₂) hroot
    have hz' : z ∣ (1 : ℤ) := by
      simpa [abcPolynomial, coeff_sub] using hz
    have hzunit : IsUnit z := isUnit_iff_dvd_one.mpr hz'
    rcases Int.isUnit_iff.mp hzunit with rfl | rfl
    · have ha₁q : (3 : ℚ) ≤ a₁ := by exact_mod_cast ha₁
      have ha₂q : (a₁ : ℚ) < a₂ := by exact_mod_cast ha₂
      simp [abcPolynomialQ, abcPolynomial, IsRoot] at hx
      nlinarith
    · have ha₁q : (3 : ℚ) ≤ a₁ := by exact_mod_cast ha₁
      have ha₂q : (a₁ : ℚ) < a₂ := by exact_mod_cast ha₂
      simp [abcPolynomialQ, abcPolynomial, IsRoot] at hx
      nlinarith

lemma abcPolynomial_irreducible {a₁ a₂ : ℤ}
    (ha₁ : 3 ≤ a₁) (ha₂ : a₁ < a₂) :
    Irreducible (abcPolynomial a₁ a₂) := by
  exact ((abcPolynomial_monic a₁ a₂).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mpr (abcPolynomialQ_irreducible ha₁ ha₂)

instance (P : Parameters) : Fact (Irreducible (abcPolynomialQ P.a₁ P.a₂)) :=
  ⟨abcPolynomialQ_irreducible P.three_le P.lt⟩

/-- The cubic field generated by a root of the ABC polynomial. -/
abbrev ABCField (P : Parameters) := AdjoinRoot (abcPolynomialQ P.a₁ P.a₂)

lemma field_finrank (P : Parameters) : Module.finrank ℚ (ABCField P) = 3 := by
  rw [(AdjoinRoot.powerBasis (abcPolynomialQ_monic P.a₁ P.a₂).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, abcPolynomialQ_natDegree]

instance (P : Parameters) : Fact (Module.finrank ℚ (ABCField P) = 3) :=
  ⟨field_finrank P⟩

/-- The distinguished root in the ABC number field. -/
def alpha (P : Parameters) : ABCField P :=
  AdjoinRoot.root (abcPolynomialQ P.a₁ P.a₂)

/-- A real root of the defining polynomial gives a real embedding of the ABC
field. -/
def realLift (P : Parameters) (r : ℝ)
    (hr : (abcPolynomialR P.a₁ P.a₂).IsRoot r) : ABCField P →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) r <| by
    rw [abcPolynomialQ_eval₂_real_eq]
    exact hr

@[simp] lemma realLift_alpha (P : Parameters) (r : ℝ)
    (hr : (abcPolynomialR P.a₁ P.a₂).IsRoot r) :
    realLift P r hr (alpha P) = r := by
  exact AdjoinRoot.lift_root _

/-- Regard a real embedding as a complex embedding fixed by conjugation. -/
def complexOfRealEmbedding {K : Type*} [Field K] (f : K →+* ℝ) :
    { φ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ } :=
  ⟨Complex.ofRealHom.comp f, by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq]⟩

@[simp] lemma complexOfRealEmbedding_apply {K : Type*} [Field K]
    (f : K →+* ℝ) (x : K) :
    (complexOfRealEmbedding f : K →+* ℂ) x = f x :=
  rfl

noncomputable def rootEmbedding (P : Parameters) (i : Fin 3) :
    ABCField P →+* ℝ :=
  realLift P (realRoot P i) (realRoot_root P i)

noncomputable def rootPlace (P : Parameters) (i : Fin 3) :
    NumberField.InfinitePlace (ABCField P) :=
  NumberField.InfinitePlace.mk (complexOfRealEmbedding (rootEmbedding P i))

lemma realRoot_nonneg (P : Parameters) (i : Fin 3) : 0 ≤ realRoot P i := by
  have ha₁r : (3 : ℝ) ≤ P.a₁ := by exact_mod_cast P.three_le
  have ha₂r : (P.a₁ : ℝ) < P.a₂ := by exact_mod_cast P.lt
  fin_cases i
  · exact (rootTriple P).r₀_mem.1
  · exact le_trans (by linarith) (rootTriple P).r₁_mem.1
  · exact le_trans (by linarith) (rootTriple P).r₂_mem.1

@[simp] lemma rootPlace_alpha (P : Parameters) (i : Fin 3) :
    rootPlace P i (alpha P) = realRoot P i := by
  rw [rootPlace, NumberField.InfinitePlace.apply]
  simp [rootEmbedding, Real.norm_eq_abs, abs_of_nonneg (realRoot_nonneg P i)]

lemma rootPlace_injective (P : Parameters) : Function.Injective (rootPlace P) := by
  intro i j h
  apply realRoot_injective P
  rw [← rootPlace_alpha P i, ← rootPlace_alpha P j, h]

/-- The ABC field is totally real: the three disjoint sign-change intervals
produce three real embeddings, exhausting its three complex embeddings. -/
theorem abcField_isTotallyReal (P : Parameters) :
    NumberField.IsTotallyReal (ABCField P) := by
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
      (fun e : { φ : ABCField P →+* ℂ //
        NumberField.ComplexEmbedding.IsReal φ } ↦ (e.1 (alpha P)).re) h
    exact hr₀₁ (by simpa [e₀, e₁] using hv)
  have he₁₂ : e₁ ≠ e₂ := by
    intro h
    have hv := congrArg
      (fun e : { φ : ABCField P →+* ℂ //
        NumberField.ComplexEmbedding.IsReal φ } ↦ (e.1 (alpha P)).re) h
    exact hr₁₂ (by simpa [e₁, e₂] using hv)
  have he₀₂ : e₀ ≠ e₂ := by
    intro h
    have hv := congrArg
      (fun e : { φ : ABCField P →+* ℂ //
        NumberField.ComplexEmbedding.IsReal φ } ↦ (e.1 (alpha P)).re) h
    exact hr₀₂ (by simpa [e₀, e₂] using hv)
  let e : Fin 3 → { φ : ABCField P →+* ℂ //
      NumberField.ComplexEmbedding.IsReal φ } := ![e₀, e₁, e₂]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have hcard : 3 ≤ Fintype.card { φ : ABCField P →+* ℂ //
      NumberField.ComplexEmbedding.IsReal φ } := by
    simpa using Fintype.card_le_of_injective e he
  rw [NumberField.InfinitePlace.card_real_embeddings] at hcard
  have hsignature :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (ABCField P)
  rw [field_finrank] at hsignature
  apply NumberField.nrComplexPlaces_eq_zero_iff.mp
  omega

noncomputable instance (P : Parameters) :
    NumberField.IsTotallyReal (ABCField P) :=
  abcField_isTotallyReal P

noncomputable def rootPlaceEquiv (P : Parameters) :
    Fin 3 ≃ NumberField.InfinitePlace (ABCField P) :=
  Equiv.ofBijective (rootPlace P) <|
    (Fintype.bijective_iff_injective_and_card (rootPlace P)).mpr ⟨
      rootPlace_injective P, by
        rw [Fintype.card_fin,
          Cusick.CubicOrder.card_infinitePlaces_eq_three (K := ABCField P)]⟩

/-- The first two real places, indexed after omitting the third. -/
noncomputable def firstTwoPlaces (P : Parameters) :
    Fin 2 ≃ {w : NumberField.InfinitePlace (ABCField P) //
      w ≠ rootPlace P 2} := by
  let f : Fin 2 → {w : NumberField.InfinitePlace (ABCField P) //
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

lemma alpha_abcPolynomialQ (P : Parameters) :
    Polynomial.aeval (alpha P) (abcPolynomialQ P.a₁ P.a₂) = 0 := by
  change Polynomial.eval₂ (AdjoinRoot.of _) (AdjoinRoot.root _)
    (abcPolynomialQ P.a₁ P.a₂) = 0
  exact AdjoinRoot.eval₂_root _

lemma alpha_abcPolynomial (P : Parameters) :
    Polynomial.aeval (alpha P) (abcPolynomial P.a₁ P.a₂) = 0 := by
  rw [aeval_def]
  have hmap : algebraMap ℤ (ABCField P) =
      (AdjoinRoot.of (abcPolynomialQ P.a₁ P.a₂)).comp (Int.castRingHom ℚ) := by
    ext z
    simp
  rw [hmap, ← Polynomial.eval₂_map]
  change Polynomial.eval₂ _ _ (abcPolynomialQ P.a₁ P.a₂) = 0
  exact AdjoinRoot.eval₂_root _

lemma alpha_isIntegral (P : Parameters) : IsIntegral ℤ (alpha P) :=
  ⟨abcPolynomial P.a₁ P.a₂, abcPolynomial_monic _ _, alpha_abcPolynomial P⟩

lemma alpha_mul_sub_mul_sub (P : Parameters) :
    alpha P * (alpha P - algebraMap ℤ (ABCField P) P.a₁) *
      (alpha P - algebraMap ℤ (ABCField P) P.a₂) = 1 := by
  have h := alpha_abcPolynomial P
  simp [abcPolynomial, map_mul, map_sub] at h
  exact sub_eq_zero.mp h

/-- The distinguished algebraic integer, as an element of the maximal order. -/
def alphaInteger (P : Parameters) : NumberField.RingOfIntegers (ABCField P) :=
  ⟨alpha P, alpha_isIntegral P⟩

lemma alphaInteger_minpoly (P : Parameters) :
    minpoly ℤ (alphaInteger P) = abcPolynomial P.a₁ P.a₂ := by
  have hroot : Polynomial.aeval (alphaInteger P)
      (abcPolynomial P.a₁ P.a₂) = 0 := by
    rw [aeval_def]
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_zero, Polynomial.hom_eval₂]
    have halpha : algebraMap (NumberField.RingOfIntegers (ABCField P)) (ABCField P)
        (alphaInteger P) = alpha P := by
      unfold alphaInteger
      exact NumberField.RingOfIntegers.map_mk _ _
    rw [halpha]
    simpa [alphaInteger, aeval_def, IsScalarTower.algebraMap_eq ℤ
      (NumberField.RingOfIntegers (ABCField P)) (ABCField P)] using alpha_abcPolynomial P
  let hI : IsIntegral ℤ (alphaInteger P) :=
    NumberField.RingOfIntegers.isIntegral _
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hI hroot
  have hqUnit : IsUnit q :=
    (abcPolynomial_irreducible P.three_le P.lt).isUnit_or_isUnit hq |>.resolve_left
      (minpoly.not_isUnit ℤ (alphaInteger P))
  apply Polynomial.eq_of_monic_of_associated (minpoly.monic hI)
    (abcPolynomial_monic P.a₁ P.a₂)
  exact ⟨hqUnit.unit, by simpa [hqUnit.unit_spec] using hq.symm⟩

/-- The monogenic order `ℤ[α]` inside the ring of integers. -/
def orderCarrier (P : Parameters) :
    Subalgebra ℤ (NumberField.RingOfIntegers (ABCField P)) :=
  Algebra.adjoin ℤ ({alphaInteger P} : Set (NumberField.RingOfIntegers (ABCField P)))

/-- The distinguished generator, now viewed inside the monogenic order. -/
def orderAlpha (P : Parameters) : orderCarrier P :=
  ⟨alphaInteger P, Algebra.subset_adjoin (Set.mem_singleton _)⟩

def orderAlphaSubOne (P : Parameters) : orderCarrier P :=
  orderAlpha P - algebraMap ℤ (orderCarrier P) P.a₁

def orderAlphaSubTwo (P : Parameters) : orderCarrier P :=
  orderAlpha P - algebraMap ℤ (orderCarrier P) P.a₂

lemma order_generators_mul (P : Parameters) :
    orderAlpha P * orderAlphaSubOne P * orderAlphaSubTwo P = 1 := by
  apply Subtype.ext
  apply NumberField.RingOfIntegers.ext
  simp only [orderAlpha, orderAlphaSubOne, orderAlphaSubTwo,
    Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_algebraMap,
    map_mul, map_sub]
  have halpha : algebraMap (NumberField.RingOfIntegers (ABCField P)) (ABCField P)
      (alphaInteger P) = alpha P := by
    unfold alphaInteger
    exact NumberField.RingOfIntegers.map_mk _ _
  rw [halpha, ← IsScalarTower.algebraMap_apply ℤ
    (NumberField.RingOfIntegers (ABCField P)) (ABCField P),
    ← IsScalarTower.algebraMap_apply ℤ
      (NumberField.RingOfIntegers (ABCField P)) (ABCField P)]
  exact alpha_mul_sub_mul_sub P

/-- The three canonical ABC units. -/
noncomputable def alphaUnit (P : Parameters) : (orderCarrier P)ˣ :=
  Units.mkOfMulEqOne (orderAlpha P) (orderAlphaSubOne P * orderAlphaSubTwo P) <| by
    simpa [mul_assoc] using order_generators_mul P

noncomputable def alphaSubOneUnit (P : Parameters) : (orderCarrier P)ˣ :=
  Units.mkOfMulEqOne (orderAlphaSubOne P) (orderAlphaSubTwo P * orderAlpha P) <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using order_generators_mul P

noncomputable def alphaSubTwoUnit (P : Parameters) : (orderCarrier P)ˣ :=
  Units.mkOfMulEqOne (orderAlphaSubTwo P) (orderAlpha P * orderAlphaSubOne P) <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using order_generators_mul P

@[simp] lemma coe_alphaUnit (P : Parameters) :
    (alphaUnit P : orderCarrier P) = orderAlpha P := rfl

@[simp] lemma coe_alphaSubOneUnit (P : Parameters) :
    (alphaSubOneUnit P : orderCarrier P) = orderAlphaSubOne P := rfl

@[simp] lemma coe_alphaSubTwoUnit (P : Parameters) :
    (alphaSubTwoUnit P : orderCarrier P) = orderAlphaSubTwo P := rfl

/-- The power basis generated by `α` before reindexing its degree by the
explicit equality `deg(f) = 3`. -/
noncomputable def orderPowerBasis (P : Parameters) :
    PowerBasis ℤ (orderCarrier P) := by
  let hI : IsIntegral ℤ (alphaInteger P) :=
    NumberField.RingOfIntegers.isIntegral _
  exact Algebra.adjoin.powerBasis' hI

lemma orderPowerBasis_dim (P : Parameters) : (orderPowerBasis P).dim = 3 := by
  rw [orderPowerBasis, Algebra.adjoin.powerBasis'_dim, alphaInteger_minpoly,
    abcPolynomial_natDegree]

@[simp] lemma orderPowerBasis_gen (P : Parameters) :
    (orderPowerBasis P).gen = orderAlpha P := by
  unfold orderPowerBasis
  rw [Algebra.adjoin.powerBasis'_gen]
  apply Subtype.ext
  rfl

/-- The power basis `1, α, α²` of the ABC order. -/
noncomputable def orderBasis (P : Parameters) :
    Module.Basis (Fin 3) ℤ (orderCarrier P) :=
  (orderPowerBasis P).basis.reindex (finCongr (orderPowerBasis_dim P))

@[simp] lemma orderBasis_apply (P : Parameters) (i : Fin 3) :
    orderBasis P i = orderAlpha P ^ (i : ℕ) := by
  simp [orderBasis, PowerBasis.basis_eq_pow]

@[simp] lemma orderBasis_zero (P : Parameters) : orderBasis P 0 = 1 := by
  simp

/-- The three ordered real embeddings restricted to the ABC order. -/
noncomputable def orderEmbedding (P : Parameters) (i : Fin 3) :
    orderCarrier P →+* ℝ :=
  (rootEmbedding P i).comp (algebraMap (orderCarrier P) (ABCField P))

@[simp] lemma orderEmbedding_orderAlpha (P : Parameters) (i : Fin 3) :
    orderEmbedding P i (orderAlpha P) = realRoot P i := by
  change rootEmbedding P i (alpha P) = realRoot P i
  simp [rootEmbedding]

@[simp] lemma orderEmbedding_orderBasis (P : Parameters) (i j : Fin 3) :
    orderEmbedding P i (orderBasis P j) = realRoot P i ^ (j : ℕ) := by
  rw [orderBasis_apply, map_pow, orderEmbedding_orderAlpha]

lemma orderEmbedding_zero_injective (P : Parameters) :
    Function.Injective (orderEmbedding P 0) :=
  (rootEmbedding P 0).injective.comp
    (FaithfulSMul.algebraMap_injective (orderCarrier P) (ABCField P))

/-- The Minkowski embedding matrix of the power basis. This definition is
kept independent of the dynamical period bridge. -/
noncomputable def orderEmbeddingMatrix (P : Parameters) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j ↦ orderEmbedding P i (orderBasis P j)

@[simp] lemma orderEmbeddingMatrix_apply (P : Parameters) (i j : Fin 3) :
    orderEmbeddingMatrix P i j = realRoot P i ^ (j : ℕ) := by
  simp [orderEmbeddingMatrix]

lemma orderEmbeddingMatrix_det (P : Parameters) :
    (orderEmbeddingMatrix P).det =
      (root1 P - root0 P) * (root2 P - root0 P) * (root2 P - root1 P) := by
  rw [Matrix.det_fin_three]
  simp [orderEmbeddingMatrix, root0, root1, root2]
  ring

lemma orderEmbeddingMatrix_det_pos (P : Parameters) :
    0 < (orderEmbeddingMatrix P).det := by
  rw [orderEmbeddingMatrix_det]
  exact mul_pos (mul_pos (sub_pos.mpr (roots_strict_order P).1)
    (sub_pos.mpr (lt_trans (roots_strict_order P).1 (roots_strict_order P).2)))
    (sub_pos.mpr (roots_strict_order P).2)

lemma orderEmbeddingMatrix_det_ne_zero (P : Parameters) :
    (orderEmbeddingMatrix P).det ≠ 0 := ne_of_gt (orderEmbeddingMatrix_det_pos P)

/-- The ABC monogenic order as an actual cubic order in the sense used by
the regulator formalization. -/
noncomputable def cubicOrder (P : Parameters) : Cusick.CubicOrder (ABCField P) where
  carrier := orderCarrier P
  basis := orderBasis P

noncomputable def basicUnitFamily (P : Parameters) :
    Fin 2 → (orderCarrier P)ˣ :=
  ![alphaUnit P, alphaSubOneUnit P]

noncomputable def candidateUnitFamily (P : Parameters) :
    Fin (NumberField.Units.rank (ABCField P)) → (cubicOrder P).carrierˣ :=
  fun i ↦ basicUnitFamily P
    ((finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))) i)

lemma candidateUnitFamily_zero (P : Parameters) :
    candidateUnitFamily P
      ((finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 0) =
        alphaUnit P := by
  simp [candidateUnitFamily, basicUnitFamily]
  rfl

lemma candidateUnitFamily_one (P : Parameters) :
    candidateUnitFamily P
      ((finCongr (Cusick.CubicOrder.unitRank_eq_two (cubicOrder P))).symm 1) =
        alphaSubOneUnit P := by
  simp [candidateUnitFamily, basicUnitFamily]
  rfl

/-! ### The order as a localization lattice -/

private lemma orderCarrier_map_eq_adjoin (P : Parameters) :
    (orderCarrier P).map
        (IsScalarTower.toAlgHom ℤ
          (NumberField.RingOfIntegers (ABCField P)) (ABCField P)) =
      Algebra.adjoin ℤ ({alpha P} : Set (ABCField P)) := by
  rw [orderCarrier, AlgHom.map_adjoin_singleton]
  congr 2

private lemma exists_orderCarrier_mul_int_eq (P : Parameters) (z : ABCField P) :
    ∃ (x : orderCarrier P) (d : ℤ), d ≠ 0 ∧
      z * algebraMap ℤ (ABCField P) d =
        algebraMap (orderCarrier P) (ABCField P) x := by
  have hzQ : z ∈ Algebra.adjoin ℚ ({alpha P} : Set (ABCField P)) := by
    rw [show Algebra.adjoin ℚ ({alpha P} : Set (ABCField P)) = ⊤ by
      exact AdjoinRoot.adjoinRoot_eq_top]
    trivial
  obtain ⟨d, hd⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin
      (nonZeroDivisors ℤ) ℚ ({alpha P} : Set (ABCField P)) z hzQ
  have hd0 : (d : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hd' : algebraMap ℤ (ABCField P) (d : ℤ) * z ∈
      Algebra.adjoin ℤ ({alpha P} : Set (ABCField P)) := by
    simpa only [Submonoid.smul_def, Algebra.smul_def] using hd
  rw [← orderCarrier_map_eq_adjoin P] at hd'
  obtain ⟨x, hx, hxeq⟩ := Subalgebra.mem_map.mp hd'
  refine ⟨⟨x, hx⟩, d, hd0, ?_⟩
  rw [mul_comm]
  exact hxeq.symm

noncomputable local instance orderCarrier_isLocalization (P : Parameters) :
    IsLocalization
      (Algebra.algebraMapSubmonoid (orderCarrier P) (nonZeroDivisors ℤ))
      (ABCField P) := by
  apply (isLocalization_iff _ _).mpr
  refine ⟨fun y ↦ ?_, fun z ↦ ?_, ?_⟩
  ·
    obtain ⟨d, hd, hdy⟩ := y.property
    change IsUnit (algebraMap (orderCarrier P) (ABCField P) (y : orderCarrier P))
    rw [← hdy]
    change IsUnit (algebraMap ℤ (ABCField P) d)
    exact (map_ne_zero_of_mem_nonZeroDivisors _
      (FaithfulSMul.algebraMap_injective ℤ (ABCField P)) hd).isUnit
  ·
    obtain ⟨x, d, hd, hzx⟩ := exists_orderCarrier_mul_int_eq P z
    let d' : nonZeroDivisors ℤ := ⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩
    let e : Algebra.algebraMapSubmonoid (orderCarrier P) (nonZeroDivisors ℤ) :=
      ⟨algebraMap ℤ (orderCarrier P) d,
        Algebra.mem_algebraMapSubmonoid_of_mem d'⟩
    refine ⟨(x, e), ?_⟩
    simpa [e, IsScalarTower.algebraMap_apply ℤ (orderCarrier P) (ABCField P)] using hzx
  · intro x y hxy
    have hxy' : x = y := by
      exact FaithfulSMul.algebraMap_injective (orderCarrier P) (ABCField P) hxy
    subst y
    exact ⟨1, by simp⟩

end ABCOrders
