import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The banana reduction on the modular space

This file proves the rank-two ``banana trick'' directly.  It defines the
diagonal and upper-unipotent one-parameter subgroups of `SL(2, ℝ)`, constructs
primitive integral directions by approximation with growing prime
denominators, and proves that the resulting expanding strip is dense in
`SL(2, ℝ) / SL(2, ℤ)`.  The usual closed-set formulation follows.
-/

noncomputable section

open Set

namespace SL2Banana

/-- The real special linear group in dimension two. -/
abbrev BananaSL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The image of `SL(2, ℤ)` in `SL(2, ℝ)`. -/
def bananaIntegralSL2 : Subgroup BananaSL2R :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin 2)).range

/-- The space of oriented covolume-one two-dimensional lattices. -/
abbrev BananaModularSpace := BananaSL2R ⧸ bananaIntegralSL2

/-- The determinant-one diagonal matrix
`diag(exp(t / 2), exp(-t / 2))`. -/
def bananaDiagonal (t : ℝ) : BananaSL2R :=
  ⟨!![Real.exp (t / 2), 0; 0, Real.exp (-t / 2)], by
    rw [Matrix.det_fin_two_of]
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero⟩

/-- The upper-unipotent matrix `[[1, s], [0, 1]]`. -/
def bananaUnipotent (s : ℝ) : BananaSL2R :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The integral upper-unipotent matrix with parameter `n`. -/
def bananaIntegralUnipotent (n : ℤ) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, n; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- Auxiliary step `bananaUnipotent_int_mem` in the banana-density argument used in Proposition 5.2. -/
theorem bananaUnipotent_int_mem (n : ℤ) :
    bananaUnipotent (n : ℝ) ∈ bananaIntegralSL2 := by
  refine ⟨bananaIntegralUnipotent n, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bananaUnipotent, bananaIntegralUnipotent,
      RingHom.mapMatrix_apply]

/-- Auxiliary step `bananaDiagonal_zero` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaDiagonal_zero : bananaDiagonal 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bananaDiagonal]

/-- Auxiliary step `bananaDiagonal_add` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaDiagonal_add (t r : ℝ) :
    bananaDiagonal (t + r) = bananaDiagonal t * bananaDiagonal r := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bananaDiagonal, Matrix.mul_apply]
  all_goals rw [← Real.exp_add]
  all_goals
    congr 1
    ring

/-- Auxiliary step `bananaDiagonal_neg` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaDiagonal_neg (t : ℝ) :
    bananaDiagonal (-t) = (bananaDiagonal t)⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  rw [← bananaDiagonal_add]
  simp

/-- Auxiliary step `bananaUnipotent_zero` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaUnipotent_zero : bananaUnipotent 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bananaUnipotent]

/-- Auxiliary step `bananaUnipotent_add` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaUnipotent_add (s r : ℝ) :
    bananaUnipotent (s + r) = bananaUnipotent s * bananaUnipotent r := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bananaUnipotent, Matrix.mul_apply]
  ring

/-- Auxiliary step `bananaUnipotent_neg` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaUnipotent_neg (s : ℝ) :
    bananaUnipotent (-s) = (bananaUnipotent s)⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  rw [← bananaUnipotent_add]
  simp

/-- Conjugation by the diagonal flow expands the upper horocycle. -/
theorem bananaDiagonal_conj_unipotent (t s : ℝ) :
    bananaDiagonal t * bananaUnipotent s * (bananaDiagonal t)⁻¹ =
      bananaUnipotent (Real.exp t * s) := by
  have hposneg : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  have hnegpos : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
    rw [mul_comm]
    exact hposneg
  have hsquare : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← bananaDiagonal_neg]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bananaDiagonal, bananaUnipotent, Matrix.mul_apply]
  · exact hposneg
  · calc
      Real.exp (t / 2) * s * Real.exp (t / 2) =
          (Real.exp (t / 2) * Real.exp (t / 2)) * s := by ring
      _ = Real.exp t * s := by rw [hsquare]
  · exact hnegpos

/-- The standard lattice, viewed as the identity coset. -/
def bananaBasePoint : BananaModularSpace :=
  ((1 : BananaSL2R) : BananaModularSpace)

/-- The point on the closed standard horocycle with parameter `s`. -/
def bananaHorocyclePoint (s : ℝ) : BananaModularSpace :=
  ((bananaUnipotent s : BananaSL2R) : BananaModularSpace)

/-- Auxiliary step `bananaHorocyclePoint_zero` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaHorocyclePoint_zero : bananaHorocyclePoint 0 = bananaBasePoint := by
  simp [bananaHorocyclePoint, bananaBasePoint]

/-- Integer translation does not change a point on the standard closed
horocycle. -/
theorem bananaHorocyclePoint_add_int (s : ℝ) (n : ℤ) :
    bananaHorocyclePoint (s + n) = bananaHorocyclePoint s := by
  change ((bananaUnipotent (s + (n : ℝ)) : BananaSL2R) : BananaModularSpace) =
    ((bananaUnipotent s : BananaSL2R) : BananaModularSpace)
  rw [bananaUnipotent_add]
  exact QuotientGroup.mk_mul_of_mem _ (bananaUnipotent_int_mem n)

/-- Auxiliary step `bananaHorocyclePoint_add_one` in the banana-density argument used in Proposition 5.2. -/
@[simp]
theorem bananaHorocyclePoint_add_one (s : ℝ) :
    bananaHorocyclePoint (s + 1) = bananaHorocyclePoint s := by
  simpa using bananaHorocyclePoint_add_int s 1

/-- First move along the standard horocycle, then apply diagonal time `t`. -/
def bananaStripPoint (t s : ℝ) : BananaModularSpace :=
  bananaDiagonal t • bananaHorocyclePoint s

/-- Auxiliary step `bananaStripPoint_eq_coset` in the banana-density argument used in Proposition 5.2. -/
theorem bananaStripPoint_eq_coset (t s : ℝ) :
    bananaStripPoint t s =
      ((bananaDiagonal t * bananaUnipotent s : BananaSL2R) : BananaModularSpace) := by
  rfl

/-- The forward diagonal saturation of one full period of the standard
horocycle. -/
def bananaExpandingStrip : Set BananaModularSpace :=
  {x | ∃ t ∈ Ici (0 : ℝ), ∃ s ∈ Icc (0 : ℝ) 1,
    x = bananaStripPoint t s}

/-- Auxiliary step `mem_bananaExpandingStrip_iff` in the banana-density argument used in Proposition 5.2. -/
theorem mem_bananaExpandingStrip_iff (x : BananaModularSpace) :
    x ∈ bananaExpandingStrip ↔
      ∃ t ∈ Ici (0 : ℝ), ∃ s ∈ Icc (0 : ℝ) 1,
        x = bananaDiagonal t • bananaHorocyclePoint s := by
  rfl

/-- A set is invariant under every real diagonal time. -/
def IsBananaDiagonalInvariant (C : Set BananaModularSpace) : Prop :=
  ∀ (t : ℝ), MapsTo (bananaDiagonal t • ·) C C

/-- Auxiliary step `isBananaDiagonalInvariant_iff` in the banana-density argument used in Proposition 5.2. -/
theorem isBananaDiagonalInvariant_iff (C : Set BananaModularSpace) :
    IsBananaDiagonalInvariant C ↔
      ∀ (t : ℝ) (x : BananaModularSpace), x ∈ C → bananaDiagonal t • x ∈ C := by
  rfl

/-- Forward invariance under the diagonal flow.  This is the hypothesis used
by the expanding-horocycle formulation of the banana lemma. -/
def IsBananaForwardDiagonalInvariant (C : Set BananaModularSpace) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → MapsTo (bananaDiagonal t • ·) C C

/-- Auxiliary step `IsBananaDiagonalInvariant.forward` in the banana-density argument used in Proposition 5.2. -/
theorem IsBananaDiagonalInvariant.forward
    {C : Set BananaModularSpace} (hC : IsBananaDiagonalInvariant C) :
    IsBananaForwardDiagonalInvariant C := by
  intro t _
  exact hC t

/-- Auxiliary step `IsBananaDiagonalInvariant.image_eq` in the banana-density argument used in Proposition 5.2. -/
theorem IsBananaDiagonalInvariant.image_eq
    {C : Set BananaModularSpace} (hC : IsBananaDiagonalInvariant C) (t : ℝ) :
    (bananaDiagonal t • ·) '' C = C := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hC t hx
  · intro x hx
    refine ⟨bananaDiagonal (-t) • x, hC (-t) hx, ?_⟩
    change bananaDiagonal t • (bananaDiagonal (-t) • x) = x
    rw [← mul_smul, ← bananaDiagonal_add]
    simp

/-- Auxiliary step `bananaExpandingStrip_subset` in the banana-density argument used in Proposition 5.2. -/
theorem bananaExpandingStrip_subset
    {C : Set BananaModularSpace}
    (hdiag : IsBananaForwardDiagonalInvariant C)
    (hsegment : ∀ s ∈ Icc (0 : ℝ) 1, bananaHorocyclePoint s ∈ C) :
    bananaExpandingStrip ⊆ C := by
  rintro x ⟨t, ht, s, hs, rfl⟩
  exact hdiag t ht (hsegment s hs)

/-! ## A constructive proof of expanding-strip density

For a target matrix with bottom-right entry nonzero, growing prime
denominators give primitive integral bottom rows converging in direction to
the target bottom row.  Bezout completes each row to an element of
`SL(2, ℤ)`.  An explicit diagonal time and horocycle parameter then produce a
representative with the target top row and a convergent bottom row.  Targets
with zero bottom-right entry follow by a vanishing unipotent perturbation.
-/

open Filter

namespace BananaApprox

def pp (n : ℕ) : ℕ := Nat.nth Nat.Prime n
def raw (r : ℝ) (n : ℕ) : ℤ := ⌊(pp n : ℝ) * r⌋
def adj (r : ℝ) (n : ℕ) : ℤ :=
  if (pp n : ℤ) ∣ raw r n then raw r n + 1 else raw r n

/-- Auxiliary step `prime_pp` in the banana-density argument used in Proposition 5.2. -/
lemma prime_pp (n : ℕ) : Nat.Prime (pp n) := Nat.prime_nth_prime n
/-- Auxiliary step `pp_pos` in the banana-density argument used in Proposition 5.2. -/
lemma pp_pos (n : ℕ) : 0 < pp n := (prime_pp n).pos

/-- Auxiliary step `tendsto_pp` in the banana-density argument used in Proposition 5.2. -/
lemma tendsto_pp : Tendsto pp atTop atTop := by
  exact tendsto_atTop_mono
    (fun n => (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)) tendsto_id

/-- Auxiliary step `adj_not_dvd` in the banana-density argument used in Proposition 5.2. -/
lemma adj_not_dvd (r : ℝ) (n : ℕ) : ¬ (pp n : ℤ) ∣ adj r n := by
  rw [adj]
  split_ifs with h
  · intro h'
    have hone : (pp n : ℤ) ∣ 1 := by
      simpa using dvd_sub h' h
    have hone' : pp n ∣ 1 := Int.natCast_dvd.mp hone
    exact (prime_pp n).not_dvd_one hone'
  · exact h

/-- Auxiliary step `adj_coprime` in the banana-density argument used in Proposition 5.2. -/
lemma adj_coprime (r : ℝ) (n : ℕ) : IsCoprime (adj r n) (pp n : ℤ) := by
  rw [Int.isCoprime_iff_nat_coprime]
  apply Nat.Coprime.symm
  simp only [Int.natAbs_natCast]
  rw [(prime_pp n).coprime_iff_not_dvd]
  simpa only [Int.natCast_dvd] using adj_not_dvd r n

/-- Auxiliary step `adj_error_lower` in the banana-density argument used in Proposition 5.2. -/
lemma adj_error_lower (r : ℝ) (n : ℕ) :
    (-1 : ℝ) ≤ (adj r n : ℝ) - (pp n : ℝ) * r := by
  rw [adj]
  split_ifs <;> push_cast
  · simp only [raw]
    have hf : (pp n : ℝ) * r < ((⌊(pp n : ℝ) * r⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    linarith
  · simp only [raw]
    have hf : (pp n : ℝ) * r < ((⌊(pp n : ℝ) * r⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    linarith

/-- Auxiliary step `adj_error_upper` in the banana-density argument used in Proposition 5.2. -/
lemma adj_error_upper (r : ℝ) (n : ℕ) :
    (adj r n : ℝ) - (pp n : ℝ) * r ≤ 2 := by
  rw [adj]
  split_ifs <;> push_cast
  · simp only [raw]
    have hf : ((⌊(pp n : ℝ) * r⌋ : ℤ) : ℝ) ≤ (pp n : ℝ) * r := Int.floor_le _
    linarith
  · simp only [raw]
    have hf : ((⌊(pp n : ℝ) * r⌋ : ℤ) : ℝ) ≤ (pp n : ℝ) * r := Int.floor_le _
    linarith

/-- Auxiliary step `tendsto_adj_div` in the banana-density argument used in Proposition 5.2. -/
lemma tendsto_adj_div (r : ℝ) :
    Tendsto (fun n => (adj r n : ℝ) / (pp n : ℝ)) atTop (nhds r) := by
  have hpR : Tendsto (fun n => (pp n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_pp
  have herr : Tendsto
      (fun n => ((adj r n : ℝ) - (pp n : ℝ) * r) / (pp n : ℝ))
      atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Filter.Eventually.of_forall (adj_error_lower r))
      (Filter.Eventually.of_forall (adj_error_upper r)) hpR
  convert herr.add_const r using 1
  · funext n
    have hn : (pp n : ℝ) ≠ 0 := by exact_mod_cast (pp_pos n).ne'
    field_simp [hn]
    linarith
  · ring

end BananaApprox

open BananaApprox

private def eps (D : ℝ) : ℤ := if 0 < D then 1 else -1
private def botC (C D : ℝ) (n : ℕ) : ℤ := eps D * adj (C / D) n
private def botD (D : ℝ) (n : ℕ) : ℤ := eps D * (pp n : ℤ)
private def area (A B C D : ℝ) (n : ℕ) : ℝ :=
  A * botD D n - B * botC C D n

/-- Auxiliary step `eps_sq` in the banana-density argument used in Proposition 5.2. -/
private lemma eps_sq (D : ℝ) : eps D * eps D = 1 := by
  simp only [eps]
  split_ifs <;> norm_num

/-- Auxiliary step `eps_ne_zero` in the banana-density argument used in Proposition 5.2. -/
private lemma eps_ne_zero (D : ℝ) : eps D ≠ 0 := by
  intro h
  have := eps_sq D
  rw [h] at this
  norm_num at this

/-- Auxiliary step `eps_cast_mul_abs` in the banana-density argument used in Proposition 5.2. -/
private lemma eps_cast_mul_abs {D : ℝ} (hD : D ≠ 0) :
    (eps D : ℝ) * |D| = D := by
  simp only [eps]
  split_ifs with h
  · rw [abs_of_pos h]
    norm_num
  · have hn : D < 0 := lt_of_le_of_ne (le_of_not_gt h) hD
    rw [abs_of_neg hn]
    norm_num

/-- Auxiliary step `bot_coprime` in the banana-density argument used in Proposition 5.2. -/
private lemma bot_coprime (C D : ℝ) (n : ℕ) :
    IsCoprime (botC C D n) (botD D n) := by
  simp only [botC, botD, eps]
  split_ifs
  · simpa using adj_coprime (C / D) n
  · simpa using (adj_coprime (C / D) n).neg_left.neg_right

/-- Auxiliary step `tendsto_area_div` in the banana-density argument used in Proposition 5.2. -/
private lemma tendsto_area_div
    {A B C D : ℝ} (hD : D ≠ 0) (hdet : A * D - B * C = 1) :
    Tendsto (fun n => area A B C D n / (pp n : ℝ)) atTop (nhds (1 / |D|)) := by
  have hm := tendsto_adj_div (C / D)
  have he : ((eps D : ℤ) : ℝ) ≠ 0 := by exact_mod_cast eps_ne_zero D
  have hformula (n : ℕ) :
      area A B C D n / (pp n : ℝ) =
        (eps D : ℝ) * (A - B * ((adj (C / D) n : ℝ) / (pp n : ℝ))) := by
    have hp : (pp n : ℝ) ≠ 0 := by exact_mod_cast (pp_pos n).ne'
    simp only [area, botC, botD]
    push_cast
    field_simp [hp]
  have hbase : Tendsto
      (fun n => (eps D : ℝ) * (A - B * ((adj (C / D) n : ℝ) / (pp n : ℝ))))
      atTop (nhds ((eps D : ℝ) * (A - B * (C / D)))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hm)).const_mul _
  have hab : A - B * (C / D) = 1 / D := by
    field_simp [hD]
    linarith
  have hval : (eps D : ℝ) * (A - B * (C / D)) = 1 / |D| := by
    rw [hab]
    have ha : 0 < |D| := abs_pos.mpr hD
    field_simp [hD, ne_of_gt ha]
    exact eps_cast_mul_abs hD
  rw [← hval]
  exact hbase.congr' (Filter.Eventually.of_forall fun n => (hformula n).symm)

/-- Auxiliary step `tendsto_area_atTop` in the banana-density argument used in Proposition 5.2. -/
private lemma tendsto_area_atTop
    {A B C D : ℝ} (hD : D ≠ 0) (hdet : A * D - B * C = 1) :
    Tendsto (area A B C D) atTop atTop := by
  have hpR : Tendsto (fun n => (pp n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_pp
  have hr := tendsto_area_div hD hdet
  have hpos : 0 < 1 / |D| := one_div_pos.mpr (abs_pos.mpr hD)
  have hprod := hpR.atTop_mul_pos hpos hr
  apply hprod.congr'
  filter_upwards with n
  have hp : (pp n : ℝ) ≠ 0 := by exact_mod_cast (pp_pos n).ne'
  field_simp [hp]

/-- Auxiliary step `tendsto_botC_div_area` in the banana-density argument used in Proposition 5.2. -/
private lemma tendsto_botC_div_area
    {A B C D : ℝ} (hD : D ≠ 0) (hdet : A * D - B * C = 1) :
    Tendsto (fun n => (botC C D n : ℝ) / area A B C D n) atTop (nhds C) := by
  have hm := tendsto_adj_div (C / D)
  have hnum : Tendsto (fun n => (botC C D n : ℝ) / (pp n : ℝ)) atTop
      (nhds ((eps D : ℝ) * (C / D))) := by
    convert hm.const_mul (eps D : ℝ) using 1
    funext n
    simp only [botC]
    push_cast
    ring
  have hden := tendsto_area_div hD hdet
  have hden0 : (1 / |D| : ℝ) ≠ 0 := one_div_ne_zero (abs_ne_zero.mpr hD)
  have hquot := hnum.div hden hden0
  have heq :
      ((fun n => (botC C D n : ℝ) / (pp n : ℝ)) /
        (fun n => area A B C D n / (pp n : ℝ))) =ᶠ[atTop]
      (fun n => (botC C D n : ℝ) / area A B C D n) := by
    filter_upwards [(tendsto_area_atTop hD hdet).eventually_gt_atTop 0] with n hn
    have hp : (pp n : ℝ) ≠ 0 := by exact_mod_cast (pp_pos n).ne'
    change
      ((botC C D n : ℝ) / (pp n : ℝ)) /
        (area A B C D n / (pp n : ℝ)) =
      (botC C D n : ℝ) / area A B C D n
    field_simp [hp, hn.ne']
  have hval : (eps D : ℝ) * (C / D) / (1 / |D|) = C := by
    have ha : 0 < |D| := abs_pos.mpr hD
    field_simp [hD, ne_of_gt ha]
    linear_combination C * eps_cast_mul_abs hD
  simpa only [hval] using hquot.congr' heq

/-- Auxiliary step `tendsto_botD_div_area` in the banana-density argument used in Proposition 5.2. -/
private lemma tendsto_botD_div_area
    {A B C D : ℝ} (hD : D ≠ 0) (hdet : A * D - B * C = 1) :
    Tendsto (fun n => (botD D n : ℝ) / area A B C D n) atTop (nhds D) := by
  have hnum : Tendsto (fun _n : ℕ => (eps D : ℝ)) atTop (nhds (eps D : ℝ)) :=
    tendsto_const_nhds
  have hden := tendsto_area_div hD hdet
  have hden0 : (1 / |D| : ℝ) ≠ 0 := one_div_ne_zero (abs_ne_zero.mpr hD)
  have hquot := hnum.div hden hden0
  have heq :
      ((fun _n : ℕ => (eps D : ℝ)) /
        (fun n => area A B C D n / (pp n : ℝ))) =ᶠ[atTop]
      (fun n => (botD D n : ℝ) / area A B C D n) := by
    filter_upwards [(tendsto_area_atTop hD hdet).eventually_gt_atTop 0] with n hn
    have hp : (pp n : ℝ) ≠ 0 := by exact_mod_cast (pp_pos n).ne'
    simp only [botD]
    push_cast
    change
      ((eps D : ℝ) / (area A B C D n / (pp n : ℝ))) =
        (eps D : ℝ) * (pp n : ℝ) / area A B C D n
    field_simp [hp, hn.ne']
  have hval : (eps D : ℝ) / (1 / |D|) = D := by
    have ha : 0 < |D| := abs_pos.mpr hD
    field_simp [hD, ne_of_gt ha]
    exact eps_cast_mul_abs hD
  simpa only [hval] using hquot.congr' heq

/-- Auxiliary step `coset_mem_closure_of_d_ne_zero` in the banana-density argument used in Proposition 5.2. -/
private theorem coset_mem_closure_of_d_ne_zero
    (g : BananaSL2R) (hD : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0) :
    (g : BananaModularSpace) ∈ closure bananaExpandingStrip := by
  let A : ℝ := g 0 0
  let B : ℝ := g 0 1
  let C : ℝ := g 1 0
  let D : ℝ := g 1 1
  have hD' : D ≠ 0 := hD
  have hdet : A * D - B * C = 1 := by
    simpa only [A, B, C, D, Matrix.det_fin_two] using g.property
  let w : ℕ → Fin 2 → ℤ := fun n => ![botC C D n, botD D n]
  have hw (n : ℕ) : IsCoprime (w n 0) (w n 1) := by
    change IsCoprime (botC C D n) (botD D n)
    exact bot_coprime C D n
  have hex (n : ℕ) :
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 = w n := by
    rcases ModularGroup.bottom_row_surj (hw n) with ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩
  choose γ hγ using hex
  let γR : ℕ → BananaSL2R := fun n =>
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (γ n)
  have hγR_row (n : ℕ) :
      (γR n : Matrix (Fin 2) (Fin 2) ℝ) 1 =
        (fun i => (w n i : ℝ)) := by
    funext i
    rw [show (γR n : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.map (γ n : Matrix (Fin 2) (Fin 2) ℤ) (Int.castRingHom ℝ) by
        rfl]
    simp only [Matrix.map_apply, Int.coe_castRingHom]
    rw [congrFun (hγ n) i]
  have hγR_mem (n : ℕ) : γR n ∈ bananaIntegralSL2 := ⟨γ n, rfl⟩
  let L : ℕ → ℝ := area A B C D
  let θ : ℕ → ℝ := fun n =>
    ((1 / L n) * B - (γR n : Matrix (Fin 2) (Fin 2) ℝ) 0 1) /
      (botD D n : ℝ)
  let T : ℕ → ℝ := fun n => 2 * Real.log (L n)
  let q : ℕ → BananaSL2R := fun n =>
    bananaDiagonal (T n) * bananaUnipotent (θ n) * γR n
  let M : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun n =>
    !![A, B; (botC C D n : ℝ) / L n, (botD D n : ℝ) / L n]
  have hLtop : Tendsto L atTop atTop := tendsto_area_atTop hD' hdet
  have hlarge : ∀ᶠ n in atTop, 1 ≤ L n := hLtop.eventually_ge_atTop 1
  have hqM : (fun n => (q n : Matrix (Fin 2) (Fin 2) ℝ)) =ᶠ[atTop] M := by
    filter_upwards [hlarge] with n hn
    have hLpos : 0 < L n := zero_lt_one.trans_le hn
    have hL0 : L n ≠ 0 := hLpos.ne'
    have hbotD0 : (botD D n : ℝ) ≠ 0 := by
      simp only [botD]
      push_cast
      exact mul_ne_zero (by exact_mod_cast eps_ne_zero D)
        (by exact_mod_cast (pp_pos n).ne')
    have hexp : Real.exp (T n / 2) = L n := by
      simp only [T]
      convert Real.exp_log hLpos using 1
      ring
    have hexpneg : Real.exp (-T n / 2) = 1 / L n := by
      rw [show -T n / 2 = -(T n / 2) by ring, Real.exp_neg, hexp]
      simp only [one_div]
    have hγdet :
        ((γR n : Matrix (Fin 2) (Fin 2) ℝ) 0 0) * (botD D n : ℝ) -
          ((γR n : Matrix (Fin 2) (Fin 2) ℝ) 0 1) * (botC C D n : ℝ) = 1 := by
      have hd := (γR n).property
      rw [Matrix.det_fin_two] at hd
      have hc := congrFun (hγR_row n) 0
      have hd' := congrFun (hγR_row n) 1
      simp only [w] at hc hd'
      rw [hc, hd'] at hd
      exact hd
    have harea :
        L n = A * (botD D n : ℝ) - B * (botC C D n : ℝ) := rfl
    have hγdetL := congrArg (fun x : ℝ => L n * x) hγdet
    have hdu :
        (bananaDiagonal (T n) : Matrix (Fin 2) (Fin 2) ℝ) *
          (bananaUnipotent (θ n) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![L n, L n * θ n; 0, 1 / L n] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [bananaDiagonal, bananaUnipotent, Matrix.mul_apply, hexp, hexpneg]
    change
      ((bananaDiagonal (T n) : Matrix (Fin 2) (Fin 2) ℝ) *
        (bananaUnipotent (θ n) : Matrix (Fin 2) (Fin 2) ℝ)) *
          (γR n : Matrix (Fin 2) (Fin 2) ℝ) = M n
    rw [hdu]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simp [M, Matrix.mul_apply, θ]
      rw [congrFun (hγR_row n) 0]
      simp [w]
      field_simp [hL0, hbotD0]
      nlinarith [hγdetL, harea]
    · simp [M, Matrix.mul_apply, θ]
      rw [congrFun (hγR_row n) 1]
      simp [w]
      field_simp [hL0, hbotD0]
      ring
    · simp [M, Matrix.mul_apply]
      rw [congrFun (hγR_row n) 0]
      simp [w]
      ring
    · simp [M, Matrix.mul_apply]
      rw [congrFun (hγR_row n) 1]
      simp [w]
      ring
  have hM : Tendsto M atTop (nhds (g : Matrix (Fin 2) (Fin 2) ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact tendsto_botC_div_area hD' hdet
    · exact tendsto_botD_div_area hD' hdet
  have hqMatrix : Tendsto (fun n => (q n : Matrix (Fin 2) (Fin 2) ℝ)) atTop
      (nhds (g : Matrix (Fin 2) (Fin 2) ℝ)) := hM.congr' hqM.symm
  have hqGroup : Tendsto q atTop (nhds g) := tendsto_subtype_rng.mpr hqMatrix
  have hqQuot : Tendsto (fun n => (q n : BananaModularSpace)) atTop (nhds (g : BananaModularSpace)) :=
    QuotientGroup.continuous_mk.continuousAt.tendsto.comp hqGroup
  apply mem_closure_of_tendsto hqQuot
  filter_upwards [hlarge] with n hn
  refine ⟨T n, ?_, Int.fract (θ n), ?_, ?_⟩
  · simp only [T]
    exact mul_nonneg (by norm_num) (Real.log_nonneg hn)
  · exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · have hθ : θ n = Int.fract (θ n) + (⌊θ n⌋ : ℤ) := by
      simpa [add_comm] using (Int.floor_add_fract (θ n)).symm
    have hperiod : bananaStripPoint (T n) (θ n) =
        bananaStripPoint (T n) (Int.fract (θ n)) := by
      change bananaDiagonal (T n) • bananaHorocyclePoint (θ n) =
        bananaDiagonal (T n) • bananaHorocyclePoint (Int.fract (θ n))
      apply congrArg (bananaDiagonal (T n) • ·)
      calc
        bananaHorocyclePoint (θ n) =
            bananaHorocyclePoint (Int.fract (θ n) + (⌊θ n⌋ : ℤ)) :=
          congrArg bananaHorocyclePoint hθ
        _ = bananaHorocyclePoint (Int.fract (θ n)) :=
          bananaHorocyclePoint_add_int _ _
    rw [← hperiod]
    change ((q n : BananaSL2R) : BananaModularSpace) = bananaStripPoint (T n) (θ n)
    rw [bananaStripPoint_eq_coset]
    exact QuotientGroup.mk_mul_of_mem _ (hγR_mem n)

/-- Auxiliary step `coset_mem_closure` in the banana-density argument used in Proposition 5.2. -/
private theorem coset_mem_closure (g : BananaSL2R) :
    (g : BananaModularSpace) ∈ closure bananaExpandingStrip := by
  by_cases hD : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0
  · have hC : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0 := by
      intro hC
      have hd := g.property
      rw [Matrix.det_fin_two, hD, hC] at hd
      norm_num at hd
    let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    let u : ℕ → BananaSL2R := fun n => bananaUnipotent (δ n)
    have hδ : Tendsto δ atTop (nhds 0) := by
      simpa only [δ, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have huMatrix : Tendsto (fun n => (u n : Matrix (Fin 2) (Fin 2) ℝ)) atTop
        (nhds ((1 : BananaSL2R) : Matrix (Fin 2) (Fin 2) ℝ)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      fin_cases i <;> fin_cases j
      · change Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1)
        exact tendsto_const_nhds
      · change Tendsto δ atTop (nhds 0)
        exact hδ
      · change Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (nhds 0)
        exact tendsto_const_nhds
      · change Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1)
        exact tendsto_const_nhds
    have hu : Tendsto u atTop (nhds (1 : BananaSL2R)) := tendsto_subtype_rng.mpr huMatrix
    have hgu : Tendsto (fun n => g * u n) atTop (nhds g) := by
      simpa using tendsto_const_nhds.mul hu
    have hguQ : Tendsto (fun n => ((g * u n : BananaSL2R) : BananaModularSpace)) atTop
        (nhds (g : BananaModularSpace)) :=
      QuotientGroup.continuous_mk.continuousAt.tendsto.comp hgu
    apply IsClosed.mem_of_tendsto isClosed_closure hguQ
    apply Filter.Eventually.of_forall
    intro n
    apply coset_mem_closure_of_d_ne_zero
    change
      ((g : Matrix (Fin 2) (Fin 2) ℝ) *
        (bananaUnipotent (δ n) : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 ≠ 0
    simp [Matrix.mul_apply, bananaUnipotent, hD, δ, hC] <;> positivity
  · exact coset_mem_closure_of_d_ne_zero g hD


/-- The diagonal saturation of a full standard horocycle period is dense in
the modular lattice space.  This is the expanding-horocycle, or banana,
density statement. -/
theorem banana_expanding_horocycle_dense :
    Dense bananaExpandingStrip := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | _ g => exact coset_mem_closure g

/-- **Banana lemma.** A closed, diagonally invariant subset of the modular
lattice space that contains one full standard horocycle period is the whole
space. -/
theorem banana_closed_invariant_eq_univ
    {C : Set BananaModularSpace}
    (hclosed : IsClosed C)
    (hdiag : IsBananaForwardDiagonalInvariant C)
    (hsegment : ∀ s ∈ Icc (0 : ℝ) 1, bananaHorocyclePoint s ∈ C) :
    C = Set.univ := by
  have hstrip : bananaExpandingStrip ⊆ C :=
    bananaExpandingStrip_subset hdiag hsegment
  have hdense : Dense C := banana_expanding_horocycle_dense.mono hstrip
  calc
    C = closure C := hclosed.closure_eq.symm
    _ = Set.univ := hdense.closure_eq

/-- Membership-oriented form of the banana lemma. -/
theorem banana_mem_of_closed_invariant
    {C : Set BananaModularSpace}
    (hclosed : IsClosed C)
    (hdiag : IsBananaForwardDiagonalInvariant C)
    (hsegment : ∀ s ∈ Icc (0 : ℝ) 1, bananaHorocyclePoint s ∈ C)
    (x : BananaModularSpace) :
    x ∈ C := by
  rw [banana_closed_invariant_eq_univ hclosed hdiag hsegment]
  exact Set.mem_univ x

end SL2Banana
