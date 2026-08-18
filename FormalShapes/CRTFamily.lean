import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic.Order

/-!
# The explicit CRT family in the final arithmetic construction

This module contains the six local congruences and the separated family of
ABC parameters used in Section 5.3.
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

private lemma two_three_coprime (N : ℕ) :
    (twoPart N).Coprime (threePart N) := by
  exact (by decide : Nat.Coprime 2 3).pow N N

private lemma two_three_five_coprime (N : ℕ) :
    (twoPart N * threePart N).Coprime (fivePart N) := by
  exact Nat.Coprime.mul_left
    ((by decide : Nat.Coprime 2 5).pow N N)
    ((by decide : Nat.Coprime 3 5).pow N N)

private def crt23 (N x2 x3 : ℕ) : ℕ :=
  Nat.chineseRemainder (two_three_coprime N) x2 x3

private def crt235 (N x2 x3 x5 : ℕ) : ℕ :=
  Nat.chineseRemainder (two_three_five_coprime N) (crt23 N x2 x3) x5

private lemma crt235_mod_two (N x2 x3 x5 : ℕ) :
    Nat.ModEq (twoPart N) (crt235 N x2 x3 x5) x2 := by
  have hprod := (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.1
  have h23 := (Nat.chineseRemainder
    (two_three_coprime N) x2 x3).property.1
  exact (hprod.of_dvd (dvd_mul_right (twoPart N) (threePart N))).trans h23

private lemma crt235_mod_three (N x2 x3 x5 : ℕ) :
    Nat.ModEq (threePart N) (crt235 N x2 x3 x5) x3 := by
  have hprod := (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.1
  have h23 := (Nat.chineseRemainder
    (two_three_coprime N) x2 x3).property.2
  exact (hprod.of_dvd (dvd_mul_left (threePart N) (twoPart N))).trans h23

private lemma crt235_mod_five (N x2 x3 x5 : ℕ) :
    Nat.ModEq (fivePart N) (crt235 N x2 x3 x5) x5 :=
  (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.2

/-- The common CRT modulus `2^N 3^N 5^N = 30^N`. -/
def crtModulus (N : ℕ) : ℕ := twoPart N * threePart N * fivePart N

lemma crtModulus_eq (N : ℕ) : crtModulus N = 30 ^ N := by
  simp [crtModulus, twoPart, threePart, fivePart, ← mul_pow]

lemma crtModulus_pos (N : ℕ) : 0 < crtModulus N := by
  rw [crtModulus_eq]
  positivity

lemma crtModulus_tendsto : Tendsto crtModulus atTop atTop := by
  convert tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : 1 < (30 : ℕ)) using 1
  funext N
  exact crtModulus_eq N

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

lemma localAOne_bounds (N : ℕ) :
    crtModulus N ^ 2 ≤ localAOne N ∧
      localAOne N < crtModulus N ^ 2 + crtModulus N := by
  constructor
  · simp [localAOne]
  · have hr := crt235_lt N 0 1 1
    dsimp [localAOne]
    omega

lemma localATwo_bounds (N : ℕ) :
    3 * crtModulus N ^ 2 ≤ localATwo N ∧
      localATwo N < 3 * crtModulus N ^ 2 + crtModulus N := by
  constructor
  · simp [localATwo]
  · have hr := crt235_lt N 1 0 1
    dsimp [localATwo]
    omega

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
