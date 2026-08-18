import main
import Mathlib.Data.Nat.ChineseRemainder

noncomputable section

namespace CubicPeriodicTori

open Filter

def twoPart (N : ℕ) := 2 ^ N
def threePart (N : ℕ) := 3 ^ N
def fivePart (N : ℕ) := 5 ^ N

lemma two_three_coprime (N : ℕ) :
    (twoPart N).Coprime (threePart N) := by
  exact (by decide : Nat.Coprime 2 3).pow N N

lemma two_three_five_coprime (N : ℕ) :
    (twoPart N * threePart N).Coprime (fivePart N) := by
  exact Nat.Coprime.mul_left
    ((by decide : Nat.Coprime 2 5).pow N N)
    ((by decide : Nat.Coprime 3 5).pow N N)

def crt23 (N x2 x3 : ℕ) : ℕ :=
  Nat.chineseRemainder (two_three_coprime N) x2 x3

def crt235 (N x2 x3 x5 : ℕ) : ℕ :=
  Nat.chineseRemainder (two_three_five_coprime N) (crt23 N x2 x3) x5

lemma crt235_mod_two (N x2 x3 x5 : ℕ) :
    Nat.ModEq (twoPart N) (crt235 N x2 x3 x5) x2 := by
  have hprod := (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.1
  have h23 := (Nat.chineseRemainder
    (two_three_coprime N) x2 x3).property.1
  exact (hprod.of_dvd (dvd_mul_right (twoPart N) (threePart N))).trans h23

lemma crt235_mod_three (N x2 x3 x5 : ℕ) :
    Nat.ModEq (threePart N) (crt235 N x2 x3 x5) x3 := by
  have hprod := (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.1
  have h23 := (Nat.chineseRemainder
    (two_three_coprime N) x2 x3).property.2
  exact (hprod.of_dvd (dvd_mul_left (threePart N) (twoPart N))).trans h23

lemma crt235_mod_five (N x2 x3 x5 : ℕ) :
    Nat.ModEq (fivePart N) (crt235 N x2 x3 x5) x5 :=
  (Nat.chineseRemainder
    (two_three_five_coprime N) (crt23 N x2 x3) x5).property.2

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

lemma crt235_lt (N x2 x3 x5 : ℕ) :
    crt235 N x2 x3 x5 < crtModulus N := by
  exact Nat.chineseRemainder_lt_mul (two_three_five_coprime N)
    (crt23 N x2 x3) x5 (by simp [twoPart, threePart]) (by simp [fivePart])

def localAOne (N : ℕ) : ℕ := crt235 N 0 1 1 + crtModulus N
def localATwo (N : ℕ) : ℕ := crt235 N 1 0 1 + 4 * crtModulus N

lemma localAOne_bounds (N : ℕ) :
    crtModulus N ≤ localAOne N ∧ localAOne N < 2 * crtModulus N := by
  constructor
  · simp [localAOne]
  · dsimp [localAOne]
    have hr := crt235_lt N 0 1 1
    omega

lemma localATwo_bounds (N : ℕ) :
    4 * crtModulus N ≤ localATwo N ∧ localATwo N < 5 * crtModulus N := by
  constructor
  · simp [localATwo]
  · dsimp [localATwo]
    have hr := crt235_lt N 1 0 1
    omega

lemma local_parameters_ordered (N : ℕ) :
    3 ≤ localAOne (N + 1) ∧ localAOne (N + 1) < localATwo (N + 1) := by
  have hM : 3 ≤ crtModulus (N + 1) := by
    rw [crtModulus_eq, pow_succ]
    nlinarith [pow_pos (by norm_num : 0 < (30 : ℕ)) N]
  constructor
  · exact hM.trans (localAOne_bounds (N + 1)).1
  · have hpos := crtModulus_pos (N + 1)
    have h1 := (localAOne_bounds (N + 1)).2
    have h2 := (localATwo_bounds (N + 1)).1
    omega

lemma local_separation_lower (N : ℕ) :
    crtModulus N ≤
      min (localAOne N) (localATwo N - localAOne N) := by
  rw [le_min_iff]
  constructor
  · exact (localAOne_bounds N).1
  · have h1 := (localAOne_bounds N).2
    have h2 := (localATwo_bounds N).1
    omega

lemma local_separation_tendsto :
    Tendsto (fun N ↦ min (localAOne N) (localATwo N - localAOne N))
      atTop atTop := by
  exact Filter.tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall local_separation_lower) crtModulus_tendsto

lemma local_conditions (N : ℕ) :
    SatisfiesLocalConditions N (localAOne N) (localATwo N) := by
  have hm2 : twoPart N ∣ crtModulus N := by
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hm3 : threePart N ∣ crtModulus N := by
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hm5 : fivePart N ∣ crtModulus N := dvd_mul_left _ _
  constructor
  · exact (crt235_mod_two N 0 1 1).add (Nat.modEq_zero_iff_dvd.mpr hm2)
  constructor
  · have h := (crt235_mod_two N 1 0 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm2).mul_left 4)
    simpa [localATwo, twoPart] using h
  constructor
  · have h := (crt235_mod_three N 0 1 1).add
        (Nat.modEq_zero_iff_dvd.mpr hm3)
    simpa [localAOne, threePart] using h
  constructor
  · exact (crt235_mod_three N 1 0 1).add
      ((Nat.modEq_zero_iff_dvd.mpr hm3).mul_left 4)
  constructor
  · have h := (crt235_mod_five N 0 1 1).add
        (Nat.modEq_zero_iff_dvd.mpr hm5)
    simpa [localAOne, fivePart] using h
  · have h := (crt235_mod_five N 1 0 1).add
        ((Nat.modEq_zero_iff_dvd.mpr hm5).mul_left 4)
    simpa [localATwo, fivePart] using h

end CubicPeriodicTori
