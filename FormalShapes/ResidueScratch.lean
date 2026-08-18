import Mathlib.RingTheory.ZMod.UnitsCyclic

open Set

lemma residue_classification (C f : ℕ) (hf : f < 7 * 2 ^ (C + 4))
    (hpow : ∃ R : ℕ, Nat.ModEq (7 * 2 ^ (C + 4)) (5 ^ R) f) :
    ∃ k : ℕ, ∃ j ∈ ({1, 5, 9, 13, 25, 45} : Set ℕ), f = 56 * k + j := by
  rcases hpow with ⟨R, hR⟩
  refine ⟨f / 56, f % 56, ?_, ?_⟩
  · have h56dvd : 56 ∣ 7 * 2 ^ (C + 4) := by
      refine ⟨2 ^ C, ?_⟩
      rw [show C + 4 = C + 1 + 1 + 1 + 1 by omega]
      repeat' rw [pow_succ]
      ring
    have hm : Nat.ModEq 56 (5 ^ R) f := hR.of_dvd h56dvd
    change f % 56 = 1 ∨ f % 56 = 5 ∨ f % 56 = 9 ∨ f % 56 = 13 ∨
      f % 56 = 25 ∨ f % 56 = 45
    have hperiod : Nat.ModEq 56 (5 ^ 6) 1 := by decide
    have hrexp : 5 ^ R % 56 = 5 ^ (R % 6) % 56 := by
      rw [← Nat.mod_add_div R 6, pow_add, pow_mul]
      have := hperiod.pow (R / 6)
      exact this.mul_right (5 ^ (R % 6))
    have hfmod : f % 56 = 5 ^ (R % 6) % 56 := by
      exact hm.symm
    rw [hfmod]
    interval_cases hcase : R % 6 <;> norm_num
  · omega
