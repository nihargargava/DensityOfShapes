import ApproxScratch

open Filter Set Topology

noncomputable section

def modulus (C : ℕ) : ℕ := 7 * 2 ^ C
lemma modulus_pos (C : ℕ) : 0 < modulus C := by simp [modulus]
def residueMesh (C : ℕ) : Set ℕ :=
  {f | f < modulus C ∧ ∃ R : ℕ, Nat.ModEq (modulus C) (5 ^ R) f}

lemma exists_nonnegative_irrational_close
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hirr : Irrational (A / B))
    (t : ℝ) {e : ℝ} (he : 0 < e) :
    ∃ p q : ℕ, |(p : ℝ) * A - (q : ℝ) * B - t| < e := by
  obtain ⟨p, q, hlim⟩ :=
    exists_nonnegative_irrational_approximation hA hB hirr t
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim e he
  refine ⟨p N, q N, ?_⟩
  have hh := hN N le_rfl
  rw [Real.dist_eq] at hh
  convert hh using 1 <;> ring

lemma test (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Cn fn : ℕ → ℕ,
      (∀ n, fn n ∈ residueMesh (Cn n)) ∧
      Tendsto (fun n ↦ ((fn n : ℕ) : ℝ) / modulus (Cn n)) atTop (nhds s) := by
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · let Cn : ℕ → ℕ := fun n ↦ n
    let fn : ℕ → ℕ := fun _ ↦ 1
    refine ⟨Cn, fn, ?_, ?_⟩
    · intro n
      refine ⟨?_, 0, ?_⟩
      · have hone : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        dsimp [fn, Cn, modulus]
        omega
      · exact Nat.ModEq.refl _
    · have hden : Tendsto (fun n : ℕ ↦ (modulus n : ℝ)) atTop atTop := by
        have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
        have hm := Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 7) hp
        simpa [modulus, Nat.cast_mul, Nat.cast_pow] using hm
      have hz : Tendsto (fun n : ℕ ↦ (1 : ℝ) / modulus n) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      simpa [fn, Cn] using hz
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have heps (n : ℕ) : 0 < (1 : ℝ) / (n + 1) := by positivity
    have hchoice : ∀ n : ℕ, ∃ p q : ℕ,
        |(p : ℝ) * Real.log 5 - (q : ℝ) * Real.log 2 -
          (Real.log s + Real.log 7 - 3 * (1 / ((n : ℝ) + 1)))| <
            1 / ((n : ℝ) + 1) := by
      intro n
      exact exists_nonnegative_irrational_close hlog5 hlog2
        irrational_log_five_div_log_two _ (heps n)
    choose p q hpq using hchoice
    let Cn : ℕ → ℕ := q
    let fn : ℕ → ℕ := fun n ↦ 5 ^ p n
    let L : ℕ → ℝ := fun n ↦
      (p n : ℝ) * Real.log 5 - (q n : ℝ) * Real.log 2 - Real.log 7
    have hL (n : ℕ) :
        |L n - Real.log s| < 4 * (1 / ((n : ℝ) + 1)) := by
      dsimp [L]
      have := hpq n
      rw [abs_lt] at this ⊢
      constructor <;> linarith
    have hdelta : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hfour : Tendsto (fun n : ℕ ↦ 4 * ((1 : ℝ) / (n + 1))) atTop
        (nhds 0) := by
      simpa using hdelta.const_mul 4
    have hLlim : Tendsto L atTop (nhds (Real.log s)) := by
      have hlower : Tendsto
          (fun n : ℕ ↦ Real.log s - 4 * ((1 : ℝ) / (n + 1))) atTop
          (nhds (Real.log s)) := by simpa using tendsto_const_nhds.sub hfour
      have hupper : Tendsto
          (fun n : ℕ ↦ Real.log s + 4 * ((1 : ℝ) / (n + 1))) atTop
          (nhds (Real.log s)) := by simpa using tendsto_const_nhds.add hfour
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
      · exact Filter.Eventually.of_forall fun n ↦ by
          have := (abs_lt.mp (hL n)).1.le
          linarith
      · exact Filter.Eventually.of_forall fun n ↦ by
          have := (abs_lt.mp (hL n)).2.le
          linarith
    have hexp (n : ℕ) :
        Real.exp (L n) = ((fn n : ℕ) : ℝ) / modulus (Cn n) := by
      have hratio : 0 < (((5 : ℝ) ^ p n) / (7 * 2 ^ q n)) := by positivity
      simp only [fn, Cn, modulus, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul]
      rw [← Real.exp_log hratio]
      congr 1
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (by positivity),
        Real.log_pow, Real.log_pow]
      dsimp [L, fn, Cn, modulus]
      push_cast
      ring
    refine ⟨Cn, fn, ?_, ?_⟩
    · intro n
      refine ⟨?_, p n, Nat.ModEq.refl _⟩
      have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs.1 hs.2
      have hLneg : L n < 0 := by
        have hup := (abs_lt.mp (hpq n)).2
        dsimp [L]
        linarith [heps n]
      have hratio : ((fn n : ℕ) : ℝ) / modulus (Cn n) < 1 := by
        rw [← hexp]
        simpa using Real.exp_lt_one_iff.mpr hLneg
      have hcast : ((fn n : ℕ) : ℝ) < modulus (Cn n) :=
        (div_lt_one (by exact_mod_cast modulus_pos (Cn n))).mp hratio
      exact_mod_cast hcast
    · have he := (Real.continuous_exp.tendsto (Real.log s)).comp hLlim
      rw [Real.exp_log hspos] at he
      convert he using 1
      funext n
      exact (hexp n).symm
