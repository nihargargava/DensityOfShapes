import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PowModTotient

open Filter Set Topology

noncomputable section

#check Real.strictMonoOn_log
#check Real.exp_injective
#check Real.log_injOn_pos
#check Nat.Coprime.pow_right
#check Nat.Coprime.pow
#check Nat.coprime_self
#check Int.natAbs_pos
#check Int.natAbs_of_nonneg
#check Nat.ModEq.pow_totient
#check Nat.totient_pos

lemma irrational_log_three_div_log_five :
    Irrational (Real.log 3 / Real.log 5) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hrel : (b : ℝ) * Real.log 3 = (a : ℝ) * Real.log 5 := by
    have hc := (div_eq_div_iff hlog5.ne' (Int.cast_ne_zero.mpr hb)).mp hab
    simpa [mul_comm] using hc
  have hratpos : 0 < (a : ℝ) / (b : ℝ) := by
    rw [← hab]
    exact div_pos hlog3 hlog5
  have impossible (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
      (h : (n : ℝ) * Real.log 3 = (m : ℝ) * Real.log 5) : False := by
    have hlogs : Real.log ((3 : ℝ) ^ n) = Real.log ((5 : ℝ) ^ m) := by
      simpa [Real.log_pow] using h
    have hpowsR : (3 : ℝ) ^ n = (5 : ℝ) ^ m :=
      Real.log_injOn_pos (pow_pos (by norm_num : (0 : ℝ) < 3) _)
        (pow_pos (by norm_num : (0 : ℝ) < 5) _) hlogs
    have hpowsN : 3 ^ n = 5 ^ m := by exact_mod_cast hpowsR
    have hcop : Nat.Coprime (3 ^ n) (5 ^ m) :=
      (by decide : Nat.Coprime 3 5).pow n m
    rw [hpowsN] at hcop
    have hone : 5 ^ m = 1 := (Nat.coprime_self (5 ^ m)).mp hcop
    exact (ne_of_gt (one_lt_pow₀ (by norm_num) hm.ne')) hone
  rcases div_pos_iff.mp hratpos with hpos | hneg
  · have haI : (0 : ℤ) < a := by exact_mod_cast hpos.1
    have hbI : (0 : ℤ) < b := by exact_mod_cast hpos.2
    have haCast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
      norm_cast
      simpa [abs_of_pos haI]
    have hbCast : ((b.natAbs : ℕ) : ℝ) = (b : ℝ) := by
      norm_cast
      simpa [abs_of_pos hbI]
    apply impossible a.natAbs b.natAbs
      (Int.natAbs_pos.mpr haI.ne') (Int.natAbs_pos.mpr hbI.ne')
    simpa [haCast, hbCast] using hrel
  · have haI : a < (0 : ℤ) := by exact_mod_cast hneg.1
    have hbI : b < (0 : ℤ) := by exact_mod_cast hneg.2
    have haCast : ((a.natAbs : ℕ) : ℝ) = -(a : ℝ) := by
      norm_cast
      simpa [abs_of_neg haI]
    have hbCast : ((b.natAbs : ℕ) : ℝ) = -(b : ℝ) := by
      norm_cast
      simpa [abs_of_neg hbI]
    apply impossible a.natAbs b.natAbs
      (Int.natAbs_pos.mpr haI.ne) (Int.natAbs_pos.mpr hbI.ne)
    have := congrArg Neg.neg hrel
    simpa [haCast, hbCast] using this

lemma irrational_scaled_logs (s3 s5 : ℕ) (hs3 : 0 < s3) (hs5 : 0 < s5) :
    Irrational (((s3 : ℝ) * Real.log 3) / ((s5 : ℝ) * Real.log 5)) := by
  have hscaled : Irrational
      ((((s3 : ℝ) * (Real.log 3 / Real.log 5)) / (s5 : ℝ))) :=
    (irrational_log_three_div_log_five.natCast_mul hs3.ne').div_natCast hs5.ne'
  convert hscaled using 1
  have hlog5 : Real.log 5 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hs5R : (s5 : ℝ) ≠ 0 := by exact_mod_cast hs5.ne'
  field_simp

lemma irrational_log_nat_div_log_nat {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hab : a.Coprime b) : Irrational (Real.log a / Real.log b) := by
  rw [irrational_iff_ne_rational]
  intro m n hn hq
  have hloga : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hrel : (n : ℝ) * Real.log a = (m : ℝ) * Real.log b := by
    have hc := (div_eq_div_iff hlogb.ne' (Int.cast_ne_zero.mpr hn)).mp hq
    simpa [mul_comm] using hc
  have hratpos : 0 < (m : ℝ) / (n : ℝ) := by
    rw [← hq]
    exact div_pos hloga hlogb
  have impossible (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
      (h : (v : ℝ) * Real.log a = (u : ℝ) * Real.log b) : False := by
    have hlogs : Real.log ((a : ℝ) ^ v) = Real.log ((b : ℝ) ^ u) := by
      simpa [Real.log_pow] using h
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans ha)
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans hb)
    have hpowsR : (a : ℝ) ^ v = (b : ℝ) ^ u :=
      Real.log_injOn_pos (pow_pos haR _) (pow_pos hbR _) hlogs
    have hpowsN : a ^ v = b ^ u := by exact_mod_cast hpowsR
    have hcop : Nat.Coprime (a ^ v) (b ^ u) := hab.pow v u
    rw [hpowsN] at hcop
    have hone : b ^ u = 1 := (Nat.coprime_self (b ^ u)).mp hcop
    exact (ne_of_gt (one_lt_pow₀ hb hu.ne')) hone
  rcases div_pos_iff.mp hratpos with hpos | hneg
  · have hmI : (0 : ℤ) < m := by exact_mod_cast hpos.1
    have hnI : (0 : ℤ) < n := by exact_mod_cast hpos.2
    have hmCast : ((m.natAbs : ℕ) : ℝ) = (m : ℝ) := by simpa [abs_of_pos hmI]
    have hnCast : ((n.natAbs : ℕ) : ℝ) = (n : ℝ) := by simpa [abs_of_pos hnI]
    apply impossible m.natAbs n.natAbs
      (Int.natAbs_pos.mpr hmI.ne') (Int.natAbs_pos.mpr hnI.ne')
    simpa [hmCast, hnCast] using hrel
  · have hmI : m < (0 : ℤ) := by exact_mod_cast hneg.1
    have hnI : n < (0 : ℤ) := by exact_mod_cast hneg.2
    have hmCast : ((m.natAbs : ℕ) : ℝ) = -(m : ℝ) := by simpa [abs_of_neg hmI]
    have hnCast : ((n.natAbs : ℕ) : ℝ) = -(n : ℝ) := by simpa [abs_of_neg hnI]
    apply impossible m.natAbs n.natAbs
      (Int.natAbs_pos.mpr hmI.ne) (Int.natAbs_pos.mpr hnI.ne)
    have hnegrel := congrArg Neg.neg hrel
    simpa [hmCast, hnCast] using hnegrel

lemma irrational_log_five_div_log_two :
    Irrational (Real.log 5 / Real.log 2) :=
  irrational_log_nat_div_log_nat (by norm_num) (by norm_num) (by norm_num)

lemma exists_nonnegative_irrational_approximation
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hirr : Irrational (A / B))
    (t : ℝ) :
    ∃ p q : ℕ → ℕ,
      Tendsto (fun n ↦ (p n : ℝ) * A - (q n : ℝ) * B) atTop (nhds t) := by
  letI : Fact (0 < B) := ⟨hB⟩
  have hdZ : DenseRange (fun z : ℤ ↦ z • (A : AddCircle B)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  have hdN : DenseRange (fun n : ℕ ↦ n • (A : AddCircle B)) :=
    denseRange_zsmul_iff_nsmul.mp hdZ
  obtain ⟨P, hP⟩ := exists_nat_gt ((t + B / 2) / A)
  have hPA : t + B / 2 < (P : ℝ) * A := by
    calc
      t + B / 2 = ((t + B / 2) / A) * A :=
        (div_mul_cancel₀ _ hA.ne').symm
      _ < (P : ℝ) * A := mul_lt_mul_of_pos_right hP hA
  let target : AddCircle B := (t - (P : ℝ) * A : ℝ)
  have htarget : target ∈ closure (Set.range fun n : ℕ ↦ n • (A : AddCircle B)) := by
    rw [hdN.closure_eq]
    exact Set.mem_univ _
  rcases mem_closure_iff_seq_limit.mp htarget with ⟨x, hx, hxlim⟩
  choose k hk using hx
  have hklim : Tendsto (fun n ↦ k n • (A : AddCircle B)) atTop (nhds target) := by
    simpa only [hk] using hxlim
  let p : ℕ → ℕ := fun n ↦ P + k n
  have hplim : Tendsto (fun n ↦ p n • (A : AddCircle B)) atTop
      (nhds (t : AddCircle B)) := by
    have hcP : Tendsto (fun _ : ℕ ↦ P • (A : AddCircle B)) atTop
        (nhds (P • (A : AddCircle B))) := tendsto_const_nhds
    have hsum := hcP.add hklim
    simpa [p, target, add_nsmul, add_assoc] using hsum
  let a : ℝ := t - B / 2
  have ht_mem : t ∈ Set.Ico a (a + B) := by
    constructor <;> dsimp [a] <;> linarith
  have ha_mem : a ∈ Set.Ico a (a + B) := by
    exact ⟨le_rfl, lt_add_of_pos_right _ hB⟩
  have hcoe_ne : (t : AddCircle B) ≠ (a : AddCircle B) := by
    intro h
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht_mem ha_mem).mp h
    dsimp [a] at this
    linarith
  let r : ℕ → ℝ := fun n ↦ (AddCircle.equivIco B a (p n • (A : AddCircle B)) : ℝ)
  have hrlim : Tendsto r atTop (nhds t) := by
    have hc := (AddCircle.continuousAt_equivIco B a hcoe_ne).tendsto.comp hplim
    have heq : AddCircle.equivIco B a (t : AddCircle B) = ⟨t, ht_mem⟩ := by
      apply (AddCircle.equivIco B a).symm.injective
      rw [(AddCircle.equivIco B a).symm_apply_apply]
      change (t : AddCircle B) = (t : AddCircle B)
      rfl
    have hc' := continuous_subtype_val.continuousAt.tendsto.comp hc
    change Tendsto (fun n ↦
      ((AddCircle.equivIco B a (p n • (A : AddCircle B))) : ℝ)) atTop (nhds t)
    convert hc' using 1
    · funext n
      rfl
    · rw [heq]
  have hmultiple (n : ℕ) :
      ∃ z : ℤ, (z : ℝ) * B = (p n : ℝ) * A - r n := by
    have hcoe : (r n : AddCircle B) = ((p n : ℕ) : ℝ) * A := by
      change ((AddCircle.equivIco B a (p n • (A : AddCircle B)) : ℝ) :
          AddCircle B) = _
      have he := (AddCircle.equivIco B a).symm_apply_apply
        (p n • (A : AddCircle B))
      change ((AddCircle.equivIco B a (p n • (A : AddCircle B)) : ℝ) :
          AddCircle B) = p n • (A : AddCircle B) at he
      simpa using he
    have hmem : (r n - (p n : ℝ) * A) ∈ AddSubgroup.zmultiples B :=
      QuotientAddGroup.eq_iff_sub_mem.mp hcoe
    rcases AddSubgroup.mem_zmultiples_iff.mp hmem with ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    change ((-z : ℤ) : ℝ) * B = _
    rw [Int.cast_neg, neg_mul, ← zsmul_eq_mul]
    rw [hz]
    ring
  choose z hz using hmultiple
  have hz_nonneg (n : ℕ) : 0 ≤ z n := by
    have hr_lt : r n < a + B := (AddCircle.equivIco B a _).property.2
    have hdiff : 0 < (p n : ℝ) * A - r n := by
      have hp_le : (P : ℝ) ≤ p n := by
        exact_mod_cast Nat.le_add_right P (k n)
      have : (P : ℝ) * A ≤ (p n : ℝ) * A :=
        mul_le_mul_of_nonneg_right hp_le hA.le
      dsimp [a] at hr_lt
      linarith
    have : (0 : ℝ) < (z n : ℝ) * B := hz n ▸ hdiff
    have hzpos : (0 : ℝ) < (z n : ℝ) := by
      rcases mul_pos_iff.mp this with hpos | hneg
      · exact hpos.1
      · exact False.elim (not_lt_of_ge hB.le hneg.2)
    exact_mod_cast hzpos.le
  let q : ℕ → ℕ := fun n ↦ (z n).toNat
  refine ⟨p, q, ?_⟩
  convert hrlim using 1
  funext n
  have hzcast : (((q n : ℕ) : ℝ)) = (z n : ℝ) := by
    norm_cast
    exact Int.toNat_of_nonneg (hz_nonneg n)
  rw [hzcast, hz n]
  ring
