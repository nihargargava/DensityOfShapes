import BananaLemma
import ABCFundamentalUnits
import ABCLocalUnits
import ABCMovingFrames
import ABCScalarUnits
import ABCUnitLogs
import ArithmeticConstruction
import CRTFamily
import DynamicsCore
import OrderPeriods
import CusickRegulator
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Density of shapes of periodic tori in the cubic case

This file formalizes the statement of Theorem 1.1 in

Nguyen-Thi Dang, Nihar Gargava, and Jialun Li,
*Density of shapes of periodic tori in the cubic case*, arXiv:2502.12754.

The definitions below make the two homogeneous spaces, the period lattice,
and its normalized shape explicit.  The proof is organized according to
Sections 2--5 of the paper.  The banana argument is isolated in
`SL2Banana.banana_expanding_horocycle_dense`; `paper_construction` packages
the arithmetic construction and approximation arguments.
-/

noncomputable section

namespace CubicPeriodicTori
namespace Proposition52

open Filter Set Topology

/-- The elementary multiplicative-independence fact behind both irrational
rotation arguments in Proposition 5.2. -/
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
      simpa [abs_of_pos haI]
    have hbCast : ((b.natAbs : ℕ) : ℝ) = (b : ℝ) := by
      simpa [abs_of_pos hbI]
    apply impossible a.natAbs b.natAbs
      (Int.natAbs_pos.mpr haI.ne') (Int.natAbs_pos.mpr hbI.ne')
    simpa [haCast, hbCast] using hrel
  · have haI : a < (0 : ℤ) := by exact_mod_cast hneg.1
    have hbI : b < (0 : ℤ) := by exact_mod_cast hneg.2
    have haCast : ((a.natAbs : ℕ) : ℝ) = -(a : ℝ) := by
      simpa [abs_of_neg haI]
    have hbCast : ((b.natAbs : ℕ) : ℝ) = -(b : ℝ) := by
      simpa [abs_of_neg hbI]
    apply impossible a.natAbs b.natAbs
      (Int.natAbs_pos.mpr haI.ne) (Int.natAbs_pos.mpr hbI.ne)
    have hnegrel := congrArg Neg.neg hrel
    simpa [haCast, hbCast] using hnegrel

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

/-- If `A/B` is irrational and both numbers are positive, nonnegative
integral combinations `p A - q B` approximate every real target.  The proof
uses the dense forward orbit on the circle of length `B`, then continuously
lifts it to a fundamental interval chosen around the target. -/
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
  have htarget : target ∈ closure (Set.range fun n : ℕ ↦
      n • (A : AddCircle B)) := by
    rw [hdN.closure_eq]
    exact Set.mem_univ _
  rcases mem_closure_iff_seq_limit.mp htarget with ⟨x, hx, hxlim⟩
  choose k hk using hx
  have hklim : Tendsto (fun n ↦ k n • (A : AddCircle B)) atTop
      (nhds target) := by
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
  have ha_mem : a ∈ Set.Ico a (a + B) :=
    ⟨le_rfl, lt_add_of_pos_right _ hB⟩
  have hcoe_ne : (t : AddCircle B) ≠ (a : AddCircle B) := by
    intro h
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht_mem ha_mem).mp h
    dsimp [a] at heq
    linarith
  let r : ℕ → ℝ := fun n ↦
    (AddCircle.equivIco B a (p n • (A : AddCircle B)) : ℝ)
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
    rw [Int.cast_neg, neg_mul, ← zsmul_eq_mul]
    rw [hz]
    ring
  choose z hz using hmultiple
  have hz_nonneg (n : ℕ) : 0 ≤ z n := by
    have hr_lt : r n < a + B := (AddCircle.equivIco B a _).property.2
    have hdiff : 0 < (p n : ℝ) * A - r n := by
      have hp_le : (P : ℝ) ≤ p n := by
        exact_mod_cast Nat.le_add_right P (k n)
      have hpA : (P : ℝ) * A ≤ (p n : ℝ) * A :=
        mul_le_mul_of_nonneg_right hp_le hA.le
      dsimp [a] at hr_lt
      linarith
    have hzB : (0 : ℝ) < (z n : ℝ) * B := hz n ▸ hdiff
    have hzpos : (0 : ℝ) < (z n : ℝ) := by
      rcases mul_pos_iff.mp hzB with hpos | hneg
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

/-! ### The corrected congruence calculation in Lemma 5.1 -/

/-- Equation (7), reindexed by `C=c-4`, `D=d-2`, and `R=r-1`. -/
def exponentLattice (C D R : ℕ) : Set (ℤ × ℤ) :=
  {mn |
    (7 * 2 ^ (C + 3) : ℤ) ∣ mn.1 + mn.2 ∧
    (8 * 3 ^ (D + 1) : ℤ) ∣ mn.1 - 2 * mn.2 ∧
    (24 * 5 ^ R : ℤ) ∣ 2 * mn.1 - mn.2}

/-- The right side of Lemma 5.1.  The displayed fixed matrix is
`g = 8 * [[-1,2],[-2,1]]`. -/
def parametrizedExponentLattice (C D R : ℕ) : Set (ℤ × ℤ) :=
  {mn | ∃ x y : ℤ,
    (7 * 2 ^ C : ℤ) ∣ 3 ^ D * x - 5 ^ R * y ∧
    mn =
      (8 * (-(3 ^ D * x) + 2 * (5 ^ R * y)),
       8 * (-2 * (3 ^ D * x) + 5 ^ R * y))}

/-- Corrected Lemma 5.1.  This coordinate proof avoids the two typos in the
printed Smith-normal-form calculation. -/
theorem exponentLattice_eq_parametrized (C D R : ℕ) :
    exponentLattice C D R = parametrizedExponentLattice C D R := by
  ext mn
  rcases mn with ⟨m, n⟩
  simp only [exponentLattice, parametrizedExponentLattice, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hSum, hSecond, hThird⟩
    rcases hSum with ⟨k, hk⟩
    rcases hSecond with ⟨x, hx⟩
    rcases hThird with ⟨y, hy⟩
    have hx' : m - 2 * n = 24 * (3 ^ D * x) := by
      calc
        m - 2 * n = (8 * 3 ^ (D + 1)) * x := hx
        _ = 24 * (3 ^ D * x) := by rw [pow_succ]; ring
    have hy' : 2 * m - n = 24 * (5 ^ R * y) := by
      calc
        2 * m - n = (24 * 5 ^ R) * y := hy
        _ = 24 * (5 ^ R * y) := by ring
    have hcoprime : IsCoprime (7 * 2 ^ C : ℤ) 3 := by
      have h37 : IsCoprime (3 : ℤ) 7 :=
        ⟨5, -2, by norm_num⟩
      have h32 : IsCoprime (3 : ℤ) 2 :=
        ⟨1, -1, by norm_num⟩
      exact (h37.mul_right h32.pow_right).symm
    have hk' : m + n = 8 * ((7 * 2 ^ C) * k) := by
      calc
        m + n = (7 * 2 ^ (C + 3)) * k := hk
        _ = 8 * ((7 * 2 ^ C) * k) := by
          rw [show C + 3 = C + 1 + 1 + 1 by omega]
          repeat' rw [pow_succ]
          ring
    have hlinear :
        3 * (5 ^ R * y - 3 ^ D * x) = (7 * 2 ^ C) * k := by
      omega
    have hremaining : (7 * 2 ^ C : ℤ) ∣ 3 ^ D * x - 5 ^ R * y := by
      apply hcoprime.dvd_of_dvd_mul_left
      refine ⟨-k, ?_⟩
      calc
        3 * (3 ^ D * x - 5 ^ R * y) =
            -(3 * (5 ^ R * y - 3 ^ D * x)) := by ring
        _ = -((7 * 2 ^ C) * k) := by rw [hlinear]
        _ = (7 * 2 ^ C) * (-k) := by ring
    refine ⟨x, y, hremaining, ?_⟩
    apply Prod.ext <;> simp only
    · omega
    · omega
  · rintro ⟨x, y, hremaining, hmn⟩
    have hm : m = 8 * (-(3 ^ D * x) + 2 * (5 ^ R * y)) :=
      congrArg Prod.fst hmn
    have hn : n = 8 * (-2 * (3 ^ D * x) + 5 ^ R * y) :=
      congrArg Prod.snd hmn
    subst m
    subst n
    rcases hremaining with ⟨k, hk⟩
    constructor
    · refine ⟨-3 * k, ?_⟩
      calc
        8 * (-(3 ^ D * x) + 2 * (5 ^ R * y)) +
            8 * (-2 * (3 ^ D * x) + 5 ^ R * y) =
            -24 * (3 ^ D * x - 5 ^ R * y) := by ring
        _ = -24 * ((7 * 2 ^ C) * k) := by rw [hk]
        _ = (7 * 2 ^ (C + 3)) * (-3 * k) := by
          rw [show C + 3 = C + 1 + 1 + 1 by omega]
          repeat' rw [pow_succ]
          ring
    constructor
    · refine ⟨x, ?_⟩
      rw [pow_succ]
      ring
    · refine ⟨y, ?_⟩
      ring

/-! ### The auxiliary lattices in Proposition 5.2 -/

/-- We remove the shifts in the paper: `(C,D,R)` below corresponds to
`(c,d,r) = (C+4,D+2,R+1)` in its notation.  This also repairs the implicit
index shift in the horospherical part of the printed proof. -/
abbrev Index := ℕ × ℕ × ℕ

def modulus (C : ℕ) : ℕ := 7 * 2 ^ C

def firstScale (D : ℕ) : ℕ := 3 ^ D

def secondScale (R : ℕ) : ℕ := 5 ^ R

lemma modulus_pos (C : ℕ) : 0 < modulus C := by
  simp [modulus]

instance (C : ℕ) : NeZero (modulus C) := ⟨(modulus_pos C).ne'⟩

lemma firstScale_coprime_modulus (C D : ℕ) :
    (firstScale D).Coprime (modulus C) := by
  apply Nat.Coprime.pow_left D
  apply Nat.Coprime.mul_right
  · norm_num
  · exact (by norm_num : Nat.Coprime 3 2).pow_right C

lemma five_coprime_modulus (C : ℕ) : (5 : ℕ).Coprime (modulus C) := by
  apply Nat.Coprime.mul_right
  · norm_num
  · exact (by norm_num : Nat.Coprime 5 2).pow_right C

/-- A simultaneous positive period for `3` and `5` modulo `7 * 2^C`. -/
def periodExponent (C : ℕ) : ℕ := Nat.totient (modulus C)

lemma periodExponent_pos (C : ℕ) : 0 < periodExponent C := by
  exact Nat.totient_pos.mpr (modulus_pos C)

lemma three_pow_periodExponent_modEq (C : ℕ) :
    Nat.ModEq (modulus C) (3 ^ periodExponent C) 1 := by
  simpa [firstScale, periodExponent] using
    (Nat.ModEq.pow_totient (firstScale_coprime_modulus C 1))

lemma five_pow_periodExponent_modEq (C : ℕ) :
    Nat.ModEq (modulus C) (5 ^ periodExponent C) 1 := by
  exact Nat.ModEq.pow_totient (five_coprime_modulus C)

/-- `3^D`, regarded as a unit modulo `7 * 2^C`. -/
def firstScaleUnit (C D : ℕ) : (ZMod (modulus C))ˣ :=
  ((ZMod.isUnit_iff_coprime (firstScale D) (modulus C)).2
    (firstScale_coprime_modulus C D)).unit

/-- The representative `f` characterized by
`3^D f = 5^R (mod 7 * 2^C)`. -/
def residue (C D R : ℕ) : ℕ :=
  (((firstScaleUnit C D)⁻¹ : ZMod (modulus C)) * secondScale R).val

lemma residue_lt (C D R : ℕ) : residue C D R < modulus C :=
  ZMod.val_lt _

lemma residue_spec_zmod (C D R : ℕ) :
    (firstScale D : ZMod (modulus C)) * residue C D R = secondScale R := by
  rw [show (residue C D R : ZMod (modulus C)) =
      ((firstScaleUnit C D)⁻¹ : ZMod (modulus C)) * secondScale R by
        exact ZMod.natCast_zmod_val _]
  rw [show (firstScale D : ZMod (modulus C)) =
      (firstScaleUnit C D : ZMod (modulus C)) by
        exact (IsUnit.unit_spec _).symm]
  simp

lemma residue_spec (C D R : ℕ) :
    Nat.ModEq (modulus C) (firstScale D * residue C D R)
      (secondScale R) := by
  exact (ZMod.natCast_eq_natCast_iff
    (firstScale D * residue C D R) (secondScale R) (modulus C)).mp
      (by simpa only [Nat.cast_mul] using residue_spec_zmod C D R)

/-- The integral congruence kernel before diagonal scaling. -/
def congruenceSolutions (C D R : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (firstScale D : ZMod (modulus C)) * v 0 =
    (secondScale R : ZMod (modulus C)) * v 1}

/-- The explicit column basis `(q,0),(f,1)` of the congruence kernel. -/
def congruenceBasis (C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(modulus C : ℤ), (residue C D R : ℤ); 0, 1]

lemma congruenceSolutions_eq_range_mulVec (C D R : ℕ) :
    congruenceSolutions C D R =
      Set.range (congruenceBasis C D R).mulVec := by
  ext v
  constructor
  · intro hv
    have hA : IsUnit (firstScale D : ZMod (modulus C)) :=
      (ZMod.isUnit_iff_coprime (firstScale D) (modulus C)).2
        (firstScale_coprime_modulus C D)
    have hyz : (v 0 : ZMod (modulus C)) =
        (residue C D R : ZMod (modulus C)) * v 1 := by
      apply hA.mul_left_cancel
      calc
        (firstScale D : ZMod (modulus C)) * v 0 =
            (secondScale R : ZMod (modulus C)) * v 1 := hv
        _ = ((firstScale D : ZMod (modulus C)) * residue C D R) *
            v 1 := by rw [residue_spec_zmod]
        _ = (firstScale D : ZMod (modulus C)) *
            ((residue C D R : ZMod (modulus C)) * v 1) := by ring
    have hdiv : (modulus C : ℤ) ∣
        (residue C D R : ℤ) * v 1 - v 0 := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact_mod_cast hyz
    rcases hdiv with ⟨k, hk⟩
    refine ⟨![(-k), v 1], ?_⟩
    funext i
    fin_cases i
    · simp [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linarith
    · simp [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rintro ⟨z, rfl⟩
    simp only [congruenceSolutions, Set.mem_setOf_eq]
    simp [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [← mul_assoc, residue_spec_zmod]

/-- The fixed integral change of exponent coordinates in Lemma 5.1. -/
def exponentChange : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-8, 16; -16, 8]

/-- An explicit column basis of the three-congruence exponent lattice. -/
def exponentBasis (C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  exponentChange *
    !![((firstScale D * modulus C : ℕ) : ℤ),
        ((firstScale D * residue C D R : ℕ) : ℤ);
       0, ((secondScale R : ℕ) : ℤ)]

lemma exponentBasis_apply (C D R : ℕ) :
    exponentBasis C D R =
      !![-8 * ((firstScale D * modulus C : ℕ) : ℤ),
          -8 * ((firstScale D * residue C D R : ℕ) : ℤ) +
            16 * ((secondScale R : ℕ) : ℤ);
         -16 * ((firstScale D * modulus C : ℕ) : ℤ),
          -16 * ((firstScale D * residue C D R : ℕ) : ℤ) +
            8 * ((secondScale R : ℕ) : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentBasis, exponentChange, Matrix.mul_apply, Fin.sum_univ_two]

/-- Equation (7) and corrected Lemma 5.1, combined into an actual basis
statement rather than an equality of parametrized sets. -/
theorem exponentLattice_eq_range_exponentBasis (C D R : ℕ) :
    exponentLattice C D R = Set.range (fun z : Fin 2 → ℤ ↦
      ((exponentBasis C D R).mulVec z 0,
       (exponentBasis C D R).mulVec z 1)) := by
  rw [exponentLattice_eq_parametrized]
  ext mn
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    have hcong : ![x, y] ∈ congruenceSolutions C D R := by
      simp only [congruenceSolutions, Set.mem_setOf_eq]
      have hcast :
          (((firstScale D : ℤ) * x : ℤ) : ZMod (modulus C)) =
            (((secondScale R : ℤ) * y : ℤ) : ZMod (modulus C)) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        simpa [firstScale, secondScale, modulus, sub_eq_neg_add,
          add_comm, add_left_comm, add_assoc] using hxy.neg_right
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast] using hcast
    rw [congruenceSolutions_eq_range_mulVec] at hcong
    rcases hcong with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hx := congrFun hz 0
    have hy := congrFun hz 1
    simp [congruenceBasis, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at hx hy
    have hx' := hx.symm
    have hy' := hy.symm
    subst x
    subst y
    apply Prod.ext <;> simp only
    ·
      simp [exponentBasis_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        firstScale, secondScale]
      ring
    ·
      simp [exponentBasis_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        firstScale, secondScale]
      ring
  · rintro ⟨z, rfl⟩
    let x : ℤ := (modulus C : ℤ) * z 0 + (residue C D R : ℤ) * z 1
    let y : ℤ := z 1
    refine ⟨x, y, ?_, ?_⟩
    · have hspec :
          (((firstScale D : ℤ) * (residue C D R : ℤ) : ℤ) :
              ZMod (modulus C)) = (secondScale R : ℤ) := by
        push_cast
        simpa only [Nat.cast_mul] using residue_spec_zmod C D R
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hspec
      rcases hspec with ⟨k, hk⟩
      refine ⟨(firstScale D : ℤ) * z 0 - k * z 1, ?_⟩
      dsimp [x, y]
      change (firstScale D : ℤ) *
          ((modulus C : ℤ) * z 0 + (residue C D R : ℤ) * z 1) -
        (secondScale R : ℤ) * z 1 =
          (modulus C : ℤ) * ((firstScale D : ℤ) * z 0 - k * z 1)
      have hneg : (firstScale D : ℤ) * (residue C D R : ℤ) -
          (secondScale R : ℤ) = -(modulus C : ℤ) * k := by
        linarith [hk]
      calc
        (firstScale D : ℤ) *
              ((modulus C : ℤ) * z 0 + (residue C D R : ℤ) * z 1) -
            (secondScale R : ℤ) * z 1 =
            (modulus C : ℤ) * ((firstScale D : ℤ) * z 0) +
              ((firstScale D : ℤ) * (residue C D R : ℤ) -
                (secondScale R : ℤ)) * z 1 := by ring
        _ = (modulus C : ℤ) * ((firstScale D : ℤ) * z 0 - k * z 1) := by
          rw [hneg]
          ring
    · apply Prod.ext <;> simp only
      · simp [x, y, exponentBasis_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, firstScale, secondScale]
        ring
      · simp [x, y, exponentBasis_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, firstScale, secondScale]
        ring

/-- The basis obtained after applying `diag(3^D,5^R)`. -/
def lambdaBasis (C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(firstScale D * modulus C : ℕ),
      (firstScale D * residue C D R : ℕ);
     0, (secondScale R : ℕ)]

lemma lambdaBasis_det (C D R : ℕ) :
    (lambdaBasis C D R).det =
      (firstScale D * modulus C * secondScale R : ℕ) := by
  simp [lambdaBasis, Matrix.det_fin_two]

lemma lambdaBasis_det_pos (C D R : ℕ) :
    0 < (lambdaBasis C D R).det := by
  rw [lambdaBasis_det]
  norm_num [firstScale, secondScale, modulus]

/-- The normalized shape of the paper's auxiliary lattice
`Λ_{C+4,D+2,R+1}`. -/
def lambdaShape (C D R : ℕ) : ShapeSpace :=
  (normalizeBasis (lambdaBasis C D R) (lambdaBasis_det_pos C D R) :
    ShapeSpace)

private lemma normalize_left (A B Q : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hQ : 0 < Q) :
    (Real.sqrt (A * Q * B))⁻¹ * (A * Q) = Real.sqrt (A * Q / B) := by
  rw [← (sq_eq_sq₀ (by positivity) (by positivity))]
  rw [Real.sq_sqrt (by positivity), inv_mul_eq_div, div_pow]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

private lemma normalize_bottom (A B Q : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hQ : 0 < Q) :
    (Real.sqrt (A * Q * B))⁻¹ * B = (Real.sqrt (A * Q / B))⁻¹ := by
  rw [← (sq_eq_sq₀ (by positivity) (by positivity))]
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [inv_mul_eq_div, div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- A canonical determinant-one representative of the same auxiliary shape. -/
def canonicalLambdaMatrix (C D R : ℕ) : SL2R :=
  let x := Real.sqrt
    (((firstScale D : ℕ) : ℝ) * modulus C / secondScale R)
  ⟨!![x, x * ((residue C D R : ℕ) : ℝ) / modulus C;
      0, x⁻¹], by
    have hx : x ≠ 0 := by
      dsimp [x]
      apply ne_of_gt
      apply Real.sqrt_pos.2
      exact div_pos (mul_pos (by norm_num [firstScale]) (by
        exact_mod_cast modulus_pos C)) (by norm_num [secondScale])
    simp [Matrix.det_fin_two, hx]⟩

lemma lambdaShape_eq_canonical (C D R : ℕ) :
    lambdaShape C D R = (canonicalLambdaMatrix C D R : ShapeSpace) := by
  apply congrArg (fun g : SL2R ↦ (g : ShapeSpace))
  apply Subtype.ext
  have hA : 0 < (((firstScale D : ℕ) : ℝ)) := by norm_num [firstScale]
  have hB : 0 < (((secondScale R : ℕ) : ℝ)) := by norm_num [secondScale]
  have hQ : 0 < (((modulus C : ℕ) : ℝ)) := by exact_mod_cast modulus_pos C
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [normalizeBasis, lambdaBasis, lambdaBasis_det, canonicalLambdaMatrix]
      using normalize_left (((firstScale D : ℕ) : ℝ))
        (((secondScale R : ℕ) : ℝ)) (((modulus C : ℕ) : ℝ)) hA hB hQ
  · simp [normalizeBasis, lambdaBasis, canonicalLambdaMatrix]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hA),
      ne_of_gt (Real.sqrt_pos.2 hB), ne_of_gt (Real.sqrt_pos.2 hQ),
      Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, Real.sq_sqrt hQ.le]
    rw [Real.sq_sqrt hQ.le, Real.sq_sqrt hA.le]
    ring
  · simp [normalizeBasis, lambdaBasis, canonicalLambdaMatrix]
  · simpa [normalizeBasis, lambdaBasis, lambdaBasis_det, canonicalLambdaMatrix]
      using normalize_bottom (((firstScale D : ℕ) : ℝ))
        (((secondScale R : ℕ) : ℝ)) (((modulus C : ℕ) : ℝ)) hA hB hQ

def aspectLog (C D R : ℕ) : ℝ :=
  Real.log ((((firstScale D : ℕ) : ℝ) * modulus C) / secondScale R)

lemma aspectLog_eq (C D R : ℕ) :
    aspectLog C D R =
      (D : ℝ) * Real.log 3 + Real.log (modulus C) - (R : ℝ) * Real.log 5 := by
  have hA : (((firstScale D : ℕ) : ℝ)) ≠ 0 := by norm_num [firstScale]
  have hB : (((secondScale R : ℕ) : ℝ)) ≠ 0 := by norm_num [secondScale]
  have hQ : (((modulus C : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (modulus_pos C).ne'
  rw [aspectLog, Real.log_div (mul_ne_zero hA hQ) hB,
    Real.log_mul hA hQ]
  simp [firstScale, secondScale, Real.log_pow]

/-- Canonical upper-triangular coordinates on the shape space. -/
def timeMatrix (C f : ℕ) (x : ℝ) : SL2R :=
  ⟨!![Real.exp (x / 2),
      Real.exp (x / 2) * ((f : ℕ) : ℝ) / modulus C;
      0, Real.exp (-x / 2)], by
    simp [Matrix.det_fin_two, ← Real.exp_add]
    ring_nf⟩

lemma canonicalLambdaMatrix_eq_timeMatrix (C D R : ℕ) :
    canonicalLambdaMatrix C D R =
      timeMatrix C (residue C D R) (aspectLog C D R) := by
  apply Subtype.ext
  have hratio : 0 < ((((firstScale D : ℕ) : ℝ) * modulus C) / secondScale R) :=
    div_pos (mul_pos (by norm_num [firstScale]) (by exact_mod_cast modulus_pos C))
      (by norm_num [secondScale])
  ext i j
  fin_cases i <;> fin_cases j
  · change Real.sqrt _ = Real.exp (Real.log _ / 2)
    rw [Real.exp_half, Real.exp_log hratio]
  · change Real.sqrt _ * _ / _ = Real.exp (Real.log _ / 2) * _ / _
    rw [Real.exp_half, Real.exp_log hratio]
  · rfl
  · change (Real.sqrt _)⁻¹ = Real.exp (-Real.log _ / 2)
    rw [show -Real.log ((((firstScale D : ℕ) : ℝ) * modulus C) /
          secondScale R) / 2 =
        -(Real.log ((((firstScale D : ℕ) : ℝ) * modulus C) /
          secondScale R) / 2) by ring,
      Real.exp_neg, Real.exp_half, Real.exp_log hratio]

lemma lambdaShape_eq_timeMatrix (C D R : ℕ) :
    lambdaShape C D R =
      (timeMatrix C (residue C D R) (aspectLog C D R) : ShapeSpace) := by
  rw [lambdaShape_eq_canonical, canonicalLambdaMatrix_eq_timeMatrix]

lemma continuous_timeMatrix (C f : ℕ) : Continuous (timeMatrix C f) := by
  refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
  exact continuous_matrix fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp [timeMatrix] <;> fun_prop

lemma continuous_timeShape (C f : ℕ) :
    Continuous (fun x : ℝ ↦ (timeMatrix C f x : ShapeSpace)) := by
  exact continuous_quot_mk.comp (continuous_timeMatrix C f)

def lambdaShapes : Set ShapeSpace :=
  Set.range fun i : Index ↦ lambdaShape i.1 i.2.1 i.2.2

def omega : Set ShapeSpace := closure lambdaShapes

/-- `a(t) = diag(exp(t/2), exp(-t/2))`. -/
def diagonalFlow (t : ℝ) : SL2R :=
  ⟨!![Real.exp (t / 2), 0; 0, Real.exp (-t / 2)], by
    simp [Matrix.det_fin_two, ← Real.exp_add]
    ring_nf⟩

lemma timeMatrix_add (C f : ℕ) (x t : ℝ) :
    timeMatrix C f (x + t) = diagonalFlow t * timeMatrix C f x := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two,
      ← Real.exp_add]
    ring
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two]
    rw [show (x + t) / 2 = t / 2 + x / 2 by ring, Real.exp_add]
    ring
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [timeMatrix, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two,
      ← Real.exp_add]
    ring

/-- `u(s) = [[1,s],[0,1]]`. -/
def horocycle (s : ℝ) : SL2R :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma timeMatrix_zero (C f : ℕ) :
    timeMatrix C f 0 = horocycle ((f : ℝ) / modulus C) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [timeMatrix, horocycle]

def squareShape : ShapeSpace := (1 : SL2R)

/-- Representatives of the subgroup generated by `5` modulo `7 * 2^C`,
chosen in `[0,7 * 2^C)`.  This is the set `S_C` in Section 5.2. -/
def residueMesh (C : ℕ) : Set ℕ :=
  {f | f < modulus C ∧ ∃ R : ℕ, Nat.ModEq (modulus C) (5 ^ R) f}

/-- The exponent data in equation (10).  The modular-period fields preserve
the congruence kernel; `log_tendsto` is the irrational-rotation
approximation of the required diagonal displacement. -/
structure DiagonalExponentApproximation (C D R : ℕ) (t : ℝ) where
  s3 : ℕ
  s5 : ℕ
  s3_pos : 0 < s3
  s5_pos : 0 < s5
  period3 : Nat.ModEq (modulus C) (3 ^ s3) 1
  period5 : Nat.ModEq (modulus C) (5 ^ s5) 1
  p : ℕ → ℕ
  q : ℕ → ℕ
  log_tendsto : Tendsto
    (fun n ↦ ((p n * s3 : ℕ) : ℝ) * Real.log 3 -
      ((q n * s5 : ℕ) : ℝ) * Real.log 5)
    atTop (𝓝 t)

def DiagonalExponentApproximation.Dindex
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) : ℕ :=
  D + h.s3 * h.p n

def DiagonalExponentApproximation.Rindex
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) : ℕ :=
  R + h.s5 * h.q n

lemma DiagonalExponentApproximation.firstScale_modEq
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) :
    Nat.ModEq (modulus C) (firstScale (h.Dindex n)) (firstScale D) := by
  calc
    firstScale (h.Dindex n) = 3 ^ D * (3 ^ h.s3) ^ h.p n := by
      simp [firstScale, Dindex, pow_add, pow_mul]
    _ ≡ 3 ^ D * 1 ^ h.p n [MOD modulus C] :=
      (h.period3.pow (h.p n)).mul_left _
    _ = firstScale D := by simp [firstScale]

lemma DiagonalExponentApproximation.secondScale_modEq
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) :
    Nat.ModEq (modulus C) (secondScale (h.Rindex n)) (secondScale R) := by
  calc
    secondScale (h.Rindex n) = 5 ^ R * (5 ^ h.s5) ^ h.q n := by
      simp [secondScale, Rindex, pow_add, pow_mul]
    _ ≡ 5 ^ R * 1 ^ h.q n [MOD modulus C] :=
      (h.period5.pow (h.q n)).mul_left _
    _ = secondScale R := by simp [secondScale]

lemma DiagonalExponentApproximation.residue_eq
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t)
    (n : ℕ) : residue C (h.Dindex n) (h.Rindex n) = residue C D R := by
  apply Nat.ModEq.eq_of_lt_of_lt _ (residue_lt _ _ _) (residue_lt _ _ _)
  rw [← ZMod.natCast_eq_natCast_iff]
  have hfirst : (firstScale (h.Dindex n) : ZMod (modulus C)) =
      firstScale D :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.firstScale_modEq n)
  have hsecond : (secondScale (h.Rindex n) : ZMod (modulus C)) =
      secondScale R :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.secondScale_modEq n)
  have hunit : IsUnit (firstScale D : ZMod (modulus C)) :=
    (ZMod.isUnit_iff_coprime _ _).2 (firstScale_coprime_modulus C D)
  apply hunit.mul_left_cancel
  calc
    (firstScale D : ZMod (modulus C)) *
        residue C (h.Dindex n) (h.Rindex n) =
        (firstScale (h.Dindex n) : ZMod (modulus C)) *
          residue C (h.Dindex n) (h.Rindex n) := by rw [hfirst]
    _ = secondScale (h.Rindex n) := residue_spec_zmod _ _ _
    _ = secondScale R := hsecond
    _ = (firstScale D : ZMod (modulus C)) * residue C D R :=
      (residue_spec_zmod C D R).symm

/-- The irrational-rotation existence statement used for equation (10). -/
def HasDiagonalExponentData : Prop :=
  ∀ (C D R : ℕ) (t : ℝ),
    Nonempty (DiagonalExponentApproximation C D R t)

/-- Irrational rotation supplies all exponent sequences in equation (10). -/
theorem hasDiagonalExponentData : HasDiagonalExponentData := by
  intro C D R t
  let s := periodExponent C
  have hs : 0 < s := periodExponent_pos C
  have hA : 0 < (s : ℝ) * Real.log 3 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  have hB : 0 < (s : ℝ) * Real.log 5 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  obtain ⟨p, q, hlim⟩ := exists_nonnegative_irrational_approximation hA hB
    (irrational_scaled_logs s s hs hs) t
  refine ⟨{
    s3 := s
    s5 := s
    s3_pos := hs
    s5_pos := hs
    period3 := three_pow_periodExponent_modEq C
    period5 := five_pow_periodExponent_modEq C
    p := p
    q := q
    log_tendsto := ?_ }⟩
  convert hlim using 1
  funext n
  push_cast
  ring

/-- The algebraic and continuity calculation turning equation (10) into
convergence of normalized lattice shapes. -/
def DiagonalExponentDataIsSound : Prop :=
  ∀ (C D R : ℕ) (t : ℝ) (h : DiagonalExponentApproximation C D R t),
    Tendsto
      (fun n ↦ lambdaShape C (h.Dindex n) (h.Rindex n)) atTop
      (𝓝 (diagonalFlow t • lambdaShape C D R))

lemma DiagonalExponentApproximation.aspectLog_tendsto
    {C D R : ℕ} {t : ℝ} (h : DiagonalExponentApproximation C D R t) :
    Tendsto (fun n ↦ aspectLog C (h.Dindex n) (h.Rindex n)) atTop
      (nhds (aspectLog C D R + t)) := by
  have ht := h.log_tendsto.const_add (aspectLog C D R)
  convert ht using 1
  funext n
  rw [aspectLog_eq, aspectLog_eq]
  dsimp [Dindex, Rindex]
  push_cast
  ring

/-- The algebraic/continuity content of equation (10). -/
theorem diagonalExponentData_isSound : DiagonalExponentDataIsSound := by
  intro C D R t h
  have ht := (continuous_timeShape C (residue C D R)).continuousAt.tendsto.comp
    h.aspectLog_tendsto
  convert ht using 1
  · funext n
    rw [lambdaShape_eq_timeMatrix, h.residue_eq]
    rfl
  · apply congrArg nhds
    rw [lambdaShape_eq_timeMatrix, timeMatrix_add]
    rfl

/-- The exponent data in equation (12) for a mesh point `f/(7 * 2^C)`. -/
structure HorosphereExponentApproximation (C f : ℕ)
    (hf : f ∈ residueMesh C) where
  rf : ℕ
  s3 : ℕ
  s5 : ℕ
  residue_power : Nat.ModEq (modulus C) (5 ^ rf) f
  s3_pos : 0 < s3
  s5_pos : 0 < s5
  period3 : Nat.ModEq (modulus C) (3 ^ s3) 1
  period5 : Nat.ModEq (modulus C) (5 ^ s5) 1
  p : ℕ → ℕ
  q : ℕ → ℕ
  log_tendsto : Tendsto
    (fun n ↦ (rf : ℝ) * Real.log 5 +
      ((q n * s5 : ℕ) : ℝ) * Real.log 5 -
      ((p n * s3 : ℕ) : ℝ) * Real.log 3 - Real.log (modulus C))
    atTop (𝓝 0)

def HorosphereExponentApproximation.Dindex
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) : ℕ :=
  h.s3 * h.p n

def HorosphereExponentApproximation.Rindex
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) : ℕ :=
  h.rf + h.s5 * h.q n

lemma HorosphereExponentApproximation.firstScale_modEq
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) :
    Nat.ModEq (modulus C) (firstScale (h.Dindex n)) 1 := by
  calc
    firstScale (h.Dindex n) = (3 ^ h.s3) ^ h.p n := by
      simp [firstScale, Dindex, pow_mul]
    _ ≡ 1 ^ h.p n [MOD modulus C] := h.period3.pow (h.p n)
    _ = 1 := one_pow _

lemma HorosphereExponentApproximation.secondScale_modEq
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) :
    Nat.ModEq (modulus C) (secondScale (h.Rindex n)) f := by
  calc
    secondScale (h.Rindex n) = 5 ^ h.rf * (5 ^ h.s5) ^ h.q n := by
      simp [secondScale, Rindex, pow_add, pow_mul]
    _ ≡ f * 1 ^ h.q n [MOD modulus C] :=
      h.residue_power.mul (h.period5.pow (h.q n))
    _ = f := by simp

lemma HorosphereExponentApproximation.residue_eq
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) (n : ℕ) :
    residue C (h.Dindex n) (h.Rindex n) = f := by
  apply Nat.ModEq.eq_of_lt_of_lt _ (residue_lt _ _ _) hf.1
  rw [← ZMod.natCast_eq_natCast_iff]
  calc
    (residue C (h.Dindex n) (h.Rindex n) : ZMod (modulus C)) =
        (firstScale (h.Dindex n) : ZMod (modulus C)) *
          residue C (h.Dindex n) (h.Rindex n) := by
            rw [(ZMod.natCast_eq_natCast_iff _ _ _).2
              (h.firstScale_modEq n)]
            simp
    _ = secondScale (h.Rindex n) := residue_spec_zmod _ _ _
    _ = f :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.secondScale_modEq n)

/-- Irrational rotation supplies the positive exponent sequences in (12). -/
def HasHorosphereExponentData : Prop :=
  ∀ (C f : ℕ) (hf : f ∈ residueMesh C),
    Nonempty (HorosphereExponentApproximation C f hf)

/-- Irrational rotation also supplies the corrected exponent sequences in
equation (12). -/
theorem hasHorosphereExponentData : HasHorosphereExponentData := by
  intro C f hf
  rcases hf.2 with ⟨rf, hrf⟩
  let s := periodExponent C
  have hs : 0 < s := periodExponent_pos C
  have hA : 0 < (s : ℝ) * Real.log 3 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  have hB : 0 < (s : ℝ) * Real.log 5 :=
    mul_pos (Nat.cast_pos.mpr hs) (Real.log_pos (by norm_num))
  let target := (rf : ℝ) * Real.log 5 - Real.log (modulus C)
  obtain ⟨p, q, hlim⟩ := exists_nonnegative_irrational_approximation hA hB
    (irrational_scaled_logs s s hs hs) target
  refine ⟨{
    rf := rf
    s3 := s
    s5 := s
    residue_power := hrf
    s3_pos := hs
    s5_pos := hs
    period3 := three_pow_periodExponent_modEq C
    period5 := five_pow_periodExponent_modEq C
    p := p
    q := q
    log_tendsto := ?_ }⟩
  have ht := hlim.neg.const_add target
  convert ht using 1
  · funext n
    dsimp [target]
    push_cast
    ring
  · dsimp [target]
    ring

/-- The corrected algebraic conclusion of equation (12).  Our index `C` is
the paper's `c-4`, so the sequence here represents
`Λ_{C+4,D_n+2,R_n+1}` rather than the misindexed printed expression. -/
def HorosphereExponentDataIsSound : Prop :=
  ∀ (C f : ℕ) (hf : f ∈ residueMesh C)
      (h : HorosphereExponentApproximation C f hf),
    Tendsto
      (fun n ↦ lambdaShape C (h.Dindex n) (h.Rindex n)) atTop
      (𝓝 (horocycle ((f : ℝ) / modulus C) • squareShape))

lemma HorosphereExponentApproximation.aspectLog_tendsto
    {C f : ℕ} {hf : f ∈ residueMesh C}
    (h : HorosphereExponentApproximation C f hf) :
    Tendsto (fun n ↦ aspectLog C (h.Dindex n) (h.Rindex n)) atTop
      (nhds 0) := by
  have ht := h.log_tendsto.neg
  convert ht using 1
  · funext n
    rw [aspectLog_eq]
    dsimp [Dindex, Rindex]
    push_cast
    ring
  · simp

/-- The algebraic/continuity content of equation (12). -/
theorem horosphereExponentData_isSound : HorosphereExponentDataIsSound := by
  intro C f hf h
  have ht := (continuous_timeShape C f).continuousAt.tendsto.comp
    h.aspectLog_tendsto
  convert ht using 1
  · funext n
    rw [lambdaShape_eq_timeMatrix, h.residue_eq]
    rfl
  · apply congrArg nhds
    rw [timeMatrix_zero]
    simp [squareShape]

def HasDiagonalShapeSequences : Prop :=
  ∀ (C D R : ℕ) (t : ℝ), ∃ Dn Rn : ℕ → ℕ,
    Tendsto (fun n ↦ lambdaShape C (Dn n) (Rn n)) atTop
      (𝓝 (diagonalFlow t • lambdaShape C D R))

def HasHorosphereMeshSequences : Prop :=
  ∀ (C f : ℕ), f ∈ residueMesh C → ∃ Dn Rn : ℕ → ℕ,
    Tendsto (fun n ↦ lambdaShape C (Dn n) (Rn n)) atTop
      (𝓝 (horocycle ((f : ℝ) / modulus C) • squareShape))

theorem hasDiagonalShapeSequences_of_exponent_data
    (hexists : HasDiagonalExponentData)
    (hsound : DiagonalExponentDataIsSound) :
    HasDiagonalShapeSequences := by
  intro C D R t
  let h := (hexists C D R t).some
  exact ⟨h.Dindex, h.Rindex, hsound C D R t h⟩

theorem hasHorosphereMeshSequences_of_exponent_data
    (hexists : HasHorosphereExponentData)
    (hsound : HorosphereExponentDataIsSound) :
    HasHorosphereMeshSequences := by
  intro C f hf
  let h := (hexists C f hf).some
  exact ⟨h.Dindex, h.Rindex, hsound C f hf h⟩

/-- The bounded-gap assertion about `S_C/(7 * 2^C)`.  In the paper this is
proved from
`S_C = {56k+j | j ∈ {1,5,9,13,25,45}}`, whose gaps are at most `20`. -/
def MeshApproximatesUnitInterval : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ Cn fn : ℕ → ℕ,
    (∀ n, fn n ∈ residueMesh (Cn n)) ∧
    Tendsto (fun n ↦ ((fn n : ℕ) : ℝ) / modulus (Cn n)) atTop (𝓝 s)

/-- The required residue mesh is dense.  It is enough to use powers `5^R`
before reduction: irrationality of `log 5 / log 2` makes
`5^R / (7 * 2^C)` approach every point of `[0,1]` from below. -/
theorem meshApproximatesUnitInterval : MeshApproximatesUnitInterval := by
  intro s hs
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
      have hn := hpq n
      rw [abs_lt] at hn ⊢
      constructor <;> linarith
    have hdelta : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop
        (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
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

lemma lambdaShape_mem_lambdaShapes (C D R : ℕ) :
    lambdaShape C D R ∈ lambdaShapes := by
  exact ⟨(C, D, R), rfl⟩

lemma diagonal_generator_mem_omega (h : HasDiagonalShapeSequences)
    (C D R : ℕ) (t : ℝ) :
    diagonalFlow t • lambdaShape C D R ∈ omega := by
  rcases h C D R t with ⟨Dn, Rn, hn⟩
  exact IsClosed.mem_of_tendsto isClosed_closure hn
    (Filter.Eventually.of_forall fun n ↦
      subset_closure (lambdaShape_mem_lambdaShapes C (Dn n) (Rn n)))

lemma horosphere_mesh_point_mem_omega (h : HasHorosphereMeshSequences)
    (C f : ℕ) (hf : f ∈ residueMesh C) :
    horocycle ((f : ℝ) / modulus C) • squareShape ∈ omega := by
  rcases h C f hf with ⟨Dn, Rn, hn⟩
  exact IsClosed.mem_of_tendsto isClosed_closure hn
    (Filter.Eventually.of_forall fun n ↦
      subset_closure (lambdaShape_mem_lambdaShapes C (Dn n) (Rn n)))

lemma continuous_horocycle_square :
    Continuous (fun s : ℝ ↦ horocycle s • squareShape) := by
  have hh : Continuous horocycle := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_matrix fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  exact continuous_smul.comp (hh.prodMk continuous_const)

/-- The approximation statement proved on the generators in the diagonal
part of Proposition 5.2. -/
def DiagonalGeneratorApproximation : Prop :=
  ∀ t : ℝ, ∀ C D R : ℕ,
    diagonalFlow t • lambdaShape C D R ∈ omega

/-- The conclusion of the residue-mesh argument in the horospherical part. -/
def ContainsHorosphericalPiece : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, horocycle s • squareShape ∈ omega

lemma diagonalGeneratorApproximation_of_shape_sequences
    (h : HasDiagonalShapeSequences) :
    DiagonalGeneratorApproximation := by
  intro t C D R
  exact diagonal_generator_mem_omega h C D R t

lemma containsHorosphericalPiece_of_mesh
    (hseq : HasHorosphereMeshSequences)
    (hmesh : MeshApproximatesUnitInterval) :
    ContainsHorosphericalPiece := by
  intro s hs
  rcases hmesh s hs with ⟨Cn, fn, hfn, hlim⟩
  apply IsClosed.mem_of_tendsto isClosed_closure
    (continuous_horocycle_square.continuousAt.tendsto.comp hlim)
  exact Filter.Eventually.of_forall fun n ↦
    horosphere_mesh_point_mem_omega hseq (Cn n) (fn n) (hfn n)

/-- The expanding half-horocycle appearing in Margulis' banana argument. -/
def bananaSet : Set ShapeSpace :=
  {x | ∃ t ∈ Set.Ici (0 : ℝ), ∃ s ∈ Set.Icc (0 : ℝ) 1,
    x = ((diagonalFlow t * horocycle s : SL2R) : ShapeSpace)}

/-- Margulis' banana trick, equivalently the expanding-horocycle input used
in the proof of Proposition 5.2.  Its elementary proof is isolated in
`BananaLemma.lean`. -/
theorem banana_dense : Dense bananaSet := by
  change Dense SL2Banana.bananaExpandingStrip
  exact SL2Banana.banana_expanding_horocycle_dense

/-- Closed-subset form of the banana trick.  Unlike `banana_dense`, this is a
formal consequence and needs no additional dynamical input. -/
theorem banana_lemma (Ω : Set ShapeSpace)
    (hΩ : IsClosed Ω)
    (hdiag : ∀ t : ℝ, Set.MapsTo (diagonalFlow t • ·) Ω Ω)
    (hhoro : ∀ s ∈ Set.Icc (0 : ℝ) 1, horocycle s • squareShape ∈ Ω) :
    Ω = Set.univ := by
  have hbanana : bananaSet ⊆ Ω := by
    rintro x ⟨t, ht, s, hs, rfl⟩
    have hu := hhoro s hs
    have ha := hdiag t hu
    simpa [squareShape, mul_smul] using ha
  have hdense : Dense Ω := Dense.mono hbanana banana_dense
  calc
    Ω = closure Ω := hΩ.closure_eq.symm
    _ = Set.univ := dense_iff_closure_eq.mp hdense

lemma diagonal_mapsTo_omega (h : DiagonalGeneratorApproximation) :
    ∀ t : ℝ, Set.MapsTo (diagonalFlow t • ·) omega omega := by
  intro t
  have hpreclosed : IsClosed ((diagonalFlow t • ·) ⁻¹' omega) :=
    isClosed_closure.preimage (continuous_const_smul (diagonalFlow t))
  have hgenerators : lambdaShapes ⊆ (diagonalFlow t • ·) ⁻¹' omega := by
    rintro _ ⟨⟨C, D, R⟩, rfl⟩
    exact h t C D R
  exact closure_minimal hgenerators hpreclosed

/-- Proposition 5.2 follows from its two approximation steps and the
banana lemma. -/
theorem proposition_5_2
    (hdiag : DiagonalGeneratorApproximation)
    (hhoro : ContainsHorosphericalPiece) :
    Dense lambdaShapes := by
  rw [dense_iff_closure_eq]
  exact banana_lemma omega isClosed_closure
    (diagonal_mapsTo_omega hdiag) hhoro

/-- All elementary arithmetic/limit obligations in the proof of Proposition
5.2, kept separate from the dynamical banana lemma. -/
structure ApproximationData where
  diagonalExponentData : HasDiagonalExponentData
  horosphereExponentData : HasHorosphereExponentData
  mesh : MeshApproximatesUnitInterval

/-- The complete, sorry-free elementary approximation package in
Proposition 5.2. -/
def approximationData : ApproximationData where
  diagonalExponentData := hasDiagonalExponentData
  horosphereExponentData := hasHorosphereExponentData
  mesh := meshApproximatesUnitInterval

theorem ApproximationData.auxiliary_shapes_dense
    (h : ApproximationData) : Dense lambdaShapes := by
  have hdiagSeq := hasDiagonalShapeSequences_of_exponent_data
    h.diagonalExponentData diagonalExponentData_isSound
  have hhoroSeq := hasHorosphereMeshSequences_of_exponent_data
    h.horosphereExponentData horosphereExponentData_isSound
  exact proposition_5_2
    (diagonalGeneratorApproximation_of_shape_sequences hdiagSeq)
    (containsHorosphericalPiece_of_mesh hhoroSeq h.mesh)

end Proposition52

/-! ### Proposition 4.4 in the shifted coordinates of Lemma 5.1 -/

namespace ABCLocalUnits

open ABCOrders ArithmeticConstruction

lemma exponentConditions_shifted_eq_exponentLattice (C D R : ℕ) :
    SuborderUnits.ExponentConditions (C + 4) (D + 2) (R + 1) =
      Proposition52.exponentLattice C D R := by
  ext mn
  rcases mn with ⟨m, n⟩
  simp only [SuborderUnits.ExponentConditions,
    Proposition52.exponentLattice, Set.mem_setOf_eq]
  have hC : C + 4 - 1 = C + 3 := by omega
  have hD : D + 2 - 1 = D + 1 := by omega
  have hR : R + 1 - 1 = R := by omega
  rw [hC, hD, hR]

/-- Proposition 4.4 in precisely the shifted lattice notation used by
Lemma 5.1 and the final density argument. -/
theorem canonical_product_mem_iff_exponentLattice
    (P : Parameters) (C D R : ℕ)
    (hlocal : SatisfiesLocalConditions (C + 4) (D + 2) (R + 1)
      P.a₁ P.a₂)
    (m n : ℤ) :
    ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
        (orderCarrier P)ˣ) : orderCarrier P) ∈
        scalarSuborder P
          (2 ^ (C + 4) * 3 ^ (D + 2) * 5 ^ (R + 1))) ↔
      (m, n) ∈ Proposition52.exponentLattice C D R := by
  rw [canonical_product_mem_iff_exponentConditions P
    (C + 4) (D + 2) (R + 1) (by omega) (by omega) (by omega) hlocal]
  exact Set.ext_iff.mp (exponentConditions_shifted_eq_exponentLattice C D R)
    (m, n)

/-- Full Proposition 4.4 in the shifted notation of Lemma 5.1: this is the
classification of all ambient order units lying in the scalar suborder. -/
theorem unit_mem_scalarSuborder_iff_exists_sign_exponentLattice
    (P : Parameters) (C D R : ℕ)
    (hfund : (cubicOrder P).IsFundamentalFamily (candidateUnitFamily P))
    (hlocal : SatisfiesLocalConditions (C + 4) (D + 2) (R + 1)
      P.a₁ P.a₂)
    (x : (orderCarrier P)ˣ) :
    ((x : orderCarrier P) ∈ scalarSuborder P
        (2 ^ (C + 4) * 3 ^ (D + 2) * 5 ^ (R + 1))) ↔
      ∃ ε : (orderCarrier P)ˣ, (ε = 1 ∨ ε = -1) ∧
        ∃ m n : ℤ, (m, n) ∈ Proposition52.exponentLattice C D R ∧
          x = ε * (alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n := by
  rw [unit_mem_scalarSuborder_iff_exists_sign_exponents P
    (C + 4) (D + 2) (R + 1) (by omega) (by omega) (by omega)
    hfund hlocal]
  constructor
  · rintro ⟨ε, hε, m, n, hmn, hx⟩
    exact ⟨ε, hε, m, n,
      (Set.ext_iff.mp (exponentConditions_shifted_eq_exponentLattice C D R)
        (m, n)).mp hmn, hx⟩
  · rintro ⟨ε, hε, m, n, hmn, hx⟩
    exact ⟨ε, hε, m, n,
      (Set.ext_iff.mp (exponentConditions_shifted_eq_exponentLattice C D R)
        (m, n)).mpr hmn, hx⟩

end ABCLocalUnits

/-! ### Sections 2--5: the scalar-order period matrix -/

namespace ABCRealization

open ABCOrders ArithmeticConstruction ABCBoundedFrames ABCMovingFrames
open Proposition52

/-- The conductor used for the scalar suborder in Proposition 4.4. -/
def conductor (C D R : ℕ) : ℕ :=
  2 ^ (C + 4) * 3 ^ (D + 2) * 5 ^ (R + 1)

lemma unitLog_sign (P : Parameters) (ε : (orderCarrier P)ˣ)
    (hε : ε = 1 ∨ ε = -1) :
    OrderPeriods.unitLog (orderEmbedding P) ε = 0 := by
  rcases hε with rfl | rfl
  · funext i
    fin_cases i <;> simp [OrderPeriods.unitLog]
  · funext i
    fin_cases i <;> simp [OrderPeriods.unitLog]

/-- The real matrix in Lemma 5.1 is the scalar extension of its integral
exponent-basis matrix. -/
lemma exponentBasis_cast_eq (C D R : ℕ) :
    (exponentBasis C D R).map (Int.castRingHom ℝ) =
      exponentChangeReal * lambdaBasis C D R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentBasis_apply, exponentChangeReal, lambdaBasis,
      Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring

lemma cast_exponentBasis_mulVec (C D R : ℕ) (z : Fin 2 → ℤ) :
    (fun i ↦ (((exponentBasis C D R).mulVec z i : ℤ) : ℝ)) =
      (exponentChangeReal * lambdaBasis C D R).mulVec
        (fun i ↦ (z i : ℝ)) := by
  rw [← exponentBasis_cast_eq]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The period matrix obtained successively from Proposition 3.4,
Proposition 4.4, and Lemma 5.1. -/
def periodMatrix (N C D R : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  unitLogBasis N * exponentChangeReal * lambdaBasis C D R

lemma periodMatrix_det_pos (N C D R : ℕ) :
    0 < (periodMatrix N C D R).det := by
  simp only [periodMatrix, Matrix.det_mul]
  exact mul_pos (mul_pos (unitLogBasis_det_pos N)
    exponentChangeReal_det_pos) (lambdaBasis_det_pos C D R)

lemma periodMatrix_mulVec (N C D R : ℕ) (z : Fin 2 → ℤ) :
    (periodMatrix N C D R).mulVec (fun i ↦ (z i : ℝ)) =
      (unitLogBasis N).mulVec
        (fun i ↦ (((exponentBasis C D R).mulVec z i : ℤ) : ℝ)) := by
  rw [periodMatrix, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← cast_exponentBasis_mulVec]

/-- Propositions 3.4 and 4.4, followed by Lemma 5.1, identify the complete
logarithmic unit lattice of the scalar order with the columns of
`periodMatrix`. -/
lemma unitLogs_iff_periodMatrix (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) (u : Fin 2 → ℝ) :
    (∃ x : (scalarSuborder (parameters N) (conductor C D R))ˣ,
        u = OrderPeriods.unitLog
          (scalarSuborderEmbedding (parameters N) (conductor C D R)) x) ↔
      ∃ z : Fin 2 → ℤ,
        u = (periodMatrix N C D R).mulVec (fun i ↦ (z i : ℝ)) := by
  let P := parameters N
  let q := conductor C D R
  constructor
  · rintro ⟨x, rfl⟩
    have hxmem :
        (((ABCScalarUnits.ambientUnitMap P q x : (orderCarrier P)ˣ) :
          orderCarrier P) ∈ scalarSuborder P q) :=
      ABCScalarUnits.ambientUnitMap_value_mem P q x
    have hclass :=
      (ABCLocalUnits.unit_mem_scalarSuborder_iff_exists_sign_exponentLattice
        P C D R hfund hlocal (ABCScalarUnits.ambientUnitMap P q x)).mp hxmem
    obtain ⟨ε, hε, m, n, hmn, hx⟩ := hclass
    rw [exponentLattice_eq_range_exponentBasis] at hmn
    obtain ⟨z, hz⟩ := hmn
    refine ⟨z, ?_⟩
    have hm : m = (exponentBasis C D R).mulVec z 0 :=
      (congrArg Prod.fst hz).symm
    have hn : n = (exponentBasis C D R).mulVec z 1 :=
      (congrArg Prod.snd hz).symm
    dsimp only [P, q] at *
    rw [ABCScalarUnits.unitLog_ambientUnitMap, hx,
      ABCUnitLogs.unitLog_mul, ABCUnitLogs.unitLog_mul,
      unitLog_sign (parameters N) ε hε, zero_add]
    rw [← ABCUnitLogs.unitLog_mul,
      ABCUnitLogs.unitLog_canonical_product_eq_mulVec,
      periodMatrix_mulVec]
    congr 1
    funext i
    fin_cases i
    · simpa [hm]
    · simpa [hn]
  · rintro ⟨z, rfl⟩
    let m : ℤ := (exponentBasis C D R).mulVec z 0
    let n : ℤ := (exponentBasis C D R).mulVec z 1
    have hmn : (m, n) ∈ exponentLattice C D R := by
      rw [exponentLattice_eq_range_exponentBasis]
      exact ⟨z, rfl⟩
    have hmem :
        ((((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n :
            (orderCarrier P)ˣ) : orderCarrier P) ∈ scalarSuborder P q) :=
      (ABCLocalUnits.canonical_product_mem_iff_exponentLattice
        P C D R hlocal m n).mpr hmn
    let x : (scalarSuborder P q)ˣ := ABCScalarUnits.restrictUnit P q
      ((alphaUnit P) ^ m * (alphaSubOneUnit P) ^ n) hmem
    refine ⟨x, ?_⟩
    rw [ABCScalarUnits.unitLog_restrictUnit,
      ABCUnitLogs.unitLog_canonical_product_eq_mulVec,
      periodMatrix_mulVec]
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Lemma 2.6 applied to the scalar ABC order. -/
theorem normalized_periodMatrix_mem (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    (normalizeBasis (periodMatrix N C D R)
      (periodMatrix_det_pos N C D R) : ShapeSpace) ∈
        periodicTorusShapes := by
  let q := conductor C D R
  have hq : q ≠ 0 := by
    simp [q, conductor]
  apply OrderPeriods.normalized_unit_log_shape_mem_periodicTorusShapes
    (scalarSuborderBasis (parameters N) q hq)
    (scalarSuborderEmbedding (parameters N) q)
    (ABCScalarUnits.scalarSuborderBasis_zero (parameters N) q hq)
    (ABCScalarUnits.scalarSuborderEmbedding_zero_injective (parameters N) q)
    (scalarSuborderEmbeddingMatrix_det_ne_zero (parameters N) q hq)
    (periodMatrix N C D R) (periodMatrix_det_pos N C D R)
  exact unitLogs_iff_periodMatrix N C D R hfund hlocal

lemma normalized_periodMatrix_eq_movingFrame_smul
    (N C D R : ℕ) :
    (normalizeBasis (periodMatrix N C D R)
        (periodMatrix_det_pos N C D R) : ShapeSpace) =
      movingFrame N • lambdaShape C D R := by
  have hUE : 0 < (unitLogBasis N * exponentChangeReal).det := by
    simpa only [Matrix.det_mul] using
      mul_pos (unitLogBasis_det_pos N) exponentChangeReal_det_pos
  change
    (normalizeBasis
      ((unitLogBasis N * exponentChangeReal) * lambdaBasis C D R)
      _ : ShapeSpace) = movingFrame N • lambdaShape C D R
  rw [normalizeBasis_mul (unitLogBasis N * exponentChangeReal)
    (lambdaBasis C D R) hUE (lambdaBasis_det_pos C D R)]
  rw [normalize_unitLog_mul_change]
  rfl

/-- The paper's realization statement, assuming the output of Proposition
3.4 and the local congruences entering Proposition 4.4. -/
theorem realizes_of_fundamental (N C D R : ℕ)
    (hfund : (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)))
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    movingFrame N • lambdaShape C D R ∈ periodicTorusShapes := by
  rw [← normalized_periodMatrix_eq_movingFrame_smul]
  exact normalized_periodMatrix_mem N C D R hfund hlocal

/-- For the CRT family, Proposition 3.4 follows from Cusick's regulator
inequality once `N ≥ 1`; hence the realization requires only the local
conditions. -/
theorem realizes (N C D R : ℕ) (hN : 1 ≤ N)
    (hlocal : ABCLocalUnits.SatisfiesLocalConditions
      (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂) :
    movingFrame N • lambdaShape C D R ∈ periodicTorusShapes := by
  have hlogs := parameters_logs_gt_ten N hN
  have hfund :=
    ABCOrders.FundamentalUnits.candidateUnitFamily_isFundamental_of_large
      (P := parameters N) hlogs.1 hlogs.2
  exact realizes_of_fundamental N C D R hfund hlocal

end ABCRealization

open Filter Set Topology
open Proposition52

/-! ### The final moving-frame argument in Section 5.3 -/


/-- The exact output needed from Sections 2--4 and the beginning of Section
5.3.  `level n` is the CRT level of the selected ABC order, `frame n` is the
determinant-one normalization of the paper's `g_N g`, and `realizes` is the
period/unit correspondence of Lemma 2.6 combined with Proposition 4.4 and
Lemma 5.1. -/
structure ArithmeticRealization where
  level : ℕ → ℕ
  a₁ : ℕ → ℕ
  a₂ : ℕ → ℕ
  parameters_ordered : ∀ n, 3 ≤ a₁ n ∧ a₁ n < a₂ n
  localConditions : ∀ n, SatisfiesLocalConditions (level n) (a₁ n) (a₂ n)
  separation_tendsto :
    Tendsto (fun n ↦ min (a₁ n) (a₂ n - a₁ n)) atTop atTop
  frame : ℕ → SL2R
  limitFrame : SL2R
  level_ge : ∀ n, n ≤ level n
  frame_tendsto : Tendsto frame atTop (𝓝 limitFrame)
  realizes : ∀ n C D R,
    C + 4 ≤ level n → D + 2 ≤ level n → R + 1 ≤ level n →
      frame n • lambdaShape C D R ∈ periodicTorusShapes

namespace PaperArithmetic

open ABCOrders ABCBoundedFrames ABCMovingFrames

/-- CRT congruences imposed at level `N+1` descend to the three (possibly
different) conductor exponents used in Proposition 4.4. -/
lemma localConditions_to_abc
    (N C D R : ℕ)
    (hlocal : SatisfiesLocalConditions (N + 1)
      (localAOne (N + 1)) (localATwo (N + 1)))
    (hC : C + 4 ≤ N + 1) (hD : D + 2 ≤ N + 1)
    (hR : R + 1 ≤ N + 1) :
    ABCLocalUnits.SatisfiesLocalConditions (C + 4) (D + 2) (R + 1)
      (parameters N).a₁ (parameters N).a₂ := by
  rcases hlocal with ⟨h21, h22, h31, h32, h51, h52⟩
  have hd2 : 2 ^ (C + 4) ∣ 2 ^ (N + 1) := pow_dvd_pow 2 hC
  have hd3 : 3 ^ (D + 2) ∣ 3 ^ (N + 1) := pow_dvd_pow 3 hD
  have hd5 : 5 ^ (R + 1) ∣ 5 ^ (N + 1) := pow_dvd_pow 5 hR
  change
    ((localAOne (N + 1) : ℤ) ≡ 0 [ZMOD (2 : ℤ) ^ (C + 4)]) ∧
    ((localATwo (N + 1) : ℤ) ≡ 1 [ZMOD (2 : ℤ) ^ (C + 4)]) ∧
    ((localAOne (N + 1) : ℤ) ≡ 1 [ZMOD (3 : ℤ) ^ (D + 2)]) ∧
    ((localATwo (N + 1) : ℤ) ≡ 0 [ZMOD (3 : ℤ) ^ (D + 2)]) ∧
    ((localAOne (N + 1) : ℤ) ≡ 1 [ZMOD (5 : ℤ) ^ (R + 1)]) ∧
    ((localATwo (N + 1) : ℤ) ≡ 1 [ZMOD (5 : ℤ) ^ (R + 1)])
  constructor
  · exact_mod_cast h21.of_dvd hd2
  constructor
  · exact_mod_cast h22.of_dvd hd2
  constructor
  · exact_mod_cast h31.of_dvd hd3
  constructor
  · exact_mod_cast h32.of_dvd hd3
  constructor
  · exact_mod_cast h51.of_dvd hd5
  · exact_mod_cast h52.of_dvd hd5

/-- Existence of the arithmetic realization obtained exactly as in the last
paragraph of the paper: choose a compactness subsequence of `g_N g`, discard
its first term to enter the Proposition 3.4 threshold, and retain the same
subsequence for every auxiliary lattice. -/
theorem arithmeticRealization_nonempty : Nonempty ArithmeticRealization := by
  obtain ⟨limitFrame, subseq, hsubseq, hframe⟩ :=
    exists_movingFrame_convergent_subsequence
  let selected : ℕ → ℕ := fun n ↦ subseq (n + 1)
  have hselected_strict : StrictMono selected := by
    intro m n hmn
    exact hsubseq (Nat.add_lt_add_right hmn 1)
  have hselected_one : ∀ n, 1 ≤ selected n := by
    intro n
    have hle : n + 1 ≤ subseq (n + 1) := hsubseq.id_le (n + 1)
    exact (Nat.le_add_left 1 n).trans hle
  let level : ℕ → ℕ := fun n ↦ selected n + 1
  have hlevel_strict : StrictMono level := by
    intro m n hmn
    exact Nat.add_lt_add_right (hselected_strict hmn) 1
  have hlevel_tendsto : Tendsto level atTop atTop :=
    hlevel_strict.tendsto_atTop
  have hframe_shifted :
      Tendsto (fun n ↦ movingFrame (selected n)) atTop
        (𝓝 limitFrame) := by
    change Tendsto (fun n ↦ (movingFrame ∘ subseq) (n + 1)) atTop
      (𝓝 limitFrame)
    exact (Filter.tendsto_add_atTop_iff_nat 1).2 hframe
  exact ⟨{
    level := level
    a₁ := fun n ↦ localAOne (level n)
    a₂ := fun n ↦ localATwo (level n)
    parameters_ordered := by
      intro n
      change 3 ≤ localAOne (selected n + 1) ∧
        localAOne (selected n + 1) < localATwo (selected n + 1)
      exact local_parameters_ordered (selected n)
    localConditions := by
      intro n
      exact local_conditions (level n)
    separation_tendsto := by
      exact local_separation_tendsto.comp hlevel_tendsto
    frame := fun n ↦ movingFrame (selected n)
    limitFrame := limitFrame
    level_ge := by
      intro n
      have hle : n + 1 ≤ selected n := hsubseq.id_le (n + 1)
      change n ≤ selected n + 1
      omega
    frame_tendsto := hframe_shifted
    realizes := by
      intro n C D R hC hD hR
      apply ABCRealization.realizes (selected n) C D R (hselected_one n)
      exact localConditions_to_abc (selected n) C D R
        (local_conditions (selected n + 1)) hC hD hR
  }⟩

/-- A chosen realization from the paper's compactness argument. -/
noncomputable def arithmeticRealization : ArithmeticRealization :=
  Classical.choice arithmeticRealization_nonempty

end PaperArithmetic

/-- Every fixed auxiliary shape, moved by the limiting frame, is a limit of
actual periodic-torus shapes. -/
lemma ArithmeticRealization.transformed_mem_closure
    (h : ArithmeticRealization) (C D R : ℕ) :
    h.limitFrame • lambdaShape C D R ∈ closure periodicTorusShapes := by
  let N := max (C + 4) (max (D + 2) (R + 1))
  let f : ℕ → ShapeSpace := fun n => h.frame n • lambdaShape C D R
  have hf : Tendsto f atTop
      (𝓝 (h.limitFrame • lambdaShape C D R)) := by
    exact h.frame_tendsto.smul tendsto_const_nhds
  apply mem_closure_of_tendsto hf
  filter_upwards [eventually_ge_atTop N] with n hn
  apply h.realizes n C D R
  · exact (le_max_left _ _).trans (hn.trans (h.level_ge n))
  · exact le_trans (le_max_of_le_right (le_max_left _ _))
      (hn.trans (h.level_ge n))
  · exact le_trans (le_max_of_le_right (le_max_right _ _))
      (hn.trans (h.level_ge n))

lemma transformed_lambdaShapes_dense (h : Dense lambdaShapes)
    (g : SL2R) :
    Dense ((fun x : ShapeSpace => g • x) '' lambdaShapes) := by
  have hsurj : Function.Surjective (fun x : ShapeSpace => g • x) :=
    (MulAction.toPerm g).surjective
  exact hsurj.denseRange.dense_image (continuous_const_smul g) h

/-- This is the exhaustion/diagonal argument in the final paragraph of the
proof of Theorem 1.1. -/
theorem density_from_arithmetic_realization
    (haux : Dense lambdaShapes) (h : ArithmeticRealization) :
    Dense periodicTorusShapes := by
  have hclosure : Dense (closure periodicTorusShapes) := by
    apply Dense.mono ?_ (transformed_lambdaShapes_dense haux h.limitFrame)
    intro x hx
    rcases hx with ⟨y, ⟨⟨C, D, R⟩, rfl⟩, rfl⟩
    exact h.transformed_mem_closure C D R
  rw [dense_iff_closure_eq] at hclosure ⊢
  simpa only [closure_closure] using hclosure

/-- The non-dynamical construction carried out in Sections 2--5: the five
fields of `approximation` are equations (9)--(12) and the residue mesh in
Proposition 5.2; `arithmetic` is the CRT family of cubic orders, the unit
classification (Proposition 3.4), the suborder congruences (Proposition 4.4),
Lemma 5.1, and the order/period correspondence (Lemma 2.6). -/
structure PaperConstruction where
  approximation : Proposition52.ApproximationData
  arithmetic : ArithmeticRealization

theorem PaperConstruction.density (h : PaperConstruction) :
    Dense periodicTorusShapes :=
  density_from_arithmetic_realization
    h.approximation.auxiliary_shapes_dense h.arithmetic

/-- The arithmetic and elementary approximation construction in the paper.

The proof uses the formalized banana argument
`SL2Banana.banana_expanding_horocycle_dense` and Cusick bound
`Cusick.CubicOrder.regulator_lower_bound`.  It connects the explicit ABC
orders, their suborders, and the approximation data exactly through
Proposition 3.4, Proposition 4.4, Lemma 5.1, and Lemma 2.6. -/
noncomputable def paper_construction : PaperConstruction where
  approximation := Proposition52.approximationData
  arithmetic := PaperArithmetic.arithmeticRealization

/-- **Dang--Gargava--Li, Theorem 1.1.** The shapes of periodic tori in
`M \ SL(3, ℝ) / SL(3, ℤ)` are dense in `SL(2, ℝ) / SL(2, ℤ)`. -/
theorem density_of_shapes_of_periodic_tori :
    Dense periodicTorusShapes := by
  exact paper_construction.density

end CubicPeriodicTori
