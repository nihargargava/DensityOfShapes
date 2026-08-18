import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000

/-!
# Units in the scalar suborders

This file formalizes the local arithmetic in Sections 4 and 5.1 of
Dang--Gargava--Li.  The statements are kept independent of the analytic and
homogeneous-space parts of the argument.

There are two layers.  `LocalPowerLaw.of_base_and_step` is the induction in
Lemmas 4.2 and 4.3 (with the exponent in the proof of Lemma 4.2 corrected).
The companion matrix calculations at the end certify the three initial pairs
`(l,j) = (7,1), (8,1), (24,1)` used in Section 5.1.
-/

namespace PrimePowerCalculations

/-! ## Scalar suborders in integral coordinates -/

/-- Membership in `ℤ + q O` in coordinates `(1,θ₀,θ₀²)`: precisely the
two nonconstant coordinates are divisible by `q`. -/
def InScalarSuborder (q : ℤ) (v : Fin 3 → ℤ) : Prop :=
  q ∣ v 1 ∧ q ∣ v 2

/-- Lemma 4.1 in coordinates.  Pairwise coprimality makes the intersection
of the three scalar suborders equal to the scalar suborder at the product
conductor. -/
theorem inScalarSuborder_mul_three_iff
    {q₁ q₂ q₃ : ℤ}
    (h₁₂ : IsCoprime q₁ q₂) (h₁₃ : IsCoprime q₁ q₃)
    (h₂₃ : IsCoprime q₂ q₃) (v : Fin 3 → ℤ) :
    InScalarSuborder (q₁ * q₂ * q₃) v ↔
      InScalarSuborder q₁ v ∧ InScalarSuborder q₂ v ∧
        InScalarSuborder q₃ v := by
  simp only [InScalarSuborder]
  constructor
  · rintro ⟨h1, h2⟩
    have divide_factor (i : Fin 3) (hi : q₁ * q₂ * q₃ ∣ v i) :
        q₁ ∣ v i ∧ q₂ ∣ v i ∧ q₃ ∣ v i := by
      exact ⟨(dvd_mul_of_dvd_left dvd_rfl q₂ |>.mul_right q₃).trans hi,
        (dvd_mul_of_dvd_right dvd_rfl q₁ |>.mul_right q₃).trans hi,
        (dvd_mul_left q₃ (q₁ * q₂)).trans hi⟩
    rcases divide_factor 1 h1 with ⟨h11, h12, h13⟩
    rcases divide_factor 2 h2 with ⟨h21, h22, h23⟩
    exact ⟨⟨h11, h21⟩, ⟨h12, h22⟩, ⟨h13, h23⟩⟩
  · rintro ⟨⟨h11, h21⟩, ⟨h12, h22⟩, ⟨h13, h23⟩⟩
    have hprod : IsCoprime (q₁ * q₂) q₃ := h₁₃.mul_left h₂₃
    exact ⟨hprod.mul_dvd (h₁₂.mul_dvd h11 h12) h13,
      hprod.mul_dvd (h₁₂.mul_dvd h21 h22) h23⟩

/-- A choice of the two non-scalar integral coordinates of an order.
For the cubic order these are the coefficients of `θ₀` and `θ₀²`. -/
abbrev TailCoordinates (A : Type) [AddCommGroup A] :=
  A →ₗ[ℤ] (Fin 2 → ℤ)

/-- Coordinate form of membership in `ℤ + q O`. -/
def InScalarOrder {A : Type} [AddCommGroup A]
    (tail : TailCoordinates A) (q : ℤ) (x : A) : Prop :=
  ∀ i, q ∣ tail x i

/-- Exact algebraic step `inScalarOrder_neg` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma inScalarOrder_neg {A : Type} [AddCommGroup A]
    (tail : TailCoordinates A) (q : ℤ) (x : A) :
    InScalarOrder tail q (-x) ↔ InScalarOrder tail q x := by
  simp only [InScalarOrder, map_neg]
  constructor
  · intro h i
    simpa using (h i).neg_right
  · intro h i
    simpa using (h i).neg_right

/-- First-order binomial expansion modulo the square of an increment. -/
lemma pow_eq_linear_add_square {A : Type} [Ring A]
    (a q : ℤ) (y : A) (n : ℕ) :
    ∃ z : A,
      ((a : A) + (q : A) * y) ^ n =
        (a : A) ^ n + (n : A) * (a : A) ^ (n - 1) * (q : A) * y +
          (q : A) ^ 2 * z := by
  have hcomm : Commute (a : A) ((q : A) * y) :=
    Commute.mul_right Commute.intCast_left Commute.intCast_left
  rcases n with _ | _
  · exact ⟨0, by simp⟩
  rename_i n
  rcases n with _ | n
  · exact ⟨0, by simp⟩
  rw [hcomm.add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
  let z : A := ∑ m ∈ Finset.range (n + 1),
    (a : A) ^ m * (q : A) ^ (n - m) * y ^ (n + 2 - m) *
      ((n + 2).choose m : A)
  refine ⟨z, ?_⟩
  dsimp [z]
  have hsum :
      ∑ m ∈ Finset.range (n + 1),
          (a : A) ^ m * ((q : A) * y) ^ (n + 2 - m) *
            ((n + 2).choose m : A) =
        (q : A) ^ 2 * ∑ m ∈ Finset.range (n + 1),
          (a : A) ^ m * (q : A) ^ (n - m) * y ^ (n + 2 - m) *
            ((n + 2).choose m : A) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hexp : n + 2 - m = 2 + (n - m) := by omega
    rw [Commute.mul_pow Commute.intCast_left, hexp, pow_add]
    noncomm_ring [Commute.intCast_left.eq]
  rw [hsum]
  simp only [Nat.choose_self, Nat.cast_one, mul_one, pow_zero,
    Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
  push_cast
  have hsub1 : n + 1 - n = 1 := by omega
  have hsub0 : n - n = 0 := by omega
  rw [hsub1, hsub0, pow_one, pow_zero, mul_one]
  have hmiddle :
      (a : A) ^ (n + 1) * ((q : A) * y) * ((n : A) + 1 + 1) =
        ((n : A) + 1 + 1) * (a : A) ^ (n + 1) * (q : A) * y := by
    have hcast : ((n : A) + 1 + 1) = ((n + 2 : ℕ) : A) := by
      push_cast
      abel_nf
      simp
    calc
      (a : A) ^ (n + 1) * ((q : A) * y) * ((n : A) + 1 + 1) =
          ((n : A) + 1 + 1) *
            ((a : A) ^ (n + 1) * ((q : A) * y)) := by
        rw [hcast]
        exact (Nat.cast_commute (n + 2)
          ((a : A) ^ (n + 1) * ((q : A) * y))).eq.symm
      _ = _ := by noncomm_ring
  rw [hmiddle]
  noncomm_ring

/-- Exact algebraic step `prime_mul_dvd_linear_iff` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
private lemma prime_mul_dvd_linear_iff
    {p q a y : ℤ} {n : ℕ} (z : ℤ)
    (hp : Prime p) (hpq : p ∣ q) (hq : q ≠ 0)
    (ha : ¬ p ∣ a) (hy : ¬ p ∣ y) :
    p * q ∣ q * ((n : ℤ) * a ^ (n - 1) * y + q * z) ↔
      p ∣ (n : ℤ) := by
  rw [mul_comm p q, mul_dvd_mul_iff_left hq]
  have hz : p ∣ q * z := dvd_mul_of_dvd_left hpq z
  constructor
  · intro h
    have hlinear : p ∣ (n : ℤ) * a ^ (n - 1) * y := by
      simpa only [add_sub_cancel_right] using dvd_sub h hz
    rcases hp.dvd_mul.mp hlinear with hna | hy'
    · rcases hp.dvd_mul.mp hna with hn | ha'
      · exact hn
      · exact False.elim (ha (hp.dvd_of_dvd_pow ha'))
    · exact False.elim (hy hy')
  · intro hn
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hn _) _) hz

/-- The algebraic lifting step used in Lemmas 4.2 and 4.3.  If
`x = a + q y`, where `p | q`, `a` is a unit modulo `p`, and the non-scalar
tail of `y` is primitive modulo `p`, then `x^n` is scalar modulo `pq`
exactly when `p | n`.

For an order with basis `(1,θ₀,θ₀²)`, take `tail` to be the last two
coefficient maps. -/
theorem inScalarOrder_pow_iff_prime_dvd
    {A : Type} [Ring A]
    (tail : TailCoordinates A) (hscalar : ∀ a : ℤ, tail (a : A) = 0)
    {p q : ℤ} (hp : Prime p) (hpq : p ∣ q) (hq : q ≠ 0)
    (a : ℤ) (y : A) (ha : ¬ p ∣ a)
    (hy : ¬ InScalarOrder tail p y) (n : ℕ) :
    InScalarOrder tail (p * q) (((a : A) + (q : A) * y) ^ n) ↔
      p ∣ (n : ℤ) := by
  obtain ⟨z, hz⟩ := pow_eq_linear_add_square a q y n
  have hterm :
      (n : A) * (a : A) ^ (n - 1) * (q : A) * y =
        ((n : ℤ) * a ^ (n - 1) * q) • y := by
    simp [zsmul_eq_mul]
  have hsq : (q : A) ^ 2 * z = (q ^ 2) • z := by
    simp [zsmul_eq_mul]
  have hscalarPow : tail ((a : A) ^ n) = 0 := by
    rw [← Int.cast_pow]
    exact hscalar (a ^ n)
  have htail :
      tail (((a : A) + (q : A) * y) ^ n) =
        ((n : ℤ) * a ^ (n - 1) * q) • tail y + (q ^ 2) • tail z := by
    rw [hz, hterm, hsq, map_add, map_add, map_zsmul, map_zsmul,
      hscalarPow, zero_add]
  simp only [InScalarOrder]
  constructor
  · intro h
    simp only [htail, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [InScalarOrder] at hy
    obtain ⟨i, hi⟩ := Classical.not_forall.mp hy
    have hdiv := h i
    have hshape :
        (n : ℤ) * a ^ (n - 1) * q * tail y i + q ^ 2 * tail z i =
          q * ((n : ℤ) * a ^ (n - 1) * tail y i + q * tail z i) := by ring
    rw [hshape] at hdiv
    exact (prime_mul_dvd_linear_iff (tail z i) hp hpq hq ha hi).mp hdiv
  · intro hn i
    rw [htail]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hshape :
        (n : ℤ) * a ^ (n - 1) * q * tail y i + q ^ 2 * tail z i =
          q * ((n : ℤ) * a ^ (n - 1) * tail y i + q * tail z i) := by ring
    rw [hshape, mul_comm p q, mul_dvd_mul_iff_left hq]
    exact dvd_add
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hn _) _)
      (dvd_mul_of_dvd_left hpq _)

/-- Prime-power specialization of `inScalarOrder_pow_iff_prime_dvd`. -/
theorem inScalarOrder_pow_primePower_step
    {A : Type} [Ring A]
    (tail : TailCoordinates A) (hscalar : ∀ a : ℤ, tail (a : A) = 0)
    {p c : ℕ} (hp : p.Prime) (hc : 1 ≤ c)
    (a : ℤ) (y : A) (ha : ¬ (p : ℤ) ∣ a)
    (hy : ¬ InScalarOrder tail (p : ℤ) y) (n : ℕ) :
    InScalarOrder tail (p ^ (c + 1) : ℕ)
        (((a : A) + (p ^ c : ℕ) • y) ^ n) ↔ p ∣ n := by
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc0 : c ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hpq : (p : ℤ) ∣ (p ^ c : ℕ) := by
    exact_mod_cast dvd_pow_self p hc0
  have hq : (p ^ c : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hqI : ((p ^ c : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hq
  have h := inScalarOrder_pow_iff_prime_dvd tail hscalar hpI hpq hqI
    a y ha hy n
  rw [← Int.natCast_dvd_natCast]
  simpa [nsmul_eq_mul, pow_succ, mul_comm] using h

/-- `x` is scalar exactly to level `p^c`: its scalar coefficient is a unit
modulo `p`, and its normalized tail is primitive modulo `p`. -/
def PrimePowerSeed {A : Type} [Ring A]
    (tail : TailCoordinates A) (p q : ℕ) (x : A) : Prop :=
  ∃ a : ℤ, ∃ y : A, x = (a : A) + q • y ∧
    ¬ (p : ℤ) ∣ a ∧ ¬ InScalarOrder tail (p : ℤ) y

/-- Exact algebraic step `InScalarOrder.mono` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma InScalarOrder.mono {A : Type} [AddCommGroup A]
    {tail : TailCoordinates A} {q r : ℤ} (hqr : q ∣ r) {x : A}
    (hx : InScalarOrder tail r x) : InScalarOrder tail q x :=
  fun i ↦ hqr.trans (hx i)

/-- Exact algebraic step `PrimePowerSeed.mem` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma PrimePowerSeed.mem
    {A : Type} [Ring A] (tail : TailCoordinates A)
    (hscalar : ∀ a : ℤ, tail (a : A) = 0)
    {p q : ℕ} {x : A} (h : PrimePowerSeed tail p q x) :
    InScalarOrder tail q x := by
  rcases h with ⟨a, y, rfl, -, -⟩
  intro i
  change (q : ℤ) ∣ tail ((a : A) + q • y) i
  rw [map_add, hscalar]
  simp only [Pi.zero_apply, zero_add, map_nsmul, Pi.smul_apply]
  exact ⟨tail y i, by simp [nsmul_eq_mul, mul_comm]⟩

/-- Exact algebraic step `PrimePowerSeed.pow_mem` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma PrimePowerSeed.pow_mem
    {A : Type} [Ring A] (tail : TailCoordinates A)
    (hscalar : ∀ a : ℤ, tail (a : A) = 0)
    {p q : ℕ} {x : A} (h : PrimePowerSeed tail p q x) (n : ℕ) :
    InScalarOrder tail q (x ^ n) := by
  rcases h with ⟨a, y, hx, -, -⟩
  obtain ⟨z, hz⟩ := pow_eq_linear_add_square a q y n
  have hterm :
      (n : A) * (a : A) ^ (n - 1) * (q : A) * y =
        ((n : ℤ) * a ^ (n - 1) * q) • y := by
    simp [zsmul_eq_mul]
  have hsq : (q : A) ^ 2 * z = ((q : ℤ) ^ 2) • z := by
    simp [zsmul_eq_mul]
  have hscalarPow : tail ((a : A) ^ n) = 0 := by
    rw [← Int.cast_pow]
    exact hscalar (a ^ n)
  have hz' :
      ((a : A) + q • y) ^ n =
        (a : A) ^ n + ((n : ℤ) * a ^ (n - 1) * q) • y +
          ((q : ℤ) ^ 2) • z := by
    simpa [nsmul_eq_mul] using hz
  intro i
  rw [hx, hz', map_add, map_add, hscalarPow]
  simp only [map_zsmul, Pi.add_apply, Pi.zero_apply, zero_add,
    Pi.smul_apply, smul_eq_mul]
  apply dvd_add
  · refine ⟨(n : ℤ) * a ^ (n - 1) * tail y i, ?_⟩
    ring
  · refine ⟨(q : ℤ) * tail z i, ?_⟩
    ring

/-- Exact algebraic step `PrimePowerSeed.pow_succ_iff` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma PrimePowerSeed.pow_succ_iff
    {A : Type} [Ring A] (tail : TailCoordinates A)
    (hscalar : ∀ a : ℤ, tail (a : A) = 0)
    {p c : ℕ} (hp : p.Prime) (hc : 1 ≤ c) {x : A}
    (h : PrimePowerSeed tail p (p ^ c) x) (n : ℕ) :
    InScalarOrder tail (p ^ (c + 1) : ℕ) (x ^ n) ↔ p ∣ n := by
  rcases h with ⟨a, y, hx, ha, hy⟩
  rw [hx]
  exact inScalarOrder_pow_primePower_step tail hscalar hp hc a y ha hy n

/-- Once the level is at least `p²`, taking the `p`-th power carries an
exact seed at `p^c` to an exact seed at `p^(c+1)`.  The hypothesis `2 ≤ c`
is essential for `p=2`; at the first lift the quadratic binomial term can
contribute to the normalized tail. -/
theorem PrimePowerSeed.next
    {A : Type} [Ring A] (tail : TailCoordinates A)
    {p c : ℕ} (hp : p.Prime) (hc : 2 ≤ c) {x : A}
    (h : PrimePowerSeed tail p (p ^ c) x) :
    PrimePowerSeed tail p (p ^ (c + 1)) (x ^ p) := by
  rcases h with ⟨a, y, hx, ha, hy⟩
  obtain ⟨z, hz⟩ := pow_eq_linear_add_square a (p ^ c) y p
  let y' : A := a ^ (p - 1) • y + p ^ (c - 1) • z
  refine ⟨a ^ p, y', ?_, ?_, ?_⟩
  · rw [hx]
    push_cast at hz
    simp only [nsmul_eq_mul, zsmul_eq_mul] at hz ⊢
    push_cast
    rw [hz]
    dsimp [y']
    simp only [nsmul_eq_mul, zsmul_eq_mul]
    push_cast
    have hpowers : ((p : A) ^ c) ^ 2 =
        (p : A) * (p : A) ^ c * (p : A) ^ (c - 1) := by
      calc
        ((p : A) ^ c) ^ 2 = (p : A) ^ (c * 2) := by rw [pow_mul]
        _ = (p : A) ^ (1 + c + (c - 1)) := by congr 1; omega
        _ = _ := by rw [pow_add, pow_add, pow_one]
    rw [hpowers]
    have hswap (w : A) :
        (p : A) * ((p : A) ^ c * w) =
          (p : A) ^ c * ((p : A) * w) := by
      calc
        (p : A) * ((p : A) ^ c * w) =
            ((p : A) * (p : A) ^ c) * w := (mul_assoc _ _ _).symm
        _ = (((p : A) ^ c) * (p : A)) * w := by
          rw [(Nat.cast_commute p ((p : A) ^ c)).eq]
        _ = (p : A) ^ c * ((p : A) * w) := mul_assoc _ _ _
    have hmove :
        (a : A) ^ (p - 1) * ((p : A) ^ c * y) =
          (p : A) ^ c * ((a : A) ^ (p - 1) * y) := by
      calc
        (a : A) ^ (p - 1) * ((p : A) ^ c * y) =
            ((a : A) ^ (p - 1) * (p : A) ^ c) * y :=
          (mul_assoc _ _ _).symm
        _ = ((p : A) ^ c * (a : A) ^ (p - 1)) * y := by
          rw [(Nat.cast_commute p (a : A)).pow_left c |>.pow_right (p - 1) |>.eq]
        _ = (p : A) ^ c * ((a : A) ^ (p - 1) * y) := mul_assoc _ _ _
    noncomm_ring [hmove, hswap]
  · intro hd
    exact ha ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hd)
  · simp only [InScalarOrder]
    intro hall
    simp only [y', map_add, map_zsmul, map_nsmul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hall
    simp only [InScalarOrder] at hy
    obtain ⟨i, hi⟩ := Classical.not_forall.mp hy
    have hpPow : (p : ℤ) ∣ (p ^ (c - 1) : ℕ) := by
      exact_mod_cast dvd_pow_self p (by omega : c - 1 ≠ 0)
    have hsecond : (p : ℤ) ∣ (p ^ (c - 1) : ℕ) * tail z i :=
      dvd_mul_of_dvd_left hpPow _
    have hfirst : (p : ℤ) ∣ a ^ (p - 1) * tail y i := by
      simpa [nsmul_eq_mul] using dvd_sub (hall i) hsecond
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hfirst with haPow | hy'
    · exact ha ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow haPow)
    · exact hi hy'

/-- Iterating the uniform lift from an exact level-two seed. -/
theorem PrimePowerSeed.iterate
    {A : Type} [Ring A] (tail : TailCoordinates A)
    {p : ℕ} (hp : p.Prime) {x : A}
    (h : PrimePowerSeed tail p (p ^ 2) x) (k : ℕ) :
    PrimePowerSeed tail p (p ^ (k + 2)) (x ^ (p ^ k)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hn := ih.next tail hp (by omega : 2 ≤ k + 2)
      simpa [pow_succ, pow_mul, Nat.succ_eq_add_one, add_assoc] using hn

/-- All higher-level scalar powers generated by an exact level-two seed. -/
theorem PrimePowerSeed.pow_mem_iff
    {A : Type} [Ring A] (tail : TailCoordinates A)
    (hscalar : ∀ a : ℤ, tail (a : A) = 0)
    {p : ℕ} (hp : p.Prime) {x : A}
    (h : PrimePowerSeed tail p (p ^ 2) x) (k n : ℕ) :
    InScalarOrder tail (p ^ (k + 2) : ℕ) (x ^ n) ↔ p ^ k ∣ n := by
  induction k generalizing n with
  | zero =>
      constructor
      · simp
      · intro
        simpa using h.pow_mem tail hscalar n
  | succ k ih =>
      have hkseed := h.iterate tail hp k
      have hstep := hkseed.pow_succ_iff tail hscalar hp (by omega : 1 ≤ k + 2)
      constructor
      · intro hn
        have hmod : (p ^ (k + 2) : ℤ) ∣ (p ^ (k + 3) : ℕ) := by
          exact_mod_cast pow_dvd_pow p (by omega : k + 2 ≤ k + 3)
        have hnlow : InScalarOrder tail (p ^ (k + 2) : ℕ) (x ^ n) :=
          InScalarOrder.mono hmod hn
        rcases (ih n).mp hnlow with ⟨m, rfl⟩
        have hm : p ∣ m := by
          apply (hstep m).mp
          rw [← pow_mul]
          simpa [Nat.succ_eq_add_one, add_assoc] using hn
        rcases hm with ⟨z, rfl⟩
        refine ⟨z, ?_⟩
        rw [pow_succ]
        ring
      · rintro ⟨m, rfl⟩
        have hh := (hstep (p * m)).mpr (dvd_mul_right p m)
        simpa [pow_succ, pow_mul, Nat.succ_eq_add_one, add_assoc,
          mul_assoc] using hh

/-- Natural-exponent form of Lemmas 4.2 and 4.3.  Besides the finite
period computation modulo `p`, it asks for exact seeds at levels one and
two.  The second seed is the extra datum required to cover the exceptional
first `2`-adic lift rigorously; `PrimePowerSeed.next` proves every later
level uniformly. -/
theorem localPowerLaw_nat
    {A : Type} [Ring A] (tail : TailCoordinates A)
    (hscalar : ∀ a : ℤ, tail (a : A) = 0)
    {p l : ℕ} (hp : p.Prime) {b : A}
    (hbase : ∀ n : ℕ, InScalarOrder tail p (b ^ n) ↔ l ∣ n)
    (hseed1 : PrimePowerSeed tail p p (b ^ l))
    (hseed2 : PrimePowerSeed tail p (p ^ 2) (b ^ (l * p)))
    (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    InScalarOrder tail (p ^ c : ℕ) (b ^ n) ↔
      l * p ^ (c - 1) ∣ n := by
  by_cases hc1 : c = 1
  · subst c
    simpa using hbase n
  · have hc2 : 2 ≤ c := by omega
    let k := c - 2
    have hkc : k + 2 = c := by dsimp [k]; omega
    constructor
    · intro hn
      have hmod1 : (p : ℤ) ∣ (p ^ c : ℕ) := by
        exact_mod_cast dvd_pow_self p (by omega : c ≠ 0)
      have hn1 := InScalarOrder.mono hmod1 hn
      rcases (hbase n).mp hn1 with ⟨m, rfl⟩
      have hmod2 : (p ^ 2 : ℤ) ∣ (p ^ c : ℕ) := by
        exact_mod_cast pow_dvd_pow p hc2
      have hn2 : InScalarOrder tail (p ^ 2 : ℕ) ((b ^ l) ^ m) := by
        rw [← pow_mul]
        exact InScalarOrder.mono hmod2 hn
      have hseed1' : PrimePowerSeed tail p (p ^ 1) (b ^ l) := by
        simpa using hseed1
      have hpm : p ∣ m :=
        (hseed1'.pow_succ_iff tail hscalar hp (by omega) m).mp hn2
      rcases hpm with ⟨z, rfl⟩
      have hhigh : InScalarOrder tail (p ^ (k + 2) : ℕ)
          ((b ^ (l * p)) ^ z) := by
        rw [hkc, ← pow_mul]
        simpa [mul_assoc] using hn
      have hkz : p ^ k ∣ z :=
        (hseed2.pow_mem_iff tail hscalar hp k z).mp hhigh
      rcases hkz with ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      dsimp [k]
      rw [show c - 1 = (c - 2) + 1 by omega, pow_succ]
      ring
    · rintro ⟨w, rfl⟩
      have hkdiv : p ^ k ∣ p ^ (c - 2) * w := by
        dsimp [k]
        exact dvd_mul_right _ _
      have hhigh := (hseed2.pow_mem_iff tail hscalar hp k
        (p ^ (c - 2) * w)).mpr hkdiv
      rw [hkc] at hhigh
      rw [show c - 1 = (c - 2) + 1 by omega, pow_succ]
      rw [← pow_mul] at hhigh
      convert hhigh using 1 <;> ring

/-! ## The abstract prime-power induction -/

/-- `P c n` means that the `n`-th power of a fixed unit is scalar modulo
`p^c`.  This packages the common conclusion of Lemmas 4.2 and 4.3 without choosing a model
for the ambient cubic order. -/
def LocalPowerLaw (P : ℕ → ℤ → Prop) (p l j : ℕ) : Prop :=
  ∀ c ≥ 1, ∀ n : ℤ, P c n ↔ (l * p ^ (c - j) : ℤ) ∣ n

/-- Extend a natural-exponent classification to all integral exponents once
membership is known to be invariant under inversion. -/
theorem int_power_law_of_nat_of_neg
    (P : ℤ → Prop) (N : ℕ)
    (hnat : ∀ n : ℕ, P n ↔ N ∣ n)
    (hneg : ∀ n : ℕ, P (-n) ↔ P n) (z : ℤ) :
    P z ↔ (N : ℤ) ∣ z := by
  cases z with
  | ofNat n =>
      change P (n : ℤ) ↔ (N : ℤ) ∣ (n : ℤ)
      rw [hnat]
      exact Int.natCast_dvd_natCast.symm
  | negSucc n =>
      change P (-((n + 1 : ℕ) : ℤ)) ↔
        (N : ℤ) ∣ -((n + 1 : ℕ) : ℤ)
      rw [hneg, hnat]
      simpa only [dvd_neg] using
        (Int.natCast_dvd_natCast (m := N) (n := n + 1)).symm

/-- Exact algebraic step `LocalPowerLaw.of_nat_of_neg` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
theorem LocalPowerLaw.of_nat_of_neg
    (P : ℕ → ℤ → Prop) (p l j : ℕ)
    (hnat : ∀ c, 1 ≤ c → ∀ n : ℕ,
      P c n ↔ l * p ^ (c - j) ∣ n)
    (hneg : ∀ c, 1 ≤ c → ∀ n : ℕ, P c (-n) ↔ P c n) :
    LocalPowerLaw P p l j := by
  intro c hc n
  exact int_power_law_of_nat_of_neg (P c) (l * p ^ (c - j))
    (hnat c hc) (hneg c hc) n

/-- The formal induction used in Lemmas 4.2 and 4.3.  The algebraic binomial calculation
is precisely the hypothesis `step`: after level `j`, passing from modulus
`p^c` to `p^(c+1)` multiplies the exponent modulus by `p`.

The paper writes `p^(l₂-c)` once in the proof; the correct exponent is
`p^(c-l₂)`, as in its statement and in this theorem. -/
theorem LocalPowerLaw.of_base_and_step
    (P : ℕ → ℤ → Prop) (p l j : ℕ)
    (hj : 1 ≤ j)
    (base : ∀ c, 1 ≤ c → c ≤ j → ∀ n : ℤ, P c n ↔ (l : ℤ) ∣ n)
    (step : ∀ c, j ≤ c → ∀ n : ℤ,
      P (c + 1) n ↔ (l * p ^ (c + 1 - j) : ℤ) ∣ n) :
    LocalPowerLaw P p l j := by
  intro c hc n
  by_cases hcj : c ≤ j
  · have hsub : c - j = 0 := Nat.sub_eq_zero_of_le hcj
    simpa [hsub] using base c hc hcj n
  · have hjc : j ≤ c - 1 := by omega
    have hcpos : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hc
    have hcEq : c = (c - 1) + 1 := by omega
    rw [hcEq]
    exact step _ hjc n

/-! ## The three-congruence lattice -/

/-- The exponent conditions supplied by the three local power laws. -/
def ExponentConditions (c d r : ℕ) : Set (ℤ × ℤ) :=
  {mn |
    (7 * 2 ^ (c - 1) : ℤ) ∣ mn.1 + mn.2 ∧
    (8 * 3 ^ (d - 1) : ℤ) ∣ mn.1 - 2 * mn.2 ∧
    (24 * 5 ^ (r - 1) : ℤ) ∣ 2 * mn.1 - mn.2}

/-- Combining the local equivalences gives exactly equation (7) of the
paper.  The hypotheses are the three reductions
`b₁ᵐb₂ⁿ ↦ b₁^(m+n), b₁^(m-2n), b₂^(n-2m)` at `2,3,5`.
-/
theorem mem_exponentConditions_iff
    (P₂ P₃ P₅ : ℕ → ℤ → Prop)
    (h₂ : LocalPowerLaw P₂ 2 7 1)
    (h₃ : LocalPowerLaw P₃ 3 8 1)
    (h₅ : LocalPowerLaw P₅ 5 24 1)
    {c d r : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (m n : ℤ) :
    P₂ c (m + n) ∧ P₃ d (m - 2 * n) ∧ P₅ r (n - 2 * m) ↔
      (m, n) ∈ ExponentConditions c d r := by
  rw [h₂ c hc, h₃ d hd, h₅ r hr]
  simp only [ExponentConditions, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by simpa [neg_sub] using h3.neg_right⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by simpa [neg_sub] using h3.neg_right⟩

/-! ## Companion-matrix certificates -/

/-- Multiplication by `X` in
`ℤ[X]/(X³ - sX² + tX - 1)`, in the basis `(1,X,X²)`. -/
def companion (R : Type) [CommRing R] (s t : R) : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 0, 1], ![1, 0, -t], ![0, 1, s]]

/-- Multiplication by `X-a` in the same cubic algebra. -/
def shiftedCompanion (R : Type) [CommRing R] (s t a : R) :
    Matrix (Fin 3) (Fin 3) R :=
  companion R s t - a • 1

/-- Exact algebraic step `map_companion` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma map_companion {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (s t : R) :
    (companion R s t).map f = companion S (f s) (f t) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change f 0 = 0
    exact map_zero f
  · change f 0 = 0
    exact map_zero f
  · change f 1 = 1
    exact map_one f
  · change f 1 = 1
    exact map_one f
  · change f 0 = 0
    exact map_zero f
  · change f (-t) = -(f t)
    exact map_neg f t
  · change f 0 = 0
    exact map_zero f
  · change f 1 = 1
    exact map_one f
  · change f s = f s
    rfl

/-- Exact algebraic step `map_shiftedCompanion` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma map_shiftedCompanion {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (s t a : R) :
    (shiftedCompanion R s t a).map f =
      shiftedCompanion S (f s) (f t) (f a) := by
  rw [shiftedCompanion, shiftedCompanion]
  rw [Matrix.map_sub f (map_sub f)]
  rw [map_companion]
  rw [Matrix.map_smul' f a (1 : Matrix (Fin 3) (Fin 3) R) (map_mul f)]
  congr 2
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply]

/-- Multiplication by the distinguished generator `θ₀`, reduced modulo `q`. -/
def thetaZeroMatrix (q : ℕ) (a₁ a₂ : ZMod q) :
    Matrix (Fin 3) (Fin 3) (ZMod q) :=
  companion (ZMod q) (a₁ + a₂) (a₁ * a₂)

/-- Multiplication by `θ₀-a₁`, reduced modulo `q`. -/
def thetaZeroSubOneMatrix (q : ℕ) (a₁ a₂ : ZMod q) :
    Matrix (Fin 3) (Fin 3) (ZMod q) :=
  shiftedCompanion (ZMod q) (a₁ + a₂) (a₁ * a₂) a₁

/-- Exact algebraic step `thetaZeroMatrix_zero_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma thetaZeroMatrix_zero_one (q : ℕ) :
    thetaZeroMatrix q 0 1 = companion (ZMod q) 1 0 := by
  simp [thetaZeroMatrix]

/-- Exact algebraic step `thetaZeroMatrix_one_zero` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma thetaZeroMatrix_one_zero (q : ℕ) :
    thetaZeroMatrix q 1 0 = companion (ZMod q) 1 0 := by
  simp [thetaZeroMatrix]

/-- Exact algebraic step `thetaZeroSubOneMatrix_one_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma thetaZeroSubOneMatrix_one_one (q : ℕ) :
    thetaZeroSubOneMatrix q 1 1 = shiftedCompanion (ZMod q) 2 1 1 := by
  unfold thetaZeroSubOneMatrix
  congr 1 <;> norm_num

/-- Exact algebraic step `thetaZeroMatrix_eq_of_cast_eq_zero_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma thetaZeroMatrix_eq_of_cast_eq_zero_one (q a₁ a₂ : ℕ)
    (h₁ : (a₁ : ZMod q) = 0) (h₂ : (a₂ : ZMod q) = 1) :
    thetaZeroMatrix q a₁ a₂ = companion (ZMod q) 1 0 := by
  rw [h₁, h₂, thetaZeroMatrix_zero_one]

/-- Exact algebraic step `thetaZeroMatrix_eq_of_cast_eq_one_zero` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma thetaZeroMatrix_eq_of_cast_eq_one_zero (q a₁ a₂ : ℕ)
    (h₁ : (a₁ : ZMod q) = 1) (h₂ : (a₂ : ZMod q) = 0) :
    thetaZeroMatrix q a₁ a₂ = companion (ZMod q) 1 0 := by
  rw [h₁, h₂, thetaZeroMatrix_one_zero]

/-- Exact algebraic step `thetaZeroSubOneMatrix_eq_of_cast_eq_one_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma thetaZeroSubOneMatrix_eq_of_cast_eq_one_one (q a₁ a₂ : ℕ)
    (h₁ : (a₁ : ZMod q) = 1) (h₂ : (a₂ : ZMod q) = 1) :
    thetaZeroSubOneMatrix q a₁ a₂ = shiftedCompanion (ZMod q) 2 1 1 := by
  rw [h₁, h₂, thetaZeroSubOneMatrix_one_one]

/-- The coefficient vector of the represented element is the first column
of its multiplication matrix. -/
def coefficientVector {R : Type} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) : Fin 3 → R :=
  M.mulVec ![1, 0, 0]

/-- An element of the cubic algebra is scalar when its `X` and `X²`
coefficients vanish. -/
def IsScalar {R : Type} [CommRing R] [DecidableEq R]
    (M : Matrix (Fin 3) (Fin 3) R) : Prop :=
  coefficientVector M 1 = 0 ∧ coefficientVector M 2 = 0

instance instDecidableIsScalar {R : Type} [CommRing R] [DecidableEq R]
    (M : Matrix (Fin 3) (Fin 3) R) : Decidable (IsScalar M) := by
  unfold IsScalar
  infer_instance

/-- Exact algebraic step `isScalar_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma isScalar_one (R : Type) [CommRing R] [DecidableEq R] :
    IsScalar (1 : Matrix (Fin 3) (Fin 3) R) := by
  simp [IsScalar, coefficientVector, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- The two non-scalar coordinates of an integral multiplication matrix. -/
def matrixTail : TailCoordinates (Matrix (Fin 3) (Fin 3) ℤ) where
  toFun M := ![M 1 0, M 2 0]
  map_add' x y := by
    ext i
    fin_cases i <;> rfl
  map_smul' _ _ := by
    ext i
    fin_cases i <;> simp

/-- Exact algebraic step `matrixTail_intCast` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma matrixTail_intCast (a : ℤ) :
    matrixTail (a : Matrix (Fin 3) (Fin 3) ℤ) = 0 := by
  ext i
  fin_cases i <;> simp [matrixTail, Matrix.intCast_apply]

/-- Exact algebraic step `inScalarOrder_matrix_iff_isScalar_map` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma inScalarOrder_matrix_iff_isScalar_map
    (q : ℕ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    InScalarOrder matrixTail q M ↔
      IsScalar (M.map (Int.castRingHom (ZMod q))) := by
  simp [InScalarOrder, matrixTail, IsScalar, coefficientVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

def integerCommonMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  companion ℤ 1 0

def integerFiveMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  shiftedCompanion ℤ 2 1 1

/-! The next two equalities are the explicit `2`-adic calculations printed
in Section 5.1.  Together with the finite-period, residue, and exactness
lemmas below, they give kernel-checked Lean proofs of every SageMath result
used there. -/

lemma integerCommon_pow_seven_coefficients :
    coefficientVector (integerCommonMatrix ^ 7) = ![3, 2, 4] := by
  decide

/-- Exact algebraic step `integerCommon_pow_fourteen_coefficients` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerCommon_pow_fourteen_coefficients :
    coefficientVector (integerCommonMatrix ^ 14) = ![41, 28, 60] := by
  decide

/-- Exact algebraic step `map_integerCommonMatrix` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma map_integerCommonMatrix (q : ℕ) :
    integerCommonMatrix.map (Int.castRingHom (ZMod q)) =
      companion (ZMod q) 1 0 := by
  rw [integerCommonMatrix, map_companion]
  norm_num

/-- Exact algebraic step `map_integerFiveMatrix` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma map_integerFiveMatrix (q : ℕ) :
    integerFiveMatrix.map (Int.castRingHom (ZMod q)) =
      shiftedCompanion (ZMod q) 2 1 1 := by
  rw [integerFiveMatrix, map_shiftedCompanion]
  norm_num

/-- A reusable finite-state criterion: if `M` has period `l` and among the
first `l` powers only the zeroth is scalar, then scalar powers are exactly
the multiples of `l`. -/
theorem isScalar_pow_iff_dvd_of_period
    {R : Type} [CommRing R] [DecidableEq R]
    (M : Matrix (Fin 3) (Fin 3) R) (l : ℕ)
    (hl : 0 < l) (hperiod : M ^ l = 1)
    (hresidue : ∀ k, k < l → (IsScalar (M ^ k) ↔ k = 0))
    (n : ℕ) :
    IsScalar (M ^ n) ↔ l ∣ n := by
  have hreduce : M ^ n = M ^ (n % l) := by
    conv_lhs => rw [(Nat.mod_add_div n l).symm]
    rw [pow_add, pow_mul, hperiod, one_pow, mul_one]
  rw [hreduce, hresidue (n % l) (Nat.mod_lt _ hl)]
  exact Nat.dvd_iff_mod_eq_zero.symm

/-! The local polynomial at both `2` and `3` is `X³-X²-1`; at `5` it
is `X³-2X²+X-1`, and the relevant generator there is `X-1`. -/

def localTwoMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  companion (ZMod 2) 1 0

def localThreeMatrix : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  companion (ZMod 3) 1 0

def localFiveMatrix : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  shiftedCompanion (ZMod 5) 2 1 1

/-- Exact algebraic step `localTwo_period` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localTwo_period : localTwoMatrix ^ 7 = 1 := by decide
/-- Exact algebraic step `localThree_period` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localThree_period : localThreeMatrix ^ 8 = 1 := by decide
/-- Exact algebraic step `localFive_period` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localFive_period : localFiveMatrix ^ 24 = 1 := by decide

/-- Exact algebraic step `localTwo_residues` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localTwo_residues (k : ℕ) (hk : k < 7) :
    IsScalar (localTwoMatrix ^ k) ↔ k = 0 := by
  interval_cases k <;> decide

/-- Exact algebraic step `localThree_residues` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localThree_residues (k : ℕ) (hk : k < 8) :
    IsScalar (localThreeMatrix ^ k) ↔ k = 0 := by
  interval_cases k <;> decide

/-- Exact algebraic step `localFive_residues` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localFive_residues (k : ℕ) (hk : k < 24) :
    IsScalar (localFiveMatrix ^ k) ↔ k = 0 := by
  interval_cases k <;> decide

/-- The three `l` values in Section 5.1, proved by exhaustive computation in
the relevant finite cubic algebras. -/
theorem localTwo_scalar_pow_iff (n : ℕ) :
    IsScalar (localTwoMatrix ^ n) ↔ 7 ∣ n :=
  isScalar_pow_iff_dvd_of_period localTwoMatrix 7 (by omega)
    localTwo_period localTwo_residues n

/-- Exact algebraic step `localThree_scalar_pow_iff` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
theorem localThree_scalar_pow_iff (n : ℕ) :
    IsScalar (localThreeMatrix ^ n) ↔ 8 ∣ n :=
  isScalar_pow_iff_dvd_of_period localThreeMatrix 8 (by omega)
    localThree_period localThree_residues n

/-- Exact algebraic step `localFive_scalar_pow_iff` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
theorem localFive_scalar_pow_iff (n : ℕ) :
    IsScalar (localFiveMatrix ^ n) ↔ 24 ∣ n :=
  isScalar_pow_iff_dvd_of_period localFiveMatrix 24 (by omega)
    localFive_period localFive_residues n

/-! Exact first-level valuations.  These are the `jᵢ=1` computations: the
minimal scalar power modulo `p` ceases to be scalar modulo `p²`. -/

def localTwoMatrixModFour : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  companion (ZMod 4) 1 0

def localThreeMatrixModNine : Matrix (Fin 3) (Fin 3) (ZMod 9) :=
  companion (ZMod 9) 1 0

def localFiveMatrixModTwentyFive : Matrix (Fin 3) (Fin 3) (ZMod 25) :=
  shiftedCompanion (ZMod 25) 2 1 1

/-- Exact algebraic step `localTwo_exact_level_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localTwo_exact_level_one :
    ¬ IsScalar (localTwoMatrixModFour ^ 7) := by decide

/-- Exact algebraic step `localThree_exact_level_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localThree_exact_level_one :
    ¬ IsScalar (localThreeMatrixModNine ^ 8) := by decide

/-- Exact algebraic step `localFive_exact_level_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localFive_exact_level_one :
    ¬ IsScalar (localFiveMatrixModTwentyFive ^ 24) := by decide

/-! The first lift needs one further exactness certificate.  This is the
additional hypothesis of Lemma 4.3 at `p=2` (and is inexpensive to record
uniformly at all three primes).  From level two onward `PrimePowerSeed.next`
supplies all further levels without computation. -/

def localTwoMatrixModEight : Matrix (Fin 3) (Fin 3) (ZMod 8) :=
  companion (ZMod 8) 1 0

def localThreeMatrixModTwentySeven : Matrix (Fin 3) (Fin 3) (ZMod 27) :=
  companion (ZMod 27) 1 0

def localFiveMatrixModOneTwentyFive : Matrix (Fin 3) (Fin 3) (ZMod 125) :=
  shiftedCompanion (ZMod 125) 2 1 1

/-- Exact algebraic step `localTwo_first_lift_scalar` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localTwo_first_lift_scalar :
    IsScalar (localTwoMatrixModFour ^ 14) := by decide

/-- Exact algebraic step `localTwo_first_lift_exact` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localTwo_first_lift_exact :
    ¬ IsScalar (localTwoMatrixModEight ^ 14) := by decide

/-- Exact algebraic step `localThree_first_lift_scalar` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localThree_first_lift_scalar :
    IsScalar (localThreeMatrixModNine ^ 24) := by decide

/-- Exact algebraic step `localThree_first_lift_exact` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localThree_first_lift_exact :
    ¬ IsScalar (localThreeMatrixModTwentySeven ^ 24) := by decide

/-- Exact algebraic step `localFive_first_lift_scalar` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localFive_first_lift_scalar :
    IsScalar (localFiveMatrixModTwentyFive ^ 120) := by decide

/-- Exact algebraic step `localFive_first_lift_exact` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma localFive_first_lift_exact :
    ¬ IsScalar (localFiveMatrixModOneTwentyFive ^ 120) := by decide

/-! Exact integral seeds corresponding to the finite certificates.  These
equalities are closed computations in `Mat₃(ℤ)`; their primitive-tail
fields record non-scalarity at the next prime-power level. -/

lemma integerTwo_seed_one :
    PrimePowerSeed matrixTail 2 2 (integerCommonMatrix ^ 7) := by
  refine ⟨3, ![![0, 2, 3], ![1, 0, 2], ![2, 3, 3]], ?_, ?_, ?_⟩
  · decide
  · norm_num
  · intro h
    have h₀ := h 0
    norm_num [matrixTail] at h₀

/-- Exact algebraic step `integerTwo_seed_two` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerTwo_seed_two :
    PrimePowerSeed matrixTail 2 (2 ^ 2) (integerCommonMatrix ^ (7 * 2)) := by
  refine ⟨41, ![![0, 15, 22], ![7, 0, 15], ![15, 22, 22]], ?_, ?_, ?_⟩
  · decide
  · norm_num
  · intro h
    have h₀ := h 0
    norm_num [matrixTail] at h₀

/-- Exact algebraic step `integerThree_seed_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerThree_seed_one :
    PrimePowerSeed matrixTail 3 3 (integerCommonMatrix ^ 8) := by
  refine ⟨4, ![![0, 2, 3], ![1, 0, 2], ![2, 3, 3]], ?_, ?_, ?_⟩
  · decide
  · norm_num
  · intro h
    have h₀ := h 0
    norm_num [matrixTail] at h₀

/-- Exact algebraic step `integerThree_seed_two` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerThree_seed_two :
    PrimePowerSeed matrixTail 3 (3 ^ 2) (integerCommonMatrix ^ (8 * 3)) := by
  refine ⟨1873, ![![0, 305, 447], ![142, 0, 305], ![305, 447, 447]],
    ?_, ?_, ?_⟩
  · decide
  · norm_num
  · intro h
    have h₀ := h 0
    norm_num [matrixTail] at h₀

/-- Exact algebraic step `integerFive_seed_one` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerFive_seed_one :
    PrimePowerSeed matrixTail 5 5 (integerFiveMatrix ^ 24) := by
  refine ⟨1, ![![-5, -3, 2], ![8, -2, -5], ![-3, 2, 2]], ?_, ?_, ?_⟩
  · decide
  · norm_num
  · intro h
    have h₀ := h 0
    norm_num [matrixTail] at h₀

/-- Exact algebraic step `integerFive_seed_two` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerFive_seed_two :
    PrimePowerSeed matrixTail 5 (5 ^ 2) (integerFiveMatrix ^ (24 * 5)) := by
  refine ⟨1,
    ![![-489280, 451022, 389367], ![-512677, -940302, 61655],
      ![451022, 389367, -161568]], ?_, ?_, ?_⟩
  · decide
  · norm_num
  · intro h
    have h₀ := h 0
    norm_num [matrixTail] at h₀

/-- Exact algebraic step `integerCommon_mod_two_scalar_pow_iff` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerCommon_mod_two_scalar_pow_iff (n : ℕ) :
    InScalarOrder matrixTail 2 (integerCommonMatrix ^ n) ↔ 7 ∣ n := by
  change InScalarOrder matrixTail ((2 : ℕ) : ℤ) (integerCommonMatrix ^ n) ↔ 7 ∣ n
  rw [inScalarOrder_matrix_iff_isScalar_map, Matrix.map_pow,
    map_integerCommonMatrix]
  exact localTwo_scalar_pow_iff n

/-- Exact algebraic step `integerCommon_mod_three_scalar_pow_iff` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerCommon_mod_three_scalar_pow_iff (n : ℕ) :
    InScalarOrder matrixTail 3 (integerCommonMatrix ^ n) ↔ 8 ∣ n := by
  change InScalarOrder matrixTail ((3 : ℕ) : ℤ) (integerCommonMatrix ^ n) ↔ 8 ∣ n
  rw [inScalarOrder_matrix_iff_isScalar_map, Matrix.map_pow,
    map_integerCommonMatrix]
  exact localThree_scalar_pow_iff n

/-- Exact algebraic step `integerFive_mod_five_scalar_pow_iff` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
lemma integerFive_mod_five_scalar_pow_iff (n : ℕ) :
    InScalarOrder matrixTail 5 (integerFiveMatrix ^ n) ↔ 24 ∣ n := by
  change InScalarOrder matrixTail ((5 : ℕ) : ℤ) (integerFiveMatrix ^ n) ↔ 24 ∣ n
  rw [inScalarOrder_matrix_iff_isScalar_map, Matrix.map_pow,
    map_integerFiveMatrix]
  exact localFive_scalar_pow_iff n

/-- The complete `2`-adic power law for the canonical distinguished generator. -/
theorem integerTwo_power_law (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    InScalarOrder matrixTail (2 ^ c : ℕ) (integerCommonMatrix ^ n) ↔
      7 * 2 ^ (c - 1) ∣ n :=
  localPowerLaw_nat matrixTail matrixTail_intCast Nat.prime_two
    integerCommon_mod_two_scalar_pow_iff integerTwo_seed_one
    integerTwo_seed_two c hc n

/-- The complete `3`-adic power law for the canonical distinguished generator. -/
theorem integerThree_power_law (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    InScalarOrder matrixTail (3 ^ c : ℕ) (integerCommonMatrix ^ n) ↔
      8 * 3 ^ (c - 1) ∣ n :=
  localPowerLaw_nat matrixTail matrixTail_intCast Nat.prime_three
    integerCommon_mod_three_scalar_pow_iff integerThree_seed_one
    integerThree_seed_two c hc n

/-- The complete `5`-adic power law for the shifted distinguished generator. -/
theorem integerFive_power_law (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    InScalarOrder matrixTail (5 ^ c : ℕ) (integerFiveMatrix ^ n) ↔
      24 * 5 ^ (c - 1) ∣ n :=
  localPowerLaw_nat matrixTail matrixTail_intCast Nat.prime_five
    integerFive_mod_five_scalar_pow_iff integerFive_seed_one
    integerFive_seed_two c hc n

/-- The complete finite certificate used as input to the generic lifting
arguments in Lemmas 4.2 and 4.3. -/
structure LocalCertificate where
  prime : ℕ
  exponent : ℕ
  periodAtPrime : Prop
  exactAtSquare : Prop

def twoCertificate : LocalCertificate where
  prime := 2
  exponent := 7
  periodAtPrime := ∀ n, IsScalar (localTwoMatrix ^ n) ↔ 7 ∣ n
  exactAtSquare := ¬ IsScalar (localTwoMatrixModFour ^ 7)

def threeCertificate : LocalCertificate where
  prime := 3
  exponent := 8
  periodAtPrime := ∀ n, IsScalar (localThreeMatrix ^ n) ↔ 8 ∣ n
  exactAtSquare := ¬ IsScalar (localThreeMatrixModNine ^ 8)

def fiveCertificate : LocalCertificate where
  prime := 5
  exponent := 24
  periodAtPrime := ∀ n, IsScalar (localFiveMatrix ^ n) ↔ 24 ∣ n
  exactAtSquare := ¬ IsScalar (localFiveMatrixModTwentyFive ^ 24)

/-- Exact algebraic step `twoCertificate_valid` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
theorem twoCertificate_valid :
    twoCertificate.periodAtPrime ∧ twoCertificate.exactAtSquare := by
  exact ⟨localTwo_scalar_pow_iff, localTwo_exact_level_one⟩

/-- Exact algebraic step `threeCertificate_valid` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
theorem threeCertificate_valid :
    threeCertificate.periodAtPrime ∧ threeCertificate.exactAtSquare := by
  exact ⟨localThree_scalar_pow_iff, localThree_exact_level_one⟩

/-- Exact algebraic step `fiveCertificate_valid` used in Lemmas 4.1--4.3 or the computations of Section 5.1. -/
theorem fiveCertificate_valid :
    fiveCertificate.periodAtPrime ∧ fiveCertificate.exactAtSquare := by
  exact ⟨localFive_scalar_pow_iff, localFive_exact_level_one⟩

end PrimePowerCalculations
