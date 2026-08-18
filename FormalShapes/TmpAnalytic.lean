import CusickRegulator
noncomputable section
namespace Cusick

lemma cubic_log_bound_sorted {a b c d : ℝ}
    (hd : 4 ≤ d)
    (hddisc : d ≤ ((a-b)*(a-c)*(b-c))^2)
    (hprod : |a*b*c| = 1)
    (hab : |b| ≤ |a|) (hbc : |c| ≤ |b|) :
    Real.log (d/4) ≤ 2 * Real.sqrt 2 *
      Real.sqrt (Real.log |a| ^ 2 + Real.log |b| ^ 2 + Real.log |c| ^ 2) := by
  have habc : a*b*c ≠ 0 := by
    intro h
    rw [h, abs_zero] at hprod
    norm_num at hprod
  have ha : a ≠ 0 := by
    intro h
    apply habc
    rw [h, zero_mul, zero_mul]
  have hb : b ≠ 0 := by
    intro h
    apply habc
    rw [h, mul_zero, zero_mul]
  have hc : c ≠ 0 := by
    intro h
    apply habc
    rw [h, mul_zero]
  let v := b/a
  let w := c/b
  have hvabs : |v| ≤ 1 := by
    dsimp [v]
    rw [abs_div, div_le_one (abs_pos.mpr ha)]
    exact hab
  have hwabs : |w| ≤ 1 := by
    dsimp [w]
    rw [abs_div, div_le_one (abs_pos.mpr hb)]
    exact hbc
  have hv : v ∈ Set.Icc (-1:ℝ) 1 := by
    exact abs_le.mp hvabs
  have hw : w ∈ Set.Icc (-1:ℝ) 1 := by
    exact abs_le.mp hwabs
  obtain ⟨hfac0, hfac2⟩ := cubic_factor_nonneg_le_two hv hw
  let f := (1-v)*(1-w)*(1-v*w)
  have hfac : f = (1-v)*(1-w)*(1-v*w) := rfl
  have hdiff : (a-b)*(a-c)*(b-c) = a^2*b*f := by
    dsimp [f, v, w]
    field_simp
  have hf2 : f^2 ≤ 4 := by nlinarith
  have hdiffupper : ((a-b)*(a-c)*(b-c))^2 ≤ |a|^4*|b|^2*4 := by
    rw [hdiff]
    have habs : (a^2*b*f)^2 = |a|^4*|b|^2*f^2 := by
      rw [(show Even 4 by exact ⟨2, rfl⟩).pow_abs a, sq_abs b]
      ring
    rw [habs]
    gcongr
  have hd4 : d/4 ≤ |a|^4*|b|^2 := by
    nlinarith [hddisc.trans hdiffupper]
  have hdpos : 0 < d/4 := by positivity
  have habpos : 0 < |a|^4*|b|^2 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hdpos habpos hd4
  have hlogexpand : Real.log (|a|^4*|b|^2) =
      4*Real.log |a| + 2*Real.log |b| := by
    rw [Real.log_mul (pow_ne_zero _ (abs_ne_zero.mpr ha))
      (pow_ne_zero _ (abs_ne_zero.mpr hb)), Real.log_pow, Real.log_pow]
    norm_num
  rw [hlogexpand] at hlog
  let x := Real.log |a|
  let y := Real.log |b|
  let z := Real.log |c|
  have hsum : x+y+z=0 := by
    dsimp [x,y,z]
    rw [← Real.log_mul (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb),
      ← Real.log_mul (mul_ne_zero (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb))
        (abs_ne_zero.mpr hc), ← abs_mul, ← abs_mul, hprod, Real.log_one]
  have hxy : y ≤ x := by
    dsimp [x,y]
    exact Real.strictMonoOn_log.monotoneOn (abs_pos.mpr hb) (abs_pos.mpr ha) hab
  have hyz : z ≤ y := by
    dsimp [y,z]
    exact Real.strictMonoOn_log.monotoneOn (abs_pos.mpr hc) (abs_pos.mpr hb) hbc
  have hlin0 : 0 ≤ 2*x+y := by linarith
  let Q := x^2+y^2+z^2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsq : (2*x+y)^2 ≤ 2*Q := by
    dsimp [Q]
    nlinarith [sq_nonneg y]
  have hsqrt : 2*x+y ≤ Real.sqrt 2 * Real.sqrt Q := by
    have hs2 : 0 ≤ Real.sqrt 2 * Real.sqrt Q := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ hlin0 hs2).mp
    calc
      (2*x+y)^2 ≤ 2*Q := hsq
      _ = (Real.sqrt 2 * Real.sqrt Q)^2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
          Real.sq_sqrt hQ]
  calc
    Real.log (d/4) ≤ 2*(2*x+y) := by
      dsimp [x, y]
      linarith [hlog]
    _ ≤ 2*(Real.sqrt 2 * Real.sqrt Q) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = 2 * Real.sqrt 2 *
        Real.sqrt (Real.log |a| ^ 2 + Real.log |b| ^ 2 + Real.log |c| ^ 2) := by
      dsimp [Q,x,y,z]
      ring

end Cusick

namespace Cusick
lemma cubic_log_bound {a b c d : ℝ}
    (hd : 4 ≤ d)
    (hddisc : d ≤ ((a-b)*(a-c)*(b-c))^2)
    (hprod : |a*b*c| = 1) :
    Real.log (d/4) ≤ 2 * Real.sqrt 2 *
      Real.sqrt (Real.log |a| ^ 2 + Real.log |b| ^ 2 + Real.log |c| ^ 2) := by
  by_cases hab : |b| ≤ |a|
  · by_cases hbc : |c| ≤ |b|
    · exact cubic_log_bound_sorted hd hddisc hprod hab hbc
    · have hcb : |b| ≤ |c| := le_of_not_ge hbc
      by_cases hca : |c| ≤ |a|
      · have hdisc' : d ≤ ((a-c)*(a-b)*(c-b))^2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |a*c*b| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hca hcb
        convert h using 1 <;> ring
      · have hac : |a| ≤ |c| := le_of_not_ge hca
        have hdisc' : d ≤ ((c-a)*(c-b)*(a-b))^2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |c*a*b| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hac hab
        convert h using 1 <;> ring
  · have hab' : |a| ≤ |b| := le_of_not_ge hab
    by_cases hac : |c| ≤ |a|
    · have hdisc' : d ≤ ((b-a)*(b-c)*(a-c))^2 := by
        convert hddisc using 1 <;> ring
      have hprod' : |b*a*c| = 1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      have h := cubic_log_bound_sorted hd hdisc' hprod' hab' hac
      convert h using 1 <;> ring
    · have hac' : |a| ≤ |c| := le_of_not_ge hac
      by_cases hcb : |c| ≤ |b|
      · have hdisc' : d ≤ ((b-c)*(b-a)*(c-a))^2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |b*c*a| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hcb hac'
        convert h using 1 <;> ring
      · have hbc : |b| ≤ |c| := le_of_not_ge hcb
        have hdisc' : d ≤ ((c-b)*(c-a)*(b-a))^2 := by
          convert hddisc using 1 <;> ring
        have hprod' : |c*b*a| = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
        have h := cubic_log_bound_sorted hd hdisc' hprod' hbc hab'
        convert h using 1 <;> ring
end Cusick
