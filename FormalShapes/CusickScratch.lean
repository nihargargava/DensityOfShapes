import CusickRegulator

namespace Cusick

lemma cubic_factor_nonneg_le_two {v w : ℝ}
    (hv : v ∈ Set.Icc (-1 : ℝ) 1) (hw : w ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ (1 - v) * (1 - w) * (1 - v * w) ∧
      (1 - v) * (1 - w) * (1 - v * w) ≤ 2 := by
  have hv1 : 0 ≤ 1 - v := by linarith [hv.2]
  have hw1 : 0 ≤ 1 - w := by linarith [hw.2]
  have hvw : v * w ≤ 1 := by
    calc
      v * w ≤ |v * w| := le_abs_self _
      _ = |v| * |w| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (abs_le.mpr hv) (abs_le.mpr hw)
        (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  constructor
  · positivity
  · by_cases hw0 : 0 ≤ w
    · have haux : (1 - v) * (1 - v * w) ≤ 2 * (1 + w) := by
        have hnon : 0 ≤ (v + 1) * (1 + 2 * w - v * w) := by
          apply mul_nonneg
          · linarith [hv.1]
          · nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hv.2)]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left haux hw1
      nlinarith [sq_nonneg w]
    · by_cases hv0 : 0 ≤ v
      · have haux : (1 - w) * (1 - w * v) ≤ 2 * (1 + v) := by
          have hnon : 0 ≤ (w + 1) * (1 + 2 * v - w * v) := by
            apply mul_nonneg
            · linarith [hw.1]
            · nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hw.2)]
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left haux hv1
        nlinarith [sq_nonneg v]
      · have hv0' : v ≤ 0 := le_of_not_ge hv0
        have hw0' : w ≤ 0 := le_of_not_ge hw0
        have hab : (1 - v) * (1 - w) ≤ 2 * (1 + v * w) := by
          nlinarith [mul_nonneg (by linarith [hv.1] : 0 ≤ 1 + v)
            (by linarith [hw.1] : 0 ≤ 1 + w)]
        have habpos : 0 ≤ 1 - v * w := by nlinarith
        have hmul := mul_le_mul_of_nonneg_right hab habpos
        nlinarith [sq_nonneg (v * w)]

end Cusick
