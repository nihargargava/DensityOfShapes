import ABCBoundedFrames

/-!
# Compactness of the normalized ABC frames

This file isolates the paper's compactness step: the normalized logarithmic
frames lie in a fixed coordinate box, hence admit a convergent subsequence.
Continuity of the determinant shows that the matrix limit is again in
`SL(2, ℝ)`.  No formula for the limit is used.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCCompactness

open Filter Set Topology
open ABCBoundedFrames

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The fixed coordinate box containing every normalized ABC frame. -/
def frameBox : Set Mat2R :=
  (Set.Icc (-6 : ℝ) 6).matrix

lemma frameBox_isCompact : IsCompact frameBox :=
  IsCompact.matrix isCompact_Icc

lemma coe_baseFrame_mem_frameBox (N : ℕ) :
    (baseFrame N : Mat2R) ∈ frameBox := by
  rw [frameBox, Set.mem_matrix]
  intro i j
  exact abs_le.mp (baseFrame_entry_abs_le N i j)

private instance : FirstCountableTopology Mat2R :=
  inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))

/-- In dimension two, determinant one makes the inverse an entrywise signed
permutation of the original matrix.  Thus the same uniform bound holds for
the inverse frames, as asserted in the paper. -/
lemma coe_baseFrame_inv_entry_abs_le (N : ℕ) (i j : Fin 2) :
    |((↑((baseFrame N)⁻¹) : Mat2R) i j)| ≤ 6 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact baseFrame_entry_abs_le N 1 1
  · change |-((↑(baseFrame N) : Mat2R) 0 1)| ≤ 6
    simpa only [abs_neg] using baseFrame_entry_abs_le N 0 1
  · change |-((↑(baseFrame N) : Mat2R) 1 0)| ≤ 6
    simpa only [abs_neg] using baseFrame_entry_abs_le N 1 0
  · exact baseFrame_entry_abs_le N 0 0

/-- The paper-faithful compactness conclusion: the normalized ABC frames
have a convergent strictly monotone subsequence.  The limit is deliberately
left unidentified. -/
theorem exists_baseFrame_convergent_subsequence :
    ∃ (limitFrame : SL2R) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        Tendsto (baseFrame ∘ subseq) atTop (nhds limitFrame) := by
  obtain ⟨M, hM, subseq, hsubseq, hMlim⟩ :=
    frameBox_isCompact.tendsto_subseq
      (x := fun N ↦ (baseFrame N : Mat2R)) coe_baseFrame_mem_frameBox
  have hdetlim :
      Tendsto (fun N ↦ ((baseFrame (subseq N) : Mat2R).det)) atTop
        (nhds M.det) := by
    exact ((continuous_id.matrix_det).tendsto M).comp hMlim
  have hdetone :
      Tendsto (fun N ↦ ((baseFrame (subseq N) : Mat2R).det)) atTop
        (nhds (1 : ℝ)) := by
    simpa only [(baseFrame _).property] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  have hdet : M.det = 1 := tendsto_nhds_unique hdetlim hdetone
  let limitFrame : SL2R := ⟨M, hdet⟩
  refine ⟨limitFrame, subseq, hsubseq, ?_⟩
  apply tendsto_subtype_rng.2
  change Tendsto ((fun N ↦ (↑(baseFrame N) : Mat2R)) ∘ subseq) atTop (nhds M)
  exact hMlim

end ABCCompactness
end CubicPeriodicTori
