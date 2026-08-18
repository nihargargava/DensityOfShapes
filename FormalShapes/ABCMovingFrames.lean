import ABCCompactness

/-!
# The fixed change of basis and the paper's moving frames

The final paragraph of Dang--Gargava--Li multiplies the bounded ABC unit
frame `g_N` by the fixed matrix `g` from Lemma 5.1.  This file records that
factorization and transfers the compactness subsequence to `g_N g`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCMovingFrames

open Filter Topology
open ABCBoundedFrames ABCCompactness

/-- The fixed integral exponent change from Lemma 5.1, over `ℝ`. -/
def exponentChangeReal : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-8, 16; -16, 8]

lemma exponentChangeReal_eq :
    exponentChangeReal = !![-8, 16; -16, 8] := by
  rfl

lemma exponentChangeReal_det : exponentChangeReal.det = 192 := by
  rw [exponentChangeReal_eq, Matrix.det_fin_two]
  norm_num

lemma exponentChangeReal_det_pos : 0 < exponentChangeReal.det := by
  rw [exponentChangeReal_det]
  norm_num

/-- The fixed determinant-one representative of the paper's matrix `g`. -/
def fixedFrame : SL2R :=
  normalizeBasis exponentChangeReal exponentChangeReal_det_pos

/-- The paper's normalized moving frame `g_N g`. -/
def movingFrame (N : ℕ) : SL2R := baseFrame N * fixedFrame

lemma normalize_unitLog_mul_change (N : ℕ) :
    normalizeBasis (unitLogBasis N * exponentChangeReal)
        (by simpa [Matrix.det_mul] using
          mul_pos (unitLogBasis_det_pos N) exponentChangeReal_det_pos) =
      movingFrame N := by
  rw [normalizeBasis_mul]
  rfl

/-- Compactness for the paper's actual frames `g_N g`; the limit remains
unidentified, exactly as in the paper. -/
theorem exists_movingFrame_convergent_subsequence :
    ∃ (limitFrame : SL2R) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        Tendsto (movingFrame ∘ subseq) atTop (nhds limitFrame) := by
  obtain ⟨g₀, φ, hφ, hlim⟩ := exists_baseFrame_convergent_subsequence
  refine ⟨g₀ * fixedFrame, φ, hφ, ?_⟩
  change Tendsto (fun n ↦ baseFrame (φ n) * fixedFrame) atTop
    (nhds (g₀ * fixedFrame))
  exact hlim.mul tendsto_const_nhds

end ABCMovingFrames
end CubicPeriodicTori
