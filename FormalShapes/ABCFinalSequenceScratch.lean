import main
import ABCBoundedFrames
import ABCFundamentalUnits
import ABCMovingFrames

/-!
# The final compactness subsequence

This scratch file isolates the reindexing in the last paragraph of the
paper.  We first use compactness to choose a convergent subsequence of the
moving frames `g_N g`, and only then discard its first term so that the
explicit harmless threshold in Proposition 3.4 applies.  In particular, no
formula for the limiting frame is used.

The period-realization statement assembled from Lemma 2.6, Proposition 4.4,
and Lemma 5.1 is left as the hypothesis `hrealizes`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCFinalSequenceScratch

open Filter Topology
open ABCOrders
open ABCOrders.FundamentalUnits
open ABCBoundedFrames ABCMovingFrames

/-- The abstract arithmetic-to-period bridge still needed after the
fundamental-unit and local calculations.  The fundamental-family hypothesis
is included explicitly so that the final construction really invokes
Proposition 3.4 rather than bypassing it. -/
def SelectedABCRealizes : Prop :=
  ∀ (N C D R : ℕ),
    1 ≤ N →
    (cubicOrder (parameters N)).IsFundamentalFamily
      (candidateUnitFamily (parameters N)) →
    C + 4 ≤ N + 1 → D + 2 ≤ N + 1 → R + 1 ≤ N + 1 →
      movingFrame N • Proposition52.lambdaShape C D R ∈ periodicTorusShapes

/-- The final sequence required by `ArithmeticRealization`, conditional only
on the period-realization bridge.  The frame and its limit are obtained by
the compactness/subsequence argument of the paper. -/
theorem exists_arithmeticRealization_of_selectedABCRealizes
    (hrealizes : SelectedABCRealizes) :
    ∃ realization : ArithmeticRealization,
      ∀ n,
        (cubicOrder (parameters
          ((fun k ↦ realization.level k - 1) n))).IsFundamentalFamily
          (candidateUnitFamily (parameters
            ((fun k ↦ realization.level k - 1) n))) := by
  obtain ⟨limitFrame, subseq, hsubseq, hframe⟩ :=
    exists_movingFrame_convergent_subsequence

  -- Discard the first selected term.  This preserves convergence and makes
  -- every retained CRT index at least one, as required by the explicit
  -- regulator-comparison threshold.
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

  have hfundamental : ∀ n,
      (cubicOrder (parameters (selected n))).IsFundamentalFamily
        (candidateUnitFamily (parameters (selected n))) := by
    intro n
    obtain ⟨ha, hgap⟩ :=
      parameters_logs_gt_ten (selected n) (hselected_one n)
    exact candidateUnitFamily_isFundamental_of_large
      (parameters (selected n)) ha hgap

  let realization : ArithmeticRealization := {
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
      exact hrealizes (selected n) C D R (hselected_one n)
        (hfundamental n) hC hD hR
  }

  refine ⟨realization, ?_⟩
  intro n
  have hlevel_eq : realization.level n = selected n + 1 := rfl
  have hindex : realization.level n - 1 = selected n := by
    rw [hlevel_eq]
    omega
  change (cubicOrder (parameters (realization.level n - 1))).IsFundamentalFamily
    (candidateUnitFamily (parameters (realization.level n - 1)))
  rw [hindex]
  exact hfundamental n

end ABCFinalSequenceScratch
end CubicPeriodicTori
