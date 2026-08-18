import main
import Mathlib.Topology.MetricSpace.Sequences

open CubicPeriodicTori

#synth ProperSpace (Fin 2 → Fin 2 → ℝ)
#synth MetricSpace (Fin 2 → Fin 2 → ℝ)
#check tendsto_subseq_of_bounded
#check Metric.isBounded_iff
#check Metric.isBounded_iff_subset_closedBall
#check Bornology.IsBounded.subset_closedBall
#check isBounded_range_iff
#check Metric.isBounded_iff_eventually_le_dist
#check IsCompact.tendsto_subseq
#check tendsto_subtype_rng
#check tendsto_subtype_val_iff
#check tendsto_subtype_iff_val
#check continuous_det
#check continuous_matrix
#synth FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)
#check (isCompact_Icc : IsCompact (Set.Icc (fun _ _ : Fin 2 ↦ (-6 : ℝ)) (fun _ _ ↦ (6 : ℝ))))
#check Continuous.matrix_det
