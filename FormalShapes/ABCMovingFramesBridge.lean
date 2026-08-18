import main
import ABCMovingFrames

/-!
# Integration of moving frames with the auxiliary exponent lattices

These lemmas sit downstream of `main`: they identify the fixed literal matrix
used by `ABCMovingFrames` with the exponent change from Lemma 5.1 and factor
the actual suborder logarithm basis.  Keeping them here leaves the compactness
modules acyclic and importable by `main`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCMovingFramesBridge

open Proposition52 ABCBoundedFrames ABCMovingFrames

lemma map_exponentChange :
    exponentChange.map (Int.castRingHom ℝ) = exponentChangeReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentChange, exponentChangeReal]

/-- The integral exponent basis factors as the fixed change followed by the
auxiliary lattice basis, exactly as in the last paragraph of the paper. -/
lemma map_exponentBasis (C D R : ℕ) :
    (exponentBasis C D R).map (Int.castRingHom ℝ) =
      exponentChangeReal * lambdaBasis C D R := by
  rw [exponentBasis, Matrix.map_mul, map_exponentChange]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambdaBasis, congruenceBasis]

lemma unitLog_mul_map_exponentBasis (N C D R : ℕ) :
    unitLogBasis N * (exponentBasis C D R).map (Int.castRingHom ℝ) =
      (unitLogBasis N * exponentChangeReal) * lambdaBasis C D R := by
  rw [map_exponentBasis]
  exact (Matrix.mul_assoc (unitLogBasis N) exponentChangeReal
    (lambdaBasis C D R)).symm

/-- Normalizing the actual suborder log basis gives the action of the moving
frame on the auxiliary shape. -/
lemma normalize_actual_basis (N C D R : ℕ) :
    normalizeBasis
        ((unitLogBasis N * exponentChangeReal) * lambdaBasis C D R)
        (by
          rw [Matrix.det_mul, Matrix.det_mul]
          exact mul_pos
            (mul_pos (unitLogBasis_det_pos N) exponentChangeReal_det_pos)
            (lambdaBasis_det_pos C D R)) =
      movingFrame N *
        normalizeBasis (lambdaBasis C D R) (lambdaBasis_det_pos C D R) := by
  rw [normalizeBasis_mul (unitLogBasis N * exponentChangeReal)
    (lambdaBasis C D R)
    (by
      rw [Matrix.det_mul]
      exact mul_pos (unitLogBasis_det_pos N) exponentChangeReal_det_pos)
    (lambdaBasis_det_pos C D R)]
  rw [normalize_unitLog_mul_change]

end ABCMovingFramesBridge
end CubicPeriodicTori
