import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

#print Matrix.map
#print Matrix.map_apply

example (q : ℕ) (M : Matrix (Fin 3) (Fin 3) ℤ) (i j) :
    M.map (Int.castRingHom (ZMod q)) i j = (M i j : ZMod q) := by
  rfl

def cm : Matrix (Fin 3) (Fin 3) ℤ :=
  ![![0, 0, 1], ![1, 0, 0], ![0, 1, 1]]

def cmq (q : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod q) :=
  ![![0, 0, 1], ![1, 0, 0], ![0, 1, 1]]

example (q : ℕ) : cm.map (Int.castRingHom (ZMod q)) = cmq q := by
  unfold cm cmq Matrix.map Matrix.of
  ext ⟨i, hi⟩ ⟨j, hj⟩
  interval_cases i <;> interval_cases j <;> dsimp
