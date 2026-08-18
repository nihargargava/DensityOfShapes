import OrderPeriods
import ABCLocalUnits

/-!
# Units and logarithms of the scalar ABC suborders

This file gives the exact order/unit correspondence needed to apply Lemma
2.6 after Propositions 3.4 and 4.3.  A unit of `ℤ + qO` maps to an ambient
unit of `O`; conversely an ambient unit restricts precisely when its value
lies in `ℤ + qO`.  Closure under inversion is the elementary lemma proved
as part of the local-unit argument in `ABCLocalUnits`.
-/

noncomputable section

namespace CubicPeriodicTori
namespace ABCScalarUnits

open ABCOrders ArithmeticConstruction

/-- Inclusion of the scalar suborder induces inclusion of its unit group
into the ambient ABC-order unit group. -/
def ambientUnitMap (P : Parameters) (q : ℕ) :
    (scalarSuborder P q)ˣ →* (orderCarrier P)ˣ :=
  Units.map (scalarSuborder P q).val.toRingHom.toMonoidHom

@[simp] lemma coe_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    ((ambientUnitMap P q x : (orderCarrier P)ˣ) : orderCarrier P) =
      (x : scalarSuborder P q) :=
  rfl

lemma ambientUnitMap_injective (P : Parameters) (q : ℕ) :
    Function.Injective (ambientUnitMap P q) := by
  intro x y hxy
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val hxy

lemma ambientUnitMap_value_mem (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    ((ambientUnitMap P q x : (orderCarrier P)ˣ) : orderCarrier P) ∈
      scalarSuborder P q :=
  (x : scalarSuborder P q).property

/-- Restriction of an ambient unit whose value lies in the scalar suborder.
The inverse belongs to the scalar suborder by the inversion step of
Proposition 4.4. -/
def restrictUnit (P : Parameters) (q : ℕ) (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    (scalarSuborder P q)ˣ where
  val := ⟨x, hx⟩
  inv := ⟨((x⁻¹ : (orderCarrier P)ˣ) : orderCarrier P),
    (ABCLocalUnits.unit_inv_mem_scalarSuborder_iff P q x).2 hx⟩
  val_inv := by
    apply Subtype.ext
    exact x.val_inv
  inv_val := by
    apply Subtype.ext
    exact x.inv_val

@[simp] lemma coe_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    ((restrictUnit P q x hx : (scalarSuborder P q)ˣ) :
      scalarSuborder P q) = ⟨x, hx⟩ :=
  rfl

@[simp] lemma ambientUnitMap_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    ambientUnitMap P q (restrictUnit P q x hx) = x := by
  apply Units.ext
  rfl

@[simp] lemma restrictUnit_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    restrictUnit P q (ambientUnitMap P q x)
      (ambientUnitMap_value_mem P q x) = x := by
  apply Units.ext
  rfl

/-- Exact characterization of the range of unit inclusion. -/
theorem mem_range_ambientUnitMap_iff (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ) :
    x ∈ Set.range (ambientUnitMap P q) ↔
      (x : orderCarrier P) ∈ scalarSuborder P q := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ambientUnitMap_value_mem P q y
  · intro hx
    exact ⟨restrictUnit P q x hx, ambientUnitMap_restrictUnit P q x hx⟩

/-- Ambient units whose values lie in `ℤ + qO`. -/
def ambientUnitsInScalarSuborder (P : Parameters) (q : ℕ) :
    Subgroup (orderCarrier P)ˣ where
  carrier := {x | (x : orderCarrier P) ∈ scalarSuborder P q}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    exact (scalarSuborder P q).mul_mem hx hy
  inv_mem' := by
    intro x hx
    exact (ABCLocalUnits.unit_inv_mem_scalarSuborder_iff P q x).2 hx

@[simp] lemma mem_ambientUnitsInScalarSuborder_iff
    (P : Parameters) (q : ℕ) (x : (orderCarrier P)ˣ) :
    x ∈ ambientUnitsInScalarSuborder P q ↔
      (x : orderCarrier P) ∈ scalarSuborder P q :=
  Iff.rfl

/-- Units of the scalar suborder are exactly the ambient units whose values
belong to that suborder. -/
def unitsEquivAmbientUnitsInScalarSuborder (P : Parameters) (q : ℕ) :
    (scalarSuborder P q)ˣ ≃*
      ambientUnitsInScalarSuborder P q where
  toFun x := ⟨ambientUnitMap P q x, ambientUnitMap_value_mem P q x⟩
  invFun x := restrictUnit P q x x.property
  left_inv x := by
    apply Units.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    exact ambientUnitMap_restrictUnit P q x x.property
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (ambientUnitMap P q) x y

@[simp] lemma unitsEquivAmbientUnitsInScalarSuborder_apply
    (P : Parameters) (q : ℕ) (x : (scalarSuborder P q)ˣ) :
    (unitsEquivAmbientUnitsInScalarSuborder P q x : (orderCarrier P)ˣ) =
      ambientUnitMap P q x :=
  rfl

/-- Unit logarithms are unchanged by inclusion into the ambient ABC order. -/
lemma unitLog_ambientUnitMap (P : Parameters) (q : ℕ)
    (x : (scalarSuborder P q)ˣ) :
    OrderPeriods.unitLog (scalarSuborderEmbedding P q) x =
      OrderPeriods.unitLog (orderEmbedding P) (ambientUnitMap P q x) :=
  rfl

/-- The same compatibility in the restriction direction. -/
lemma unitLog_restrictUnit (P : Parameters) (q : ℕ)
    (x : (orderCarrier P)ˣ)
    (hx : (x : orderCarrier P) ∈ scalarSuborder P q) :
    OrderPeriods.unitLog (scalarSuborderEmbedding P q)
        (restrictUnit P q x hx) =
      OrderPeriods.unitLog (orderEmbedding P) x :=
  rfl

/-- The displayed scalar-suborder basis starts with `1`, as required by the
converse direction of the matrix period criterion. -/
lemma scalarSuborderBasis_zero (P : Parameters) (q : ℕ) (hq : q ≠ 0) :
    scalarSuborderBasis P q hq 0 = 1 := by
  rw [scalarSuborderBasis_apply]
  rfl

/-- Every restricted real embedding is injective. -/
lemma scalarSuborderEmbedding_injective (P : Parameters) (q : ℕ)
    (i : Fin 3) :
    Function.Injective (scalarSuborderEmbedding P q i) := by
  intro x y hxy
  apply Subtype.ext
  exact ((rootEmbedding P i).injective.comp
    (FaithfulSMul.algebraMap_injective (orderCarrier P) (ABCField P))) hxy

/-- The particular injectivity fact requested by `OrderPeriods`. -/
lemma scalarSuborderEmbedding_zero_injective (P : Parameters) (q : ℕ) :
    Function.Injective (scalarSuborderEmbedding P q 0) :=
  scalarSuborderEmbedding_injective P q 0

end ABCScalarUnits
end CubicPeriodicTori
