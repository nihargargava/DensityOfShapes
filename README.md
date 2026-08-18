# FormalShapes

This repository contains a Lean 4 autoformalization of Nguyen-Thi Dang,
Nihar Gargava, and Jialun Li's preprint
[“Density of shapes of periodic tori in the cubic case”](https://arxiv.org/abs/2502.12754).

The development checks the paper's main argument and formalizes two major
results on which it depends:

1. **Cusick's regulator bound.** For an order in a totally real cubic number
   field, the regulator is bounded below in terms of the order's
   discriminant. The Lean development proves the version for arbitrary
   cubic orders needed by the preprint, following Cusick's argument.
2. **The banana density lemma.** A closed subset of
   `SL(2, ℝ) / SL(2, ℤ)` that contains the required horospherical segment and
   is invariant under the diagonal group is the whole space. This formalization
   gives a self-contained proof of the expanding-horocycle density statement
   used in the paper.

The formalization also verifies in Lean the finite computations at the
primes `2`, `3`, and `5` that the preprint reports as SageMath calculations.
The main entry point is [`FormalShapes/main.lean`](FormalShapes/main.lean).

The final theorem and its dependencies are **sorry-free**. An axiom audit of
the final theorem reports only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`; it contains no `sorryAx` or project-specific axioms.

The formalization was produced by Codex running with GPT-5.6 Sol Ultra. Codex
was instructed to include detailed comments pointing to the corresponding
results in the rendered preprint to make human review easier.

## Building

The repository pins its Lean toolchain and Mathlib revision. With
[elan](https://github.com/leanprover/elan) and Lake installed, run:

```sh
lake update
lake build
```
