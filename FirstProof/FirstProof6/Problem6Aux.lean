/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FirstProof.FirstProof6.Auxiliary.LaplacianBasics
import FirstProof.FirstProof6.Auxiliary.BarrierPotential
import FirstProof.FirstProof6.Auxiliary.ResolventBound
import FirstProof.FirstProof6.Auxiliary.OneSidedBarrier
import FirstProof.FirstProof6.Auxiliary.ColoringFramework
import FirstProof.FirstProof6.Auxiliary.LoewnerPullback
import FirstProof.FirstProof6.Auxiliary.DynamicColoring

/-!
# Problem 6: Large epsilon-light vertex subsets -- Barrel Import

This file re-exports all sub-modules from `FirstProof6/Auxiliary/`.
All proven infrastructure (no sorry) lives in the sub-files.

## Main definitions

All definitions are re-exported from sub-modules:
- `Problem6.graphLaplacian`: Graph Laplacian matrix
- `Problem6.inducedLaplacian`: Induced subgraph Laplacian
- `Problem6.IsEpsLight`: epsilon-lightness predicate
- `Problem6.barrierPotential`: BSS barrier potential
- `Problem6.PartialColoring`: Partial vertex coloring
-/
