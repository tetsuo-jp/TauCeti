/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Spheres and balls in pseudo-metric spaces

A sphere of positive radius `r < R` lies in the open ball of radius `R` about the same centre
(`Metric.sphere_abs_subset_ball`); the radius is written `|r|`, as in circle integrals.

Along `atTop ×ˢ 𝓝 x`, a radius sequence tending to zero plus the distance to `x` eventually
stays below any positive `r` (`Metric.eventually_add_dist_lt_of_tendsto_zero`), so the closed
balls of those radii about the points near `x` eventually lie in `ball x r`.
-/

public section

open Metric

/-- A sphere of positive radius `r < R` lies in the open ball of radius `R` about the same
centre; the radius is written `|r|`, as in circle integrals. -/
theorem Metric.sphere_abs_subset_ball {X : Type*} [PseudoMetricSpace X] {x : X} {r R : ℝ}
    (hr : r ∈ Set.Ioo 0 R) : sphere x |r| ⊆ ball x R := by
  rw [abs_of_pos hr.1]
  exact sphere_subset_ball hr.2

open Filter Topology in
/-- Eventually along `atTop ×ˢ 𝓝 x`, a radius sequence tending to zero plus the distance to `x`
stays below any positive `r`. -/
theorem Metric.eventually_add_dist_lt_of_tendsto_zero {X : Type*} [PseudoMetricSpace X] {x : X}
    {r : ℝ} (hr : 0 < r) {rho : ℕ → ℝ} (hrho : Tendsto rho atTop (𝓝 0)) :
    ∀ᶠ p : ℕ × X in atTop ×ˢ 𝓝 x, rho p.1 + dist p.2 x < r := by
  have ht : Tendsto (fun p : ℕ × X => rho p.1 + dist p.2 x)
      (atTop ×ˢ 𝓝 x) (𝓝 (0 + dist x x)) :=
    (hrho.comp tendsto_fst).add
      (((continuous_id.dist continuous_const).tendsto x).comp tendsto_snd)
  have ht0 : Tendsto (fun p : ℕ × X => rho p.1 + dist p.2 x)
      (atTop ×ˢ 𝓝 x) (𝓝 0) := by simpa only [dist_self, zero_add] using ht
  exact (tendsto_order.1 ht0).2 r hr
