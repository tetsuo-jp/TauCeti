/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Right-continuous functions on dense subsets

A function `g` that is right-continuous at every point before `T` exceeds a level `a` at some
time `t ≤ T` only if it already exceeds `a` at `T` or at some point of a given dense set below `T`.
So the supremum of `g` over `(-∞, T]` is its supremum over `{T} ∪ (D ∩ (-∞, T])`; with `D`
countable, this replaces a supremum over uncountably many times by a countable one.

## Main declarations

* `Dense.exists_mem_insert_inter_Iic_lt`: a value of `g` above `a` at a time `t ≤ T` is matched
  by a value above `a` at `T` or at a point of `D ∩ (-∞, T]`.
* `TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt`: in a separable space, one
  countable set of times `≤ T` serves for every function right-continuous before `T`.
* `exists_seq_rat_tendsto_nhdsGT`: every real is the limit from the right of a sequence of
  rationals.
* `le_of_forall_rat_add_le`: a function right-continuous at `t + h` that does not increase along
  rational increments from `t` does not increase along the real increment `h`.
-/

public section

open Set

variable {ι α : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
  [LinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]

/-- If `g` is right-continuous at every time before `T` and `a < g t` for some `t ≤ T`, then
`a < g s` for some `s` in `{T} ∪ (D ∩ (-∞, T])`, for any dense set `D`. -/
theorem Dense.exists_mem_insert_inter_Iic_lt {D : Set ι} (hD : Dense D) {g : ι → α} {T t : ι}
    (hg : ∀ t < T, ContinuousWithinAt g (Ioi t) t) (htT : t ≤ T) {a : α} (ha : a < g t) :
    ∃ s ∈ insert T (D ∩ Iic T), a < g s := by
  rcases htT.lt_or_eq with htT | rfl
  · obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' htT).1
      ((hg t htT).preimage_mem_nhdsWithin (Ioi_mem_nhds ha))
    obtain ⟨s, hsD, hs⟩ := hD.exists_between (lt_min hu htT)
    exact ⟨s, Or.inr ⟨hsD, hs.2.le.trans (min_le_right _ _)⟩,
      hsub ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩⟩
  · exact ⟨t, mem_insert _ _, ha⟩

/-- In a separable space, every `T` has a countable set `S` of points `≤ T` such that whenever `g`
is right-continuous at every point before `T` and `a < g t` for some `t ≤ T`, also `a < g s` for
some `s ∈ S`. One may take `S = {T} ∪ (D ∩ (-∞, T])` for a countable dense set `D`. -/
theorem TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt [SeparableSpace ι] (T : ι) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧ ∀ ⦃g : ι → α⦄,
      (∀ t < T, ContinuousWithinAt g (Ioi t) t) →
        ∀ ⦃t⦄, t ≤ T → ∀ ⦃a⦄, a < g t → ∃ s ∈ S, a < g s :=
  let ⟨D, hDc, hD⟩ := exists_countable_dense ι
  ⟨insert T (D ∩ Iic T), (hDc.mono inter_subset_left).insert T,
    insert_subset_iff.2 ⟨le_rfl, inter_subset_right⟩,
    fun _ hg _ htT _ ha ↦ hD.exists_mem_insert_inter_Iic_lt hg htT ha⟩

section Rational

open Filter
open scoped Topology

/-- A sequence of rationals converging to a real number from the right. -/
theorem exists_seq_rat_tendsto_nhdsGT (u : ℝ) :
    ∃ r : ℕ → ℚ, (∀ n, u < (r n : ℝ)) ∧ Tendsto (fun n => (r n : ℝ)) atTop (𝓝[>] u) := by
  have hlt : ∀ n : ℕ, ∃ q : ℚ, u < (q : ℝ) ∧ (q : ℝ) < u + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact exists_rat_btwn (by linarith)
  choose r hr₁ hr₂ using hlt
  refine ⟨r, hr₁, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall hr₁)⟩
  have hup : Tendsto (fun n : ℕ => u + 1 / ((n : ℝ) + 1)) atTop (𝓝 (u + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (hr₁ n).le) fun n => (hr₂ n).le

/-- A function that is right-continuous at `t + h` and does not increase along rational
increments from `t` does not increase along the real increment `h ≥ 0`. -/
theorem le_of_forall_rat_add_le {G : ℝ → ℝ} {t h : ℝ} (hh : 0 ≤ h)
    (hG : Tendsto G (𝓝[>] (t + h)) (𝓝 (G (t + h))))
    (hanti : ∀ q : ℚ, 0 ≤ q → G (t + q) ≤ G t) : G (t + h) ≤ G t := by
  obtain ⟨r, hr, hrt⟩ := exists_seq_rat_tendsto_nhdsGT h
  have hid : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 h) := hrt.mono_right nhdsWithin_le_nhds
  have hshift : Tendsto (fun n => t + (r n : ℝ)) atTop (𝓝[>] (t + h)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_nhds.add hid) (Eventually.of_forall fun n => ?_)
    exact mem_Ioi.2 (by linarith [hr n])
  refine le_of_tendsto (hG.comp hshift) (Eventually.of_forall fun n => ?_)
  exact hanti (r n) (by exact_mod_cast (hh.trans (hr n).le))


end Rational
