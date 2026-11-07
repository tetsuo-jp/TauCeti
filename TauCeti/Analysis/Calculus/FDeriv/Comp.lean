/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Abel

/-!
# Derivatives under composition and changes of coordinates

By the chain rule, the differential of `f ∘ φ` at `b` is the differential of `f` at `φ b`
precomposed with that of `φ` at `b`. When the latter is invertible, one vanishes exactly when the
other does, so criticality does not depend on the coordinates.

At a fixed point of a map preserving the germ of `f`, the derivative of `f` is unchanged by
precomposition with the derivative of that map.

## Main results

* `HasFDerivAt.comp_eq_of_eventuallyEq`: invariance of a germ at a fixed point implies invariance
  of its derivative.
* `TauCeti.fderiv_comp_eq_zero_iff_of_isInvertible`: `b` is a critical point of `f ∘ φ` exactly
  when `φ b` is a critical point of `f`, if the differential of `φ` at `b` is invertible.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- If a map fixes `x` and preserves the germ of `f` there, its derivative preserves the
derivative of `f` by precomposition. -/
theorem _root_.HasFDerivAt.comp_eq_of_eventuallyEq {f : E → F} {f' : E →L[𝕜] F}
    {φ : E → E} {φ' : E →L[𝕜] E} {x : E} (hf : HasFDerivAt f f' x)
    (hφ : HasFDerivAt φ φ' x) (hfix : φ x = x)
    (hinv : f ∘ φ =ᶠ[nhds x] f) : f'.comp φ' = f' := by
  have hfφ : HasFDerivAt f f' (φ x) := by simpa only [hfix] using hf
  exact (hfφ.comp x hφ).unique (hf.congr_of_eventuallyEq hinv)

/-- **Criticality does not depend on the coordinates.** If `f` is differentiable at `φ b`, `φ` is
differentiable at `b`, and the differential of `φ` at `b` is invertible, then `b` is a critical
point of `f ∘ φ` exactly when `φ b` is a critical point of `f`. -/
theorem fderiv_comp_eq_zero_iff_of_isInvertible {f : E → G} {φ : F → E} {b : F}
    (hf : DifferentiableAt 𝕜 f (φ b)) (hφ : DifferentiableAt 𝕜 φ b)
    (hinv : (fderiv 𝕜 φ b).IsInvertible) :
    fderiv 𝕜 (f ∘ φ) b = 0 ↔ fderiv 𝕜 f (φ b) = 0 := by
  obtain ⟨e, he⟩ := hinv
  -- The differential of `f ∘ φ` at `b` is that of `f` at `φ b` precomposed with the equivalence
  -- `e`, so one vanishes exactly when the other does.
  rw [fderiv_comp (x := b) hf hφ, ← he]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; ext u; simp⟩
  ext u
  simpa using congrArg (fun L : F →L[𝕜] G ↦ L (e.symm u)) h

/-- Precomposing a real-valued function with scalar multiplication scales the norm of its
Fréchet derivative by the absolute value of the scalar. -/
theorem norm_fderiv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (a : ℝ) (x : E) :
    ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ = |a| * ‖fderiv ℝ f (a • x)‖ := by
  rw [_root_.fderiv_comp_smul a, norm_smul, Real.norm_eq_abs]

end TauCeti

namespace ContinuousLinearMap

open Function
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℝ G₂]

/-- A critical point of a map yields a critical point of its slice along a level set of a
functional `φ`. Precisely, let `(φ, ρ)` split `F` as `ℝ × G`, let `γ` parametrize a family of
points along which `φ ∘ f` is locally constant, and let `φ ∘ Df` be nonzero at `γ z`. If
`ρ ∘ f ∘ γ` has surjective derivative at `z`, then `Df` is surjective at `γ z`; equivalently, if
`γ z` is critical for `f`, then `z` is critical for the slice `ρ ∘ f ∘ γ`. -/
theorem surjective_fderiv_of_surjective_fderiv_comp {f : E → F} {γ : G₁ → E} {z : G₁} {c : ℝ}
    (φ : F →L[ℝ] ℝ) (ρ : F →L[ℝ] G₂) (eF : F ≃L[ℝ] ℝ × G₂) (heF : ∀ w, eF w = (φ w, ρ w))
    (hγ : DifferentiableAt ℝ γ z) (hf : DifferentiableAt ℝ f (γ z))
    (hconst : (fun w ↦ φ (f (γ w))) =ᶠ[𝓝 z] fun _ ↦ c)
    (hne : ∃ v, φ (fderiv ℝ f (γ z) v) ≠ 0)
    (hs : Surjective (fderiv ℝ (fun w ↦ ρ (f (γ w))) z)) : Surjective (fderiv ℝ f (γ z)) := by
  set T : G₁ →L[ℝ] E := fderiv ℝ γ z
  set A : E →L[ℝ] F := fderiv ℝ f (γ z)
  have hT : HasFDerivAt γ T z := hγ.hasFDerivAt
  have hA : HasFDerivAt f A (γ z) := hf.hasFDerivAt
  have hGd : HasFDerivAt (fun w ↦ ρ (f (γ w))) (ρ.comp (A.comp T)) z :=
    ρ.hasFDerivAt.comp z (hA.comp z hT)
  have hzero : ∀ w : G₁, φ (A (T w)) = 0 := by
    have hd : HasFDerivAt (fun w ↦ φ (f (γ w))) (φ.comp (A.comp T)) z :=
      φ.hasFDerivAt.comp z (hA.comp z hT)
    have hzero' : φ.comp (A.comp T) = 0 :=
      (hd.congr_of_eventuallyEq hconst.symm).unique (hasFDerivAt_const c z)
    intro w
    simpa using congrArg (fun B : G₁ →L[ℝ] ℝ ↦ B w) hzero'
  have hker : ∀ y, φ y = 0 → ∃ u, A u = y := by
    intro y hy
    obtain ⟨w, hw⟩ := hs (ρ y)
    rw [hGd.fderiv] at hw
    refine ⟨T w, eF.injective ?_⟩
    rw [heF, heF, hzero w, hy]
    exact Prod.ext rfl hw
  obtain ⟨v, hv⟩ := hne
  intro w
  obtain ⟨u, hu⟩ := hker (w - (φ w / φ (A v)) • A v) (by simp [div_mul_cancel₀ _ hv])
  refine ⟨u + (φ w / φ (A v)) • v, ?_⟩
  rw [map_add, map_smul, hu]
  abel

end ContinuousLinearMap
