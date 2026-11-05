/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem closing_bound_uniqueness_family_unsatisfiable (ν : ℝ)
    (hKato : ∀ u₀ : VelocityField, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → KatoLocalWitness u₀ ν) :
    ¬ (∀ (u₀ : VelocityField) (w : KatoLocalWitness u₀ ν)
      (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes u₀ ν → v 0 = u₀ → NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) := by
  intro h
  have hd : ∀ x : T3, div (0 : VelocityField) x = 0 := fun x => by simp [div]
  exact library_huniq_unsatisfiable_at_zero ν
    (hKato 0 contDiff_const hd (by simp)) (h 0 _)
