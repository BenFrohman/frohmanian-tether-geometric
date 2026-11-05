/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem frohmanian_tether_theorem
    (hKato : ∀ u₀ ν, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → 0 < ν →
      KatoLocalWitness u₀ ν)
    (hDI : ∀ u₀ ν, FrohmanianTetherRate u₀ ν)
    (τ : ℝ) (hτ : 0 < τ)
    (hTlb : ∀ u₁ ν (hsm : ContDiff ℝ (⊤ : ℕ∞) u₁)
      (hdiv : ∀ x, div u₁ x = 0)
      (hE : Integrable (fun x : T3 => ‖u₁ x‖ ^ 2))
      (hν : 0 < ν),
      τ ≤ (hKato u₁ ν hsm hdiv hE hν).T)
    (hInt : ∀ u₀ ν (_hν : 0 < ν) (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : T3 => ‖v t x‖ ^ 2))
    (huniq_shift : ∀ u₀ ν (_hν : 0 < ν) (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (w' : KatoLocalWitness (v t) ν),
          ∀ s ∈ Set.Icc (0 : ℝ) w'.T, v (t + s) = w'.u s)
    (huniq : ∀ u₀ ν (w : KatoLocalWitness u₀ ν),
      ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
        T' ∈ existenceTimes u₀ ν →
        v 0 = u₀ →
        NS_PDE v q ν →
        (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
        IsPhysicalNSSolution v →
        ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) :
  ∃ (𝔗_F : CoadjointOrbit → Functional → Functional → ℝ),
    (∀ F ω,
      FunctionalDerivative KineticEnergyHamiltonian ω =
          velocity_from_vorticity ω →
      (∀ x, div (velocity_from_vorticity ω) x = 0) →
      Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) →
      TetheredBracket F KineticEnergyHamiltonian ω =
