/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem tetherKernel_degenerates_on_kinetic_energy
    (F : Functional) (ω : CoadjointOrbit)
    (hδH : FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω)
    (hdiv : ∀ x, div (velocity_from_vorticity ω) x = 0)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2)) :
    TetherKernel ω F KineticEnergyHamiltonian = 0 := by
  by_cases hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂volume) ≠ 0
  · have hPi :=
      projection_orthogonal_to_u (velocity_from_vorticity ω) hdiv hE
    apply tetherKernel_of_right_factor_zero
    rw [hδH]
    exact hPi
  · simp only [ne_eq, not_not] at hE
    by_cases hz : velocity_from_vorticity ω = 0
    · apply tetherKernel_of_right_factor_zero
      rw [hδH, hz]
      exact Pi_u_zero (0 : VelocityField)
    · set u := velocity_from_vorticity ω
      unfold TetherKernel
      rw [hδH]
      have hnn : ∀ y, 0 ≤ ‖u y‖ ^ 2 := fun _ => pow_nonneg (norm_nonneg _) _
      have hae : (fun y => ‖u y‖ ^ 2) =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg hnn hInt).mp (by simpa using hE)
      have hu : u =ᵐ[volume] 0 :=
        hae.mono fun x hx =>
          norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa using hx))
      refine mul_eq_zero.mpr (Or.inr ?_)
      have hker :
          (fun x =>
              inner ℝ
                (Pi_u u (FunctionalDerivative F ω) x)
                (Pi_u u u x)) =ᵐ[volume] 0 :=
        hu.mono fun x hx => by simp [Pi_u, hx, inner_zero_right]
      rw [integral_congr_ae hker]
      simp [integral_zero]
