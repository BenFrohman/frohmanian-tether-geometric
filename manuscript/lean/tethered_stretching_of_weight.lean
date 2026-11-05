/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem tethered_stretching_of_weight
    (ωField uField : VelocityField) (x : T3) (C M : ℝ)
    (hu : DifferentiableAt ℝ uField x)
    (hCZ : ‖fderiv ℝ uField x‖ ≤ C * vorticity_sup_norm ωField)
    (hmax : ‖ωField x‖ = M ∧ M = vorticity_sup_norm ωField)
    (orbit : CoadjointOrbit) (testF : Functional)
    (hweight : M ^ 4 ≤ Enstrophy orbit * ∫ y,
          ‖Pi_u (velocity_from_vorticity orbit)
              (FunctionalDerivative testF orbit) y‖ ^ 2 ∂volume) :
    inner ℝ (ωField x) (convective ωField uField x) +
        TetherKernel orbit testF testF ≤
      (C * M - kappa * M ^ 2) * M ^ 2 := by
  have hpoint : ‖ωField x‖ = vorticity_sup_norm ωField := by
    rw [← hmax.2, hmax.1]
  have hstretch :=
    stretching_inner_le_at_max ωField uField x C hu hCZ hpoint
  have hcubic :
      inner ℝ (ωField x) (convective ωField uField x) ≤ C * M ^ 3 := by
    simpa [hmax.2] using hstretch
  have hker : TetherKernel orbit testF testF =
      -kappa * Enstrophy orbit * ∫ y,
          ‖Pi_u (velocity_from_vorticity orbit)
              (FunctionalDerivative testF orbit) y‖ ^ 2 ∂volume :=
    tetherKernel_quadratic_form testF orbit
  have hkerLe : TetherKernel orbit testF testF ≤ -kappa * M ^ 4 := by
    rw [hker, mul_assoc]
    exact mul_le_mul_of_nonpos_left hweight (neg_nonpos.mpr kappa_pos.le)
  have hsum :
      inner ℝ (ωField x) (convective ωField uField x) +
          TetherKernel orbit testF testF ≤
        C * M ^ 3 + -kappa * M ^ 4 := by
    linarith
  have hrew :
      C * M ^ 3 + -kappa * M ^ 4 = (C * M - kappa * M ^ 2) * M ^ 2 := by
    ring
  exact hsum.trans_eq hrew
