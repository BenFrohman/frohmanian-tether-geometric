/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.SymplecticTether

/-!
# Velocity-slot tether kernel `TetherKernelVel`

`𝔗_vel(F,G) = -κ ‖ω‖² ∫ ⟨Π_u curl(δF/δω), Π_u curl(δG/δω)⟩`.

In the vorticity pairing the Gâteaux representative of kinetic energy is the
stream function `ψ`, and `curl ψ = u`. The velocity slot therefore feeds `u`
into `Π_u`, and `Π_u u = 0` gives C2. The ψ-slot `TetherKernel` projects `ψ`
itself, which is not parallel to `u` in general (two-mode shear, commit
`a52c6af` of `frohmanian-symplectic-tether-regularity`).

**Open identification.** `curl (FunctionalDerivative H ω) = u` is NOT proved
from this repo's definitions (it needs existence and uniqueness of the Gâteaux
representative of `KineticEnergyHamiltonian` plus Biot–Savart calculus). It is
the named hypothesis `KineticEnergyCurlIdentification`, listed in `NAMING.md`.

C2 holding is exactly what makes `𝔗_vel(M,H) = 0` by symmetry, so this kernel
contributes nothing to the enstrophy balance: it gives consistency, not damping.
-/

@[expose] public section
open InnerProductSpace NavierStokes3D ArnoldGeometric MeasureTheory ForMathlib

namespace FrohmanianTether

/-- Velocity-slot tether kernel: `Π_u` applied to `curl (δF/δω)`. -/
public noncomputable def TetherKernelVel (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  -kappa * Enstrophy ω * ∫ x,
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) (curl (FunctionalDerivative F ω)) x)
        (Pi_u (velocity_from_vorticity ω) (curl (FunctionalDerivative G ω)) x)
    ∂volume

/-- **Named open hypothesis.** The curl of the encoded functional derivative of
kinetic energy is the Biot–Savart velocity (`curl ψ = u`). Not proved here. -/
public def KineticEnergyCurlIdentification (ω : CoadjointOrbit) : Prop :=
  curl (FunctionalDerivative KineticEnergyHamiltonian ω) = velocity_from_vorticity ω

/-- The velocity-slot kernel is symmetric. -/
public theorem tetherKernelVel_comm (ω : CoadjointOrbit) (F G : Functional) :
    TetherKernelVel ω F G = TetherKernelVel ω G F := by
  unfold TetherKernelVel
  congr 2
  funext x
  exact real_inner_comm _ _

/-- `Π_u u = 0` almost everywhere for every finite-energy `u` (no energy ≠ 0
side condition): energy ≠ 0 is `projection_orthogonal_to_u`; energy = 0 forces
`u = 0` a.e. -/
public theorem Pi_u_self_ae_zero (u : VelocityField) (hdiv : ∀ x, div u x = 0)
    (hInt : Integrable (fun y => ‖u y‖ ^ 2)) :
    Pi_u u u =ᵐ[volume] 0 := by
  by_cases hE : (∫ y, ‖u y‖ ^ 2 ∂volume) ≠ 0
  · rw [projection_orthogonal_to_u u hdiv hE]
  · simp only [ne_eq, not_not] at hE
    have hnn : ∀ y, 0 ≤ ‖u y‖ ^ 2 := fun _ => pow_nonneg (norm_nonneg _) _
    have hae : (fun y => ‖u y‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg hnn hInt).mp hE
    exact hae.mono fun x hx => by
      have hx0 : u x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa using hx))
      simp [Pi_u, hx0]

/-- **C2 for the velocity-slot kernel**, with `H` in the left slot. Conditional
only on the named identification `curl (δH/δω) = u`, plus the standing
`div u = 0` and finite kinetic energy already used for the ψ-slot C2. -/
public theorem tetherKernelVel_C2 (ω : CoadjointOrbit) (G : Functional)
    (hcurl : KineticEnergyCurlIdentification ω)
    (hdiv : ∀ x, div (velocity_from_vorticity ω) x = 0)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2)) :
    TetherKernelVel ω KineticEnergyHamiltonian G = 0 := by
  unfold TetherKernelVel
  rw [show curl (FunctionalDerivative KineticEnergyHamiltonian ω) =
      velocity_from_vorticity ω from hcurl]
  have hker :
      (fun x =>
          inner ℝ
            (Pi_u (velocity_from_vorticity ω) (velocity_from_vorticity ω) x)
            (Pi_u (velocity_from_vorticity ω) (curl (FunctionalDerivative G ω)) x))
        =ᵐ[volume] 0 :=
    (Pi_u_self_ae_zero _ hdiv hInt).mono fun x hx => by
      simp [hx]
  rw [integral_congr_ae hker]
  simp

/-- C2 in the right slot, by symmetry. -/
public theorem tetherKernelVel_C2_right (ω : CoadjointOrbit) (F : Functional)
    (hcurl : KineticEnergyCurlIdentification ω)
    (hdiv : ∀ x, div (velocity_from_vorticity ω) x = 0)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2)) :
    TetherKernelVel ω F KineticEnergyHamiltonian = 0 := by
  rw [tetherKernelVel_comm]
  exact tetherKernelVel_C2 ω F hcurl hdiv hInt

/-- `DegenerateWRTKineticEnergy TetherKernelVel` under the identifications. -/
public theorem tetherKernelVel_degenerate
    (hcurl : ∀ ω, KineticEnergyCurlIdentification ω)
    (hdiv : ∀ ω x, div (velocity_from_vorticity ω) x = 0)
    (hInt : ∀ ω, Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2)) :
    DegenerateWRTKineticEnergy TetherKernelVel :=
  fun F ω => tetherKernelVel_C2_right ω F (hcurl ω) (hdiv ω) (hInt ω)

end FrohmanianTether

end

#print axioms FrohmanianTether.Pi_u_self_ae_zero
#print axioms FrohmanianTether.tetherKernelVel_C2
#print axioms FrohmanianTether.tetherKernelVel_C2_right
#print axioms FrohmanianTether.tetherKernelVel_degenerate
