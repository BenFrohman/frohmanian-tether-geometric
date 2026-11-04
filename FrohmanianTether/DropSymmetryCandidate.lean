/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import FrohmanianTether.SymplecticTether

/-!
# Drop-symmetry candidate tether

Candidate `T(F,G) = -κ ‖ω‖² ∫ ⟨Π_u δF × e, Π_u δG⟩`, `e = ω/|ω|`.

* The candidate is antisymmetric, so `T(F,F) = 0`: an antisymmetric `T` gives **no
  dissipation** on any functional.
* C2 (`T(H,·) = 0`) holds under the hypothesis `δH/δω = u` (same suspect hypothesis as the
  symmetric kernel: the true Gateaux representative of `½∫|BS ω|²` is the stream function ψ).
* With C2 and antisymmetry, `T(M,H) = 0` for every `M`: no damping on `‖ω‖_∞` either.
* `e` is `|ω|⁻¹ • ω`, which Lean sets to `0` where `ω = 0` (no canonical direction there).

No Navier–Stokes regularity statement is made.
-/

@[expose] public section

open InnerProductSpace NavierStokes3D ArnoldGeometric MeasureTheory ForMathlib

namespace FrohmanianTether.DropSymmetry

/-- Unit vector along vorticity; `0` where `ω x = 0` (convention `0⁻¹ = 0`). -/
noncomputable def unitVorticity (ω : CoadjointOrbit) (x : T3) : EuclideanSpace ℝ (Fin 3) :=
  ‖ω.val x‖⁻¹ • ω.val x

/-- The drop-symmetry candidate kernel. -/
noncomputable def CrossTetherKernel (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  -kappa * Enstrophy ω * ∫ x,
      inner ℝ
        (cross (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
          (unitVorticity ω x))
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
    ∂volume

/-- Pointwise: `⟨a × e, b⟩ = -⟨b × e, a⟩`. -/
theorem inner_cross_antisymm (a b e : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross a e) b = -inner ℝ (cross b e) a := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, crossProduct]
  simp [real_inner_eq_re_inner, Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm,
    conj_trivial]
  ring

theorem crossTetherKernel_antisymm (ω : CoadjointOrbit) (F G : Functional) :
    CrossTetherKernel ω F G = -CrossTetherKernel ω G F := by
  unfold CrossTetherKernel
  conv_lhs => arg 2; arg 2; ext x; rw [inner_cross_antisymm]
  rw [integral_neg]
  ring

/-- Antisymmetry kills the diagonal: no dissipation. -/
theorem crossTetherKernel_diag (ω : CoadjointOrbit) (F : Functional) :
    CrossTetherKernel ω F F = 0 := by
  have := crossTetherKernel_antisymm ω F F
  linarith

/-- C2 for the candidate, under the (suspect) hypothesis `δH/δω = u`. -/
theorem crossTetherKernel_H_left (ω : CoadjointOrbit) (G : Functional)
    (hδH : FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω)
    (hdiv : ∀ x, div (velocity_from_vorticity ω) x = 0)
    (hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂volume) ≠ 0) :
    CrossTetherKernel ω KineticEnergyHamiltonian G = 0 := by
  have hPi := projection_orthogonal_to_u (velocity_from_vorticity ω) hdiv hE
  unfold CrossTetherKernel
  rw [hδH, hPi]
  have h0 : ∀ e : EuclideanSpace ℝ (Fin 3), cross 0 e = 0 := by
    intro e; simp [cross]
  simp [h0]

/-- C2 + antisymmetry ⇒ `T(M,H) = 0` for every `M`: the candidate damps nothing. -/
theorem crossTetherKernel_H_right (ω : CoadjointOrbit) (M : Functional)
    (hδH : FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω)
    (hdiv : ∀ x, div (velocity_from_vorticity ω) x = 0)
    (hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂volume) ≠ 0) :
    CrossTetherKernel ω M KineticEnergyHamiltonian = 0 := by
  rw [crossTetherKernel_antisymm, crossTetherKernel_H_left ω M hδH hdiv hE, neg_zero]

/-- Abstract version: any antisymmetric `B` with `B(H,·)=0` has `B(·,H)=0`. -/
theorem right_H_zero_of_antisymm_C2 (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h : ∀ ω F G, B ω F G = -B ω G F) (hC2 : ∀ ω G, B ω KineticEnergyHamiltonian G = 0)
    (ω : CoadjointOrbit) (M : Functional) : B ω M KineticEnergyHamiltonian = 0 := by
  rw [h, hC2, neg_zero]

end FrohmanianTether.DropSymmetry

end

#print axioms FrohmanianTether.DropSymmetry.crossTetherKernel_antisymm
#print axioms FrohmanianTether.DropSymmetry.crossTetherKernel_diag
#print axioms FrohmanianTether.DropSymmetry.crossTetherKernel_H_left
#print axioms FrohmanianTether.DropSymmetry.crossTetherKernel_H_right
#print axioms FrohmanianTether.DropSymmetry.right_H_zero_of_antisymm_C2
