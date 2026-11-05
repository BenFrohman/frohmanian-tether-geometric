/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.VelocitySlotTether

/-!
# Canonical stream function `ψ = (-Δ)⁻¹ ω` (added alongside the original definitions)

The model space `T3` in this repo is `EuclideanSpace ℝ (Fin 3)` (ℝ³ with Lebesgue
volume), not a quotient torus, so a zero-mean *Fourier series* definition is not
available at the type level. The honest equivalent that pins `ψ` uniquely is the
Newtonian potential `ψ(x) = ∫ (4π|x-y|)⁻¹ ω(y) dy`, defined here by an explicit
integral (no choice).

Proved here: `ψ` is uniquely determined (a definition), linear in scaling, zero on
zero data, and the curl identity holds for zero data. Two classical facts remain
**named hypotheses** (flagged in `NAMING.md`):
* `StreamFunctionCurlIsBiotSavart ω` : `curl ψ = BiotSavart ω` (differentiation
  under the singular integral, `∇(4π|z|)⁻¹ = -z/(4π|z|³)`);
* `FunctionalDerivativeIsStreamFunction ω` : the encoded `FunctionalDerivative`
  of kinetic energy equals `ψ` (integration by parts plus a uniqueness choice;
  representatives against divergence-free variations are only unique up to
  gradients, so this does not follow from `IsGateauxRepresentative` alone).
The original `KineticEnergyCurlIdentification` is untouched and remains OPEN.
-/

@[expose] public section
open InnerProductSpace NavierStokes3D ArnoldGeometric MeasureTheory ForMathlib

namespace FrohmanianTether

/-- Newtonian kernel `(4π|x-y|)⁻¹` (set to `0` on the diagonal). -/
public noncomputable def newtonKernel (x y : T3) : ℝ :=
  if x = y then 0 else (4 * Real.pi)⁻¹ * ‖x - y‖⁻¹

/-- Canonical stream function `ψ = (-Δ)⁻¹ ω` as the Newtonian potential. -/
public noncomputable def StreamFunction (ω : T3 → EuclideanSpace ℝ (Fin 3)) :
    VelocityField :=
  fun x => ∫ y, newtonKernel x y • ω y ∂volume

/-- Canonical functional derivative of kinetic energy: the stream function. -/
public noncomputable def CanonicalKineticDerivative (ω : CoadjointOrbit) : VelocityField :=
  StreamFunction ω.val

/-- **Named classical hypothesis.** `curl ψ = BiotSavart ω`. -/
public def StreamFunctionCurlIsBiotSavart (ω : CoadjointOrbit) : Prop :=
  curl (StreamFunction ω.val) = BiotSavart ω.val

/-- **Named classical hypothesis.** The encoded derivative equals `ψ`. -/
public def FunctionalDerivativeIsStreamFunction (ω : CoadjointOrbit) : Prop :=
  FunctionalDerivative KineticEnergyHamiltonian ω = CanonicalKineticDerivative ω

/-- `ψ` is homogeneous of degree one (unconditional). -/
public theorem streamFunction_smul (c : ℝ) (ω : T3 → EuclideanSpace ℝ (Fin 3)) :
    StreamFunction (fun y => c • ω y) = fun x => c • StreamFunction ω x := by
  funext x
  simp only [StreamFunction]
  rw [← integral_smul]
  congr 1
  funext y
  rw [smul_comm]

/-- `ψ` of zero data is zero. -/
public theorem streamFunction_zero : StreamFunction (fun _ => 0) = 0 := by
  have h := streamFunction_smul 0 (fun _ => 0)
  funext x
  have hx := congrFun h x
  simpa using hx

/-- The curl identity holds for zero data (proved). -/
public theorem streamFunctionCurlIsBiotSavart_of_zero (ω : CoadjointOrbit)
    (hω : ω.val = fun _ => 0) : StreamFunctionCurlIsBiotSavart ω := by
  unfold StreamFunctionCurlIsBiotSavart
  rw [hω, streamFunction_zero, BiotSavart_zero]
  funext x
  simp only [curl, directionalCoord]
  ext i
  simp [EuclideanSpace.single_apply]

/-- **Proved reduction.** The two named classical facts give the original
identification `KineticEnergyCurlIdentification`. -/
public theorem kineticEnergyCurlIdentification_of_streamFunction (ω : CoadjointOrbit)
    (hrep : FunctionalDerivativeIsStreamFunction ω)
    (hcurl : StreamFunctionCurlIsBiotSavart ω) :
    KineticEnergyCurlIdentification ω := by
  unfold KineticEnergyCurlIdentification FunctionalDerivativeIsStreamFunction at *
  rw [hrep]
  exact hcurl

/-- C2 for `TetherKernelVel` via the canonical stream function (conditional on the
two named classical facts plus the standing `div u = 0` and finite energy). -/
public theorem tetherKernelVel_C2_streamFunction (ω : CoadjointOrbit) (G : Functional)
    (hrep : FunctionalDerivativeIsStreamFunction ω)
    (hcurl : StreamFunctionCurlIsBiotSavart ω)
    (hdiv : ∀ x, div (velocity_from_vorticity ω) x = 0)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2)) :
    TetherKernelVel ω KineticEnergyHamiltonian G = 0 :=
  tetherKernelVel_C2 ω G
    (kineticEnergyCurlIdentification_of_streamFunction ω hrep hcurl) hdiv hInt

end FrohmanianTether

end

#print axioms FrohmanianTether.streamFunction_smul
#print axioms FrohmanianTether.streamFunction_zero
#print axioms FrohmanianTether.streamFunctionCurlIsBiotSavart_of_zero
#print axioms FrohmanianTether.kineticEnergyCurlIdentification_of_streamFunction
#print axioms FrohmanianTether.tetherKernelVel_C2_streamFunction
