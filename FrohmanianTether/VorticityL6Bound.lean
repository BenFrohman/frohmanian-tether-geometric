/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.NS_Equations

/-!
# Spacetime L⁶ vorticity bound (named open hypothesis)

The May draft's missing piece is a uniform spacetime bound
`∫₀ᵀ ∫_{𝕋³} |ω|⁶ dx dt < ∞`. That bound is **OPEN**: for general smooth data it is
equivalent in difficulty to the Navier–Stokes Millennium problem (a subcritical
Serrin-type quantity, but still an a-priori bound that energy methods do not give).
It is **not proved** in this repository, and the Frohmanian tether does not supply it
(`T(M,H) = 0` under C2; see `ObstructionAudit.lean`, `HWEIGHT_OBSTRUCTION.md`).

What *is* classical (Serrin / Beale–Kato–Majda-adjacent, not formalized here) is the
implication: if that L⁶ bound holds along a solution on `[0, T]`, then the solution
stays smooth on `[0, T]`. Both facts are recorded as named `Prop`s. The only theorem
in this file is honest modus ponens: open bound + classical implication ⇒ regularity
on every compact interval. No `sorry`, no new `axiom`.
-/

open NavierStokes3D MeasureTheory
open scoped ContDiff

namespace FrohmanianTether

/-- Spacetime L⁶ integrability of vorticity on a compact time interval:
`∫₀ᵀ (∫ |ω(t,x)|⁶ dx) dt < ∞`, with the spatial integral existing at each `t`.
This is the concrete content of `∫₀ᵀ ∫ |ω|⁶ < ∞`. -/
@[expose] public def HasVorticityL6OnInterval (u : ℝ → VelocityField) (T : ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : T3 => ‖vorticity (u t) x‖ ^ 6)) ∧
  IntegrableOn
    (fun t => ∫ x, ‖vorticity (u t) x‖ ^ 6 ∂NavierStokes3D.volume)
    (Set.Icc (0 : ℝ) T)

/-- **Spacetime L⁶ vorticity bound** (OPEN). For every smooth, divergence-free,
finite-energy initial datum and every physical NS solution from it, vorticity is
L⁶ in spacetime on every compact time interval `[0, T]`.

**Status: OPEN.** Not proved here. A uniform L⁶ spacetime bound on vorticity for
all smooth data is equivalent in difficulty to the Clay Millennium Navier–Stokes
problem itself (subcritical Serrin-type control, but still an open a-priori bound).
The tether kernel does not produce this bound. Listed in `NAMING.md`. -/
@[expose] public def VorticityL6SpacetimeBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
          NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
            ∀ T : ℝ, 0 ≤ T → HasVorticityL6OnInterval u T

/-- **Classical L⁶ ⇒ regularity** (OPEN in Lean; classical Serrin / subcritical).
If a physical NS solution has vorticity in L⁶([0,T] × 𝕋³), then the solution is
smooth (`ContDiff ℝ ⊤`) on `[0, T]`.

**Status: classical, assumed as hypothesis.** Not formalized in this repository.
Literature: Serrin-type criteria (velocity in critical Lebesgue spaces) and the
Beale–Kato–Majda / Prodi–Serrin family; an L⁶_{t,x} bound on vorticity is
subcritical relative to the scaling `ω ↦ λ² ω` and is classically known to prevent
blow-up. Recorded here so the gap is explicit. Listed in `NAMING.md`. -/
@[expose] public def L6VorticityImpliesRegularity (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
          NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
            ∀ T : ℝ, 0 ≤ T → HasVorticityL6OnInterval u T →
              ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)

/-- **Proved (modus ponens only).** If the open spacetime L⁶ bound held, and the
classical L⁶ ⇒ regularity implication held, then every physical solution from
admissible data would be smooth on every compact interval `[0, T]`.

This is not a Clay solution: both hypotheses are open in Lean (the first is as
hard as the Millennium problem; the second is classical but unformalized here).
Certificate: `#print axioms regularity_of_L6_bound` — only the standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`), never `sorryAx`. -/
public theorem regularity_of_L6_bound {ν : ℝ} (_hν : 0 < ν)
    (hL6 : VorticityL6SpacetimeBound ν)
    (hImp : L6VorticityImpliesRegularity ν)
    (u₀ : VelocityField)
    (hdiv : ∀ x, div u₀ x = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (u : ℝ → VelocityField) (p : ℝ → PressureField)
    (hNS : NS_PDE u p ν) (h0 : u 0 = u₀) (hphys : IsPhysicalNSSolution u)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  hImp u₀ hdiv hsm hE u p hNS h0 hphys T hT
    (hL6 u₀ hdiv hsm hE u p hNS h0 hphys T hT)

end FrohmanianTether

#print axioms FrohmanianTether.regularity_of_L6_bound
