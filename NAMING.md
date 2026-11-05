# Named hypotheses (open, not proved in this repository)

| Name | Statement | Used by | Status |
|---|---|---|---|
| `KineticEnergyCurlIdentification ω` | `curl (FunctionalDerivative KineticEnergyHamiltonian ω) = velocity_from_vorticity ω` (i.e. `curl ψ = u` for the Gâteaux representative of kinetic energy in the vorticity pairing) | `tetherKernelVel_C2`, `tetherKernelVel_C2_right`, `tetherKernelVel_degenerate` (`FrohmanianTether/VelocitySlotTether.lean`) | **OPEN.** Needs existence + uniqueness of the Gâteaux representative of `KineticEnergyHamiltonian` and Biot–Savart calculus; not derivable from the current definitions, so it is an explicit hypothesis rather than a faked lemma. |
| `VorticityL6SpacetimeBound ν` | For every smooth div-free finite-energy `u₀` and every physical NS solution from it: `HasVorticityL6OnInterval u T` for all `T ≥ 0`, i.e. `∫₀ᵀ ∫ |ω|⁶ dx dt < ∞` | `regularity_of_L6_bound` (`FrohmanianTether/VorticityL6Bound.lean`) | **OPEN.** Equivalent in difficulty to the Millennium problem (subcritical Serrin-type a-priori bound). Not proved; the tether does not supply it (`T(M,H)=0` under C2). |
| `L6VorticityImpliesRegularity ν` | If `HasVorticityL6OnInterval u T`, then `∀ t ∈ [0,T], ContDiff ℝ ⊤ (u t)` (classical Serrin / subcritical implication) | `regularity_of_L6_bound` (`FrohmanianTether/VorticityL6Bound.lean`) | **OPEN in Lean / classical in the literature.** Assumed as a named hypothesis; not formalized here. |

Notes
- `FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω` (the ψ-slot C2 hypothesis `hδ` in `tetherKernel_C2_of_identifications`) is a different identification. In the vorticity pairing the representative is the stream function ψ, not u; with δH = ψ the ψ-slot C2 fails on a two-mode shear (commit `a52c6af`, frohmanian-symplectic-tether-regularity).
- C2 for either kernel gives `T(M,H) = 0` by symmetry, so neither kernel supplies enstrophy damping. `FrohmanianTetherRate` remains open.
- `regularity_of_L6_bound` is honest modus ponens only: open L⁶ bound + classical implication ⇒ regularity on compact intervals. It is not a Clay claim. Certificate: `#print axioms regularity_of_L6_bound`.
