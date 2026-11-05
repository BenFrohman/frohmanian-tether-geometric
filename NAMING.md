# Named hypotheses (open, not proved in this repository)

| Name | Statement | Used by | Status |
|---|---|---|---|
| `KineticEnergyCurlIdentification ω` | `curl (FunctionalDerivative KineticEnergyHamiltonian ω) = velocity_from_vorticity ω` (i.e. `curl ψ = u` for the Gâteaux representative of kinetic energy in the vorticity pairing) | `tetherKernelVel_C2`, `tetherKernelVel_C2_right`, `tetherKernelVel_degenerate` (`FrohmanianTether/VelocitySlotTether.lean`) | **OPEN.** Needs existence + uniqueness of the Gâteaux representative of `KineticEnergyHamiltonian` and Biot–Savart calculus; not derivable from the current definitions, so it is an explicit hypothesis rather than a faked lemma. |

Notes
- `FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω` (the ψ-slot C2 hypothesis `hδ` in `tetherKernel_C2_of_identifications`) is a different identification. In the vorticity pairing the representative is the stream function ψ, not u; with δH = ψ the ψ-slot C2 fails on a two-mode shear (commit `a52c6af`, frohmanian-symplectic-tether-regularity).
- C2 for either kernel gives `T(M,H) = 0` by symmetry, so neither kernel supplies enstrophy damping. `FrohmanianTetherRate` remains open.
