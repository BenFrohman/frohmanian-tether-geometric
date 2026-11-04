# Geometric skeleton: conservative vs. dissipative directions

Author: Benjamin Stanley Frohman. Scope: geometry of the bracket only. No Navier–Stokes
regularity or Clay result is claimed.

## Terminology
- The classical Lie–Poisson bracket `{·,·}_cl` is antisymmetric and satisfies the Jacobi
  identity. That makes it a Poisson bracket, and makes the coadjoint orbits its symplectic leaves.
- The tethered sum `{F,G}_tethered = {F,G}_cl + T(F,G)` is **metriplectic** (antisymmetric +
  symmetric ≤ 0). It is not Poisson and does not have the same leaves.

## Claims
1. `{F,F}_tethered = T(F,F) = −κ‖ω‖² ∫ |Π_u δF|² ≤ 0`. The classical term vanishes by
   antisymmetry. `T(F,F)` is nonzero on some functionals away from the energy direction —
   stated, not machine-checked for the integrated kernel.
2. C2 (`T(F,H) = 0` for all F) plus symmetry forces `T(H,·) = 0`. Hence `{H,H}_tethered = 0`:
   the tethered flow conserves kinetic energy, and the ideal-Euler vector field of H is exactly
   the classical one.
3. This separates the conservative skeleton (the H direction, purely classical) from the
   dissipative directions (functionals with `Π_u δF ≠ 0`). It does **not** give the damping
   estimate: `T(M,H) = 0` for every M, so the bracket supplies zero damping to
   `M = ‖ω‖_∞`. The C2/C3 obstruction stays open.

## Claim-to-theorem map (FrohmanianTether, standard axioms, no sorry)
| Claim | Status |
|---|---|
| `{·,·}_cl` antisymmetric | machine-checked (`classicalBracket_antisymm`) |
| `{F,F}_cl = 0` | machine-checked (`classicalBracket_self`); `{H,H}_cl = 0`: `classicalBracket_H_H` |
| Jacobi for `{·,·}_cl` | stated, not machine-checked (cited Arnold 1966; pointwise `cross_jacobi_identity` only) |
| Coadjoint orbits are symplectic leaves | stated, not machine-checked (classical) |
| `T(F,F) = −κ‖ω‖²∫‖Π_u δF‖²` | machine-checked (`tetherKernel_quadratic_form`); `≤`: `tetherKernel_C3` |
| `T` symmetric | machine-checked (`tetherKernel_comm` / `tetherKernel_symmetric`) |
| `{F,F}_tethered = T(F,F)` | follows by unfolding `TetheredBracket` + `classicalBracket_self`; no standalone theorem |
| `T(F,F) ≢ 0` (integrated kernel) | stated, not machine-checked (only pointwise model: `tetherKernel_strict_neg_of_orthogonal_component` on `casimirTetherKernel`) |
| C2 ⇒ `T(H,M) = T(M,H) = 0` | machine-checked, with C2 as hypothesis (`tetherKernel_left_H_zero`, `left_H_zero_of_C2_symm`) |
| C2 holds for `TetherKernel` | conditional on `KineticEnergyDerivIsVelocity` (`tetherKernel_C2_of_KEDeriv`, `tetherKernel_degenerates_on_kinetic_energy`) |
| Tethered H-flow = classical Euler | conditional on δH = u (`tethered_reproduces_classical_euler`) |

## Caveat kept
`δH/δω` for `H = ½∫|BS ω|²` is the stream function ψ, not u. `KineticEnergyDerivIsVelocity`
is likely false as stated, so C2 for `TetherKernel` (and claim 2 applied to it) is conditional
on a suspect hypothesis. The implication "C2 ⇒ T(H,·)=0" is unaffected.
