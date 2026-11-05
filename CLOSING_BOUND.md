# The closing bound — the single open analytic assumption

Author: Benjamin Stanley Frohman. **No Clay claim.** Nothing here proves the bound.

## Named open Props (Lean source of truth)
| Name | File:line | Domain | Status |
|---|---|---|---|
| `FrohmanianTetherClosingBound ν` | `FrohmanianTether/ClayStatements.lean:47` | `T3` (ℝ³ model), all smooth div-free finite-energy data | **OPEN** |
| `PeriodicTetherClosingBound ν` | `FrohmanianTether/ClayStatements.lean:568` | ℤ³-periodic smooth data | **OPEN** |
| `FrohmanianTetherBound u₀ ν` (per-datum body of the ℝ³ bound) | `FrohmanianTether/SymplecticTether.lean:740` | one datum | OPEN; proved at `u₀ = 0` (`frohmanianTetherBound_zero`) |
| `FrohmanianTetherRate u₀ ν` (cubic rate `M' ≤ CM² − κ''M³`) | `FrohmanianTether/SymplecticTether.lean:752` | one datum | OPEN; proved at `u₀ = 0` (`frohmanianTetherRate_zero`) |
| `PeriodicDirectionDepletionBound ν` | `FrohmanianTether/HighSetDepletionAndBKM.lean:192` | periodic | OPEN; implies `PeriodicTetherClosingBound` |

## Honest status
* OPEN for general data. A time-uniform `‖ω‖_∞` bound for all data is, via BKM, equivalent
  to global regularity: as hard as Clay itself, not a reduction of it.
* The tether contributes nothing BKM does not: under C2, `T(M,H) = 0`, so the geometric
  layer supplies no damping for `M = ‖ω‖_∞`. C3 (`T(F,F) ≤ 0`) dissipates only in
  directions C2 forces to vanish on H. This C2/C3 obstruction sits exactly at the closing bound.
* Only zero-data instances are proved.

## Consumers (all conditional, standard axioms)
* `bkm_of_closing_bound` (ClayStatements:79) — closing bound ⇒ `BKMClosingCriterion`.
* `frohmanian_conditional_regularity_of_closing_bound` (ClayStatements:145).
* `clay_B_exact_of_periodic_tether_bound` (ClayStatements:592) — also needs `PeriodicBKMContinuation` (open in Lean).
* `periodicTetherClosingBound_of_directionDepletion`, `clay_B_exact_of_torus_direction_depletion` (HighSetDepletionAndBKM).
* `Combined.lean:113` (`hClose`), `ConditionalRegularity.lean:83,214` (`hDI`, `hRiccati`),
  `ClosureBlueprint.lean:269`, `TetheredLyapunov.lean:1821,1828`.
