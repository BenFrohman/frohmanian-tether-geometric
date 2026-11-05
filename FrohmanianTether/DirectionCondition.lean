/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.VorticityL6Bound

/-!
# Vorticity-direction regularity criteria (Constantin–Fefferman; Beirão da Veiga–Berselli)

Classical results, **assumed as named `Prop`s, not formalized**:
* Constantin–Fefferman (Indiana Univ. Math. J. 42 (1993) 775–789): if the vorticity
  direction `ξ = ω/|ω|` is Lipschitz in space on the set where `|ω| > Λ`, uniformly on
  `[0,T]`, then the solution stays smooth on `[0,T]`.
* Beirão da Veiga–Berselli (Differential Integral Equations 15 (2002) 345–356): the
  same with `½`-Hölder in place of Lipschitz.

Proved here (elementary): `ξ` is a unit vector where `ω ≠ 0`; `ξ` is invariant under
`ω ↦ c ω` for `c > 0`; the Lipschitz condition at threshold `Λ` for `ω` is equivalent to
the one at threshold `c Λ` for `c ω`; Lipschitz on the high set implies `½`-Hölder on
the high set with constant `max L 2` (using `‖ξ‖ = 1`); and the modus-ponens chains.
Nothing here proves regularity for general data. Not a Clay claim.
-/

open NavierStokes3D MeasureTheory
open scoped ContDiff

namespace FrohmanianTether

/-- Vorticity direction `ξ = ω/|ω|` (equals `0` where `ω = 0`). -/
@[expose] public noncomputable def vorticityDirection (w : VelocityField) (x : T3) :
    EuclideanSpace ℝ (Fin 3) :=
  ‖w x‖⁻¹ • w x

/-- `ξ` is Lipschitz with constant `L` on the high set `{|w| ≥ Λ}`. -/
@[expose] public def DirectionLipschitzOnHighSet (w : VelocityField) (Λ L : ℝ) : Prop :=
  ∀ x y, Λ ≤ ‖w x‖ → Λ ≤ ‖w y‖ →
    ‖vorticityDirection w x - vorticityDirection w y‖ ≤ L * ‖x - y‖

/-- `ξ` is `½`-Hölder with constant `L` on the high set `{|w| ≥ Λ}`. -/
@[expose] public def DirectionHalfHolderOnHighSet (w : VelocityField) (Λ L : ℝ) : Prop :=
  ∀ x y, Λ ≤ ‖w x‖ → Λ ≤ ‖w y‖ →
    ‖vorticityDirection w x - vorticityDirection w y‖ ≤ L * Real.sqrt ‖x - y‖

/-- Spacetime version (Constantin–Fefferman hypothesis) on `[0,T]`. -/
@[expose] public def VorticityDirectionLipschitzOnHighSet (u : ℝ → VelocityField) (T : ℝ) :
    Prop :=
  ∃ Λ L : ℝ, 0 < Λ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
    DirectionLipschitzOnHighSet (vorticity (u t)) Λ L

/-- Spacetime version (Beirão da Veiga–Berselli hypothesis) on `[0,T]`. -/
@[expose] public def VorticityDirectionHalfHolderOnHighSet (u : ℝ → VelocityField) (T : ℝ) :
    Prop :=
  ∃ Λ L : ℝ, 0 < Λ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
    DirectionHalfHolderOnHighSet (vorticity (u t)) Λ L

/-- **Classical, assumed (Constantin–Fefferman 1993).** Not formalized. -/
@[expose] public def ConstantinFeffermanCriterion (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
          NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
            ∀ T : ℝ, 0 ≤ T → VorticityDirectionLipschitzOnHighSet u T →
              ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)

/-- **Classical, assumed (Beirão da Veiga–Berselli 2002).** Not formalized. -/
@[expose] public def BeiraoDaVeigaBerselliCriterion (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
          NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
            ∀ T : ℝ, 0 ≤ T → VorticityDirectionHalfHolderOnHighSet u T →
              ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)

/-- `ξ` is a unit vector wherever `ω ≠ 0`. -/
public theorem norm_vorticityDirection (w : VelocityField) (x : T3) (hx : w x ≠ 0) :
    ‖vorticityDirection w x‖ = 1 := by
  unfold vorticityDirection
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- `ξ` is invariant under positive rescaling `ω ↦ c ω`. -/
public theorem vorticityDirection_smul (w : VelocityField) {c : ℝ} (hc : 0 < c) :
    vorticityDirection (fun y => c • w y) = vorticityDirection w := by
  funext x
  unfold vorticityDirection
  rw [norm_smul, Real.norm_of_nonneg hc.le, smul_smul, mul_inv]
  congr 1
  field_simp

/-- The Lipschitz high-set condition is invariant under `ω ↦ c ω`, `c > 0`,
with the threshold rescaled to `c Λ`. -/
public theorem directionLipschitz_smul_iff (w : VelocityField) {c : ℝ} (hc : 0 < c)
    (Λ L : ℝ) :
    DirectionLipschitzOnHighSet (fun y => c • w y) (c * Λ) L ↔
      DirectionLipschitzOnHighSet w Λ L := by
  unfold DirectionLipschitzOnHighSet
  rw [vorticityDirection_smul w hc]
  have key : ∀ z, c * Λ ≤ ‖c • w z‖ ↔ Λ ≤ ‖w z‖ := fun z => by
    rw [norm_smul, Real.norm_of_nonneg hc.le]
    exact mul_le_mul_iff_right₀ hc
  simp only [key]

/-- **Lipschitz ⇒ ½-Hölder** on the high set (threshold `Λ > 0`), constant `max L 2`.
Uses `‖ξ‖ = 1`: for `‖x-y‖ ≤ 1`, `‖x-y‖ ≤ √‖x-y‖`; for `‖x-y‖ ≥ 1`, `‖ξx-ξy‖ ≤ 2`. -/
public theorem halfHolder_of_lipschitz (w : VelocityField) {Λ L : ℝ} (hΛ : 0 < Λ)
    (h : DirectionLipschitzOnHighSet w Λ L) :
    DirectionHalfHolderOnHighSet w Λ (max L 2) := by
  intro x y hx hy
  have hx0 : w x ≠ 0 := fun h0 => by simp [h0] at hx; linarith
  have hy0 : w y ≠ 0 := fun h0 => by simp [h0] at hy; linarith
  set d := ‖x - y‖
  have hd : 0 ≤ d := norm_nonneg _
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h2 : ‖vorticityDirection w x - vorticityDirection w y‖ ≤ 2 := by
    calc _ ≤ ‖vorticityDirection w x‖ + ‖vorticityDirection w y‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_vorticityDirection w x hx0, norm_vorticityDirection w y hy0]; norm_num
  rcases le_total d 1 with hd1 | hd1
  · have hds : d ≤ Real.sqrt d := (Real.le_sqrt hd hd).mpr (by nlinarith)
    have hL := h x y hx hy
    by_cases hLn : 0 ≤ L
    · calc _ ≤ L * d := hL
        _ ≤ L * Real.sqrt d := mul_le_mul_of_nonneg_left hds hLn
        _ ≤ max L 2 * Real.sqrt d := mul_le_mul_of_nonneg_right (le_max_left _ _) hs
    · have : L * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hd
      calc _ ≤ L * d := hL
        _ ≤ 0 := this
        _ ≤ max L 2 * Real.sqrt d :=
          mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) hs
  · have h1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
    calc _ ≤ 2 := h2
      _ ≤ 2 * Real.sqrt d := by nlinarith
      _ ≤ max L 2 * Real.sqrt d := mul_le_mul_of_nonneg_right (le_max_right _ _) hs

/-- Spacetime: Lipschitz direction condition ⇒ ½-Hölder direction condition. -/
public theorem vorticityDirectionHalfHolder_of_lipschitz (u : ℝ → VelocityField) (T : ℝ)
    (h : VorticityDirectionLipschitzOnHighSet u T) :
    VorticityDirectionHalfHolderOnHighSet u T := by
  obtain ⟨Λ, L, hΛ, hL⟩ := h
  exact ⟨Λ, max L 2, hΛ, fun t ht => halfHolder_of_lipschitz _ hΛ (hL t ht)⟩

/-- **Proved (modus ponens only).** Constantin–Fefferman criterion + Lipschitz
direction condition along a physical solution ⇒ smooth on `[0,T]`. -/
public theorem regularity_of_direction_condition (ν : ℝ) (hCF : ConstantinFeffermanCriterion ν)
    (u₀ : VelocityField) (hdiv : ∀ x, div u₀ x = 0) (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (u : ℝ → VelocityField) (p : ℝ → PressureField) (hNS : NS_PDE u p ν) (h0 : u 0 = u₀)
    (hphys : IsPhysicalNSSolution u) (T : ℝ) (hT : 0 ≤ T)
    (hdir : VorticityDirectionLipschitzOnHighSet u T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  hCF u₀ hdiv hsm hE u p hNS h0 hphys T hT hdir

/-- **Proved (modus ponens only).** Beirão da Veiga–Berselli criterion +
½-Hölder direction condition ⇒ smooth on `[0,T]`. -/
public theorem regularity_of_halfHolder_direction_condition (ν : ℝ)
    (hBB : BeiraoDaVeigaBerselliCriterion ν)
    (u₀ : VelocityField) (hdiv : ∀ x, div u₀ x = 0) (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (u : ℝ → VelocityField) (p : ℝ → PressureField) (hNS : NS_PDE u p ν) (h0 : u 0 = u₀)
    (hphys : IsPhysicalNSSolution u) (T : ℝ) (hT : 0 ≤ T)
    (hdir : VorticityDirectionHalfHolderOnHighSet u T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  hBB u₀ hdiv hsm hE u p hNS h0 hphys T hT hdir

/-- **Proved.** The Beirão da Veiga–Berselli criterion alone implies the
Constantin–Fefferman criterion (Lipschitz ⇒ ½-Hölder on the high set). -/
public theorem constantinFefferman_of_beiraoDaVeigaBerselli (ν : ℝ)
    (hBB : BeiraoDaVeigaBerselliCriterion ν) : ConstantinFeffermanCriterion ν :=
  fun u₀ hdiv hsm hE u p hNS h0 hphys T hT hdir =>
    hBB u₀ hdiv hsm hE u p hNS h0 hphys T hT (vorticityDirectionHalfHolder_of_lipschitz u T hdir)

end FrohmanianTether

#print axioms FrohmanianTether.norm_vorticityDirection
#print axioms FrohmanianTether.vorticityDirection_smul
#print axioms FrohmanianTether.directionLipschitz_smul_iff
#print axioms FrohmanianTether.halfHolder_of_lipschitz
#print axioms FrohmanianTether.vorticityDirectionHalfHolder_of_lipschitz
#print axioms FrohmanianTether.regularity_of_direction_condition
#print axioms FrohmanianTether.regularity_of_halfHolder_direction_condition
#print axioms FrohmanianTether.constantinFefferman_of_beiraoDaVeigaBerselli
