/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem comparison_ode_stability
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hy_dot : ∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ max (y 0) (C / κ'') := by
  set Y := max (y 0) (C / κ'')
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbarrier : C / κ'' < Y + ε :=
    lt_of_le_of_lt (le_max_right (y 0) (C / κ'')) (lt_add_of_pos_right _ hε)
  have hy0 : y 0 ≤ Y + ε :=
    (le_max_left (y 0) (C / κ'')).trans (le_add_of_nonneg_right hε.le)
  have hyC : ContinuousOn y (Icc (0 : ℝ) t) := fun x hx =>
    (hdiff x hx.1).continuousAt.continuousWithinAt
  have hyW : ∀ x ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt y (deriv y x) (Ici x) x := fun x hx =>
    (hdiff x hx.1).hasDerivAt.hasDerivWithinAt
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => Y + ε) (0 : ℝ) x := fun x =>
    hasDerivAt_const x (Y + ε)
  have hcontact : ∀ x ∈ Ico (0 : ℝ) t, y x = Y + ε → deriv y x < 0 := by
    intro x hx hxeq
    have hneg : C * (Y + ε) ^ 2 - κ'' * (Y + ε) ^ 3 < 0 :=
      majorant_vector_field_neg_of_gt hC hκ hbarrier
    have := hy_dot x hx.1
    rw [hxeq] at this
    linarith
  have hle :=
    image_le_of_deriv_right_lt_deriv_boundary (f := y) (f' := deriv y)
      (a := 0) (b := t) (B := fun _ => Y + ε) (B' := fun _ => (0 : ℝ))
      hyC hyW hy0 hB hcontact
  exact hle ⟨ht, le_rfl⟩
