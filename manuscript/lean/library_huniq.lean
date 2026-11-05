/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem library_huniq_unsatisfiable_at_zero (ν : ℝ) (w : KatoLocalWitness 0 ν) :
    ¬ (∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes 0 ν → v 0 = 0 → NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) := by
  intro h
  have hS : NS_PDE stepField (fun _ _ => 0) ν :=
    ns_of_spatially_const _ ν (fun t => ⟨_, rfl⟩) (fun t x => deriv_step x t)
  have hZ : NS_PDE (fun (_ : ℝ) (_ : T3) => (0 : EuclideanSpace ℝ (Fin 3))) (fun _ _ => 0) ν :=
    ns_of_spatially_const _ ν (fun t => ⟨0, rfl⟩) (fun _ _ => by simp)
  have hS0 : stepField 0 = 0 := by funext x; simp [stepField]
  have hSsm : ∀ t ∈ Set.Icc (0 : ℝ) 2, ContDiff ℝ (⊤ : ℕ∞) (stepField t) :=
    fun t _ => contDiff_const
  have hZsm : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      ContDiff ℝ (⊤ : ℕ∞) ((fun (_ : ℝ) (_ : T3) => (0 : EuclideanSpace ℝ (Fin 3))) t) :=
    fun t _ => contDiff_const
  have hmem : (2 : ℝ) ∈ existenceTimes 0 ν :=
    mem_existenceTimes_zero ν (by norm_num)
  have h1 := h 2 stepField _ hmem hS0 hS hSsm 2 ⟨by norm_num, le_rfl⟩
  have h2 := h 2 _ _ hmem rfl hZ hZsm 2 ⟨by norm_num, le_rfl⟩
  have := congrFun (h1.symm.trans h2) 0
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) this
  simp [stepField] at this
