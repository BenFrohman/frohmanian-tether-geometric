/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem stepField_not_physical : ¬ IsPhysicalNSSolution stepField := by
  intro hphys
  have hS0 : stepField 0 = 0 := by funext x; simp [stepField]
  have h20 : stepField 2 = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero stepField hS0 hphys 2 (by norm_num)
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) (congrFun h20 0)
  simp [stepField] at h2

public theorem repaired_huniq_at_zero (ν : ℝ) (w : KatoLocalWitness 0 ν) :
    ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes 0 ν →
      v 0 = 0 →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t := by
  intro T' v _q _hmem hv0 _hpde _hsm hphys t ht
  have hw_zero : w.u t = 0 := eq_zero_of_isPhysicalNSSolution_zero w.u w.init w.phys t ht.1
  have hv_zero : v t = 0 := eq_zero_of_isPhysicalNSSolution_zero v hv0 hphys t ht.1
  exact hw_zero.trans hv_zero.symm

public theorem frohmanianTetherBound_zero (ν : ℝ) : FrohmanianTetherBound 0 ν := by
  intro u p _hNS hu0 hphys
  have hu_all : ∀ τ : ℝ, u τ = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero_all u hu0 hphys
  have hfun : (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) = fun _ => (0 : ℝ) := by
    funext τ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  refine ⟨0, ?_, ?_, ?_⟩
  · intro τ _hτ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  · rw [hfun]
    exact continuous_const
  · intro τ _hτ
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [vorticity]
    rw [hu_all τ, curl_zero x, norm_zero]

public theorem frohmanianTetherRate_zero (ν : ℝ) : FrohmanianTetherRate 0 ν := by
  intro u p _hν _hNS hu0 hphys
  have hu_all : ∀ τ : ℝ, u τ = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero_all u hu0 hphys
  have hfun : (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) = fun _ => (0 : ℝ) := by
    funext τ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  refine ⟨1, 1, one_pos, one_pos, ?_, ?_, ?_, ?_⟩
  · intro s _hs
    rw [hfun]
    exact differentiableAt_const 0
  · intro s _hs
    have hds : deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s = 0 := by
      rw [hfun]; simp
    rw [hds, hu_all s, vorticity_sup_norm_zero_field]
    norm_num
  · rw [hfun]
    exact continuous_const
  · intro τ _hτ
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [vorticity]
    rw [hu_all τ, curl_zero x, norm_zero]

public theorem conditional_regularity_nonvacuous_at_zero (ν : ℝ) (hν : 0 < ν) :
    ∃ (u : TimeDependentVelocity),
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (u t)) ∧
      (u 0 = 0) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes u ν) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ v : TimeDependentVelocity,
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (v t)) →
        v 0 = 0 →
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes v ν) →
        ∀ t ≥ (0 : ℝ), v t = u t) :=
  ConditionalRegularity.conditional_regularity_of_open_hyps
    (fun _ => 0)
  ...
