/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem uniqueness_of_minimal_tether
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (_hyp : SDiffActionHyp SDiff)
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (hC1 : InvariantUnderCoadjointAction SDiff B)
    (hC2 : DegenerateWRTKineticEnergy B)
    (hC3 : ProducesControllableNegativeFeedback B)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : Polarizes B)
    (h_polarT : Polarizes TetherKernel) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel ω F G :=
  uniqueness_of_minimal_symmetric_tether SDiff B h_sym hC1 hC2 hC3 h_sat h_polarB h_polarT

public theorem uniqueness_of_minimal_symmetric_tether
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (_h_sym : ∀ ω F G, B ω F G = B ω G F)
    (_hC1 : InvariantUnderCoadjointAction SDiff B)
    (_hC2 : DegenerateWRTKineticEnergy B)
    (_hC3 : ProducesControllableNegativeFeedback B)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : Polarizes B)
    (h_polarT : Polarizes TetherKernel) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel ω F G := by
  intro ω F G
  have hB := h_polarB ω F G
  have hT := h_polarT ω F G
  have hFF := h_sat F ω
  have hGG := h_sat G ω
  have hFG := h_sat (fun ω' => F ω' + G ω') ω
  linarith
