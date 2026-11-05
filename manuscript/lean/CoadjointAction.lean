/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public abbrev CoadjointAction {SDiff : Type*} [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (g : SDiff) (ω : CoadjointOrbit) : CoadjointOrbit :=
  g • ω
