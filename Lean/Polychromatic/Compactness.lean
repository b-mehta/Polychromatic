/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Compactness

/-!
# The de Bruijn–Erdős theorem

This file proves the de Bruijn–Erdős theorem: if every finite subgraph of a graph `G` is
`k`-colourable, then `G` is `k`-colourable. It is deduced from a graph-homomorphism compactness
result, built on Mathlib's Rado selection principle (`Finset.rado_selection`).

## Main results

* `nonempty_hom_of_forall_finite_subgraph_hom`: If every finite induced subgraph of `G`
  admits a homomorphism to `F`, then so does `G` (when `F` is finite).

* `deBruijn_erdos`: The de Bruijn–Erdős theorem: if every finite subgraph of a graph `G`
  is `k`-colourable, then `G` is `k`-colourable.

## References

* de Bruijn, N. G.; Erdős, P. (1951). "A colour problem for infinite graphs and a problem
  in the theory of relations".
-/

theorem nonempty_hom_of_forall_finite_subgraph_hom {V W : Type*} [Finite W]
    {G : SimpleGraph V} {F : SimpleGraph W}
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe →g F) : Nonempty (G →g F) := by
  have := G.toSubgraph
  let g : (s : Set V) → s.Finite → s → W := fun s hs ↦ h (SimpleGraph.Subgraph.induce ⊤ s) hs
  obtain ⟨χ, hχ⟩ := Set.Finite.rado_selection_subtype (β := fun _ ↦ W) g
  refine ⟨⟨χ, ?_⟩⟩
  intro a b hab
  let a' : (G.subgraphOfAdj hab).verts := ⟨a, by simp⟩
  let b' : (G.subgraphOfAdj hab).verts := ⟨b, by simp⟩
  have hab' : (G.subgraphOfAdj hab).Adj a' b' := by simp [a', b']
  change F.Adj (χ a') (χ b')
  obtain ⟨H, hHfin, hHsub, hHeq⟩ := hχ (G.subgraphOfAdj hab).verts (by simp)
  rw [hHeq, hHeq]
  simp only [g]
  apply (h ((⊤ : G.Subgraph).induce H) hHfin).map_adj
  simp only [SimpleGraph.subgraphOfAdj_verts, Set.insert_subset_iff,
    Set.singleton_subset_iff] at hHsub
  simp_all [a', b']

theorem deBruijn_erdos {α β : Type*} (G : SimpleGraph α) [Finite β]
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe.Coloring β) : Nonempty (G.Coloring β) :=
  nonempty_hom_of_forall_finite_subgraph_hom h
