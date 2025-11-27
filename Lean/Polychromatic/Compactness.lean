import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness and the Rado Selection Principle

This file contains compactness arguments for constructing infinite objects from finite
approximations. The main result is a formalization of Rado's selection principle.

## Main results

* `Finset.rado_selection`: Given functions `g : Finset α → α → β` where `β` is finite,
  there exists a single function `χ : α → β` that agrees with infinitely many `g s` on `s`.
  More precisely, for each finite set `s`, there exists a larger set `t ⊇ s` such that
  `χ` and `g t` agree on `s`.

* `Finset.rado_selection_subtype`: A variant where `g` takes subtype elements.

* `Set.Finite.rado_selection`: Extension to finite subsets of arbitrary sets.

* `nonempty_hom_of_forall_finite_subgraph_hom`: If every finite induced subgraph of `G`
  admits a homomorphism to `F`, then so does `G` (when `F` is finite).

* `deBruijn_erdos`: The de Bruijn–Erdős theorem: if every finite subgraph of a graph `G`
  is `k`-colourable, then `G` is `k`-colourable.

## Implementation notes

The proof uses the fact that the product of finite discrete spaces is compact
(by Tychonoff's theorem). The closed sets corresponding to "agreeing with `g s` on `s`"
have the finite intersection property, so their intersection is nonempty.

## References

* de Bruijn, N. G.; Erdős, P. (1951). "A colour problem for infinite graphs and a problem
  in the theory of relations".
* Rado, R. (1949). "Axiomatic treatment of rank in infinite sets".
-/

theorem Finset.rado_selection {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Finset α) → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α, ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x := by
  classical
  let instTop (a : α) : TopologicalSpace (β a) := ⊥
  have instDiscr (a : α) : DiscreteTopology (β a) := discreteTopology_bot _
  let e (s : Finset α) : Set ((a : α) → β a) := {f | ∃ t, s ⊆ t ∧ ∀ x ∈ s, f x = g t x}
  let restr (s : Finset α) : ((a : α) → β a) → (a : s) → β a := fun f a ↦ f a
  have hrestr (s : Finset α) : Continuous (restr s) := by fun_prop
  have (s : Finset α) : restr s ⁻¹' {f | ∃ t, s ⊆ t ∧ ∀ x, f x = g t x} = e s := by simp [e, restr]
  have he' (s : Finset α) : IsClosed (e s) := by
    rw [← this]
    exact (isClosed_discrete _).preimage (hrestr _)
  have he'' (B : Finset (Finset α)) : (⋂ i ∈ B, e i).Nonempty := by
    refine ⟨g (B.biUnion id), ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq, e]
    intro i hi
    exact ⟨_, Finset.subset_biUnion_of_mem id hi, by simp⟩
  simpa using CompactSpace.iInter_nonempty he' he''

theorem Finset.rado_selection_subtype {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Finset α) → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α,
      ∃ (t : Finset α) (hst : s ⊆ t), ∀ x : s, χ x = g t (Set.inclusion hst x) := by
  classical
  have (a : α) : Nonempty (β a) := ⟨g {a} ⟨a, by simp⟩⟩
  let g' (s) (a : α) : β a := if ha : a ∈ s then g s ⟨a, ha⟩ else Classical.arbitrary (β a)
  have hg (s : Finset α) (x : s) : g s x = g' s x := by simp [g']
  simpa [hg] using Finset.rado_selection g'

theorem Set.Finite.rado_selection {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Set α) → s.Finite → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite), s ⊆ t ∧ ∀ x ∈ s, χ x = g t ht x := by
  obtain ⟨χ, hχ⟩ := Finset.rado_selection (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, ht'⟩ := hχ hs.toFinset
  exact ⟨t, by simp_all⟩

theorem Set.Finite.rado_selection_subtype {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Set α) → s.Finite → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite) (hst : s ⊆ t), ∀ x : s, χ x = g t ht (Set.inclusion hst x) := by
  classical
  obtain ⟨χ, hχ⟩ := Finset.rado_selection_subtype (β := β) (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, hst⟩ := hχ hs.toFinset
  simp only [Set.Finite.toFinset_subset] at ht
  exact ⟨t, by simp_all⟩

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
  simp only [SimpleGraph.subgraphOfAdj_verts, SimpleGraph.Subgraph.induce_verts, g]
  apply (h ((⊤ : G.Subgraph).induce H) hHfin).map_adj
  simp only [SimpleGraph.subgraphOfAdj_verts, Set.insert_subset_iff,
    Set.singleton_subset_iff] at hHsub
  simp_all [a', b']

theorem deBruijn_erdos {α β : Type*} (G : SimpleGraph α) [Finite β]
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe.Coloring β) : Nonempty (G.Coloring β) :=
  nonempty_hom_of_forall_finite_subgraph_hom h
