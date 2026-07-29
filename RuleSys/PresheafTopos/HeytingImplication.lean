/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Heyting Implication on the Subobject Classifier

For the presheaf topos [f.p.LTS₁^op, Set], the subobject classifier Ω(G) = {sieves on G}
carries a Heyting algebra structure. This file defines the Heyting implication on sieves,
proves the adjunction property, and demonstrates the "Heyting gap": despite degenerate
negation (¬S = ∅ for non-empty S), the implication S₁ → S₂ remains informative.

## Key Results

- `DigraphSieve.himp`: Heyting implication on sieves
- `himp_adjunction`: S₁ ∩ T ⊆ S₂ ↔ T ⊆ S₁ → S₂
- `himp_empty_eq_negation`: (S → ∅) = ¬S
- `heyting_gap`: ∃ sieves where S₁ → S₂ is neither ∅ nor ⊤

## The Heyting Gap

The negation-collapse parallel:
- In L₃₀: ¬x = ⊥ for all x ≠ ⊥, but S → F = IF (informative implication)
- In Ω(G): ¬S = ∅ for non-empty S, but S₁ → S₂ can be intermediate

This is NOT a coincidence: both are instances of the same mechanism. When every
non-trivial element shares a common lower bound that makes complementation impossible,
negation degenerates while implication preserves structure. The topos "sees" more
logical structure than classical HML through its intuitionistic implication.

## Limitation for |L| = 1

For single-label systems, ready simulation = simulation (upper spectrum collapse from
Phase 109). The ready-simulation conjecture — that Heyting implication corresponds to
ready simulation — requires |L| ≥ 2 to be non-trivially testable.

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992), §I.8 (Heyting algebras)
-/

import RuleSys.PresheafTopos.SubobjectClassifier

set_option autoImplicit false

namespace RTS.PresheafTopos

/-!
## Part 1: Sieve Operations
-/

/-- Intersection of sieves: f ∈ S₁ ∩ S₂ iff f ∈ S₁ and f ∈ S₂. -/
def DigraphSieve.inter {G : FinDigraph} (S₁ S₂ : DigraphSieve G) : DigraphSieve G where
  mem := fun H f => S₁.mem H f ∧ S₂.mem H f
  precomp_closed := fun f h ⟨h1, h2⟩ => ⟨S₁.precomp_closed f h h1, S₂.precomp_closed f h h2⟩

/-- Ordering on sieves: S₁ ≤ S₂ iff every morphism in S₁ is also in S₂. -/
def DigraphSieve.le {G : FinDigraph} (S₁ S₂ : DigraphSieve G) : Prop :=
  ∀ (H : FinDigraph) (f : DigraphHom H G), S₁.mem H f → S₂.mem H f

/-!
## Part 2: The Heyting Implication
-/

/-- The Heyting implication on sieves.

    (S₁ → S₂).mem H f iff for every K and h : K → H, if (f ∘ h) ∈ S₁ then (f ∘ h) ∈ S₂.

    This is the standard presheaf-theoretic definition: f belongs to the implication sieve
    iff the "pullback" of S₁ along f is contained in the "pullback" of S₂ along f.
    Equivalently, f "transforms S₁-membership into S₂-membership." -/
def DigraphSieve.himp {G : FinDigraph} (S₁ S₂ : DigraphSieve G) : DigraphSieve G where
  mem := fun H f => ∀ (K : FinDigraph) (h : DigraphHom K H),
    S₁.mem K (DigraphHom.comp h f) → S₂.mem K (DigraphHom.comp h f)
  precomp_closed := fun {_H K} f g hf L h hmem => by
    -- hf : ∀ M k, S₁.mem M (comp k f) → S₂.mem M (comp k f)
    -- Need: S₂.mem L (comp h (comp g f))
    -- comp h (comp g f) = comp (comp h g) f
    rw [← DigraphHom.comp_assoc] at hmem ⊢
    exact hf L (DigraphHom.comp h g) hmem

/-!
## Part 3: Properties
-/

/-- The Heyting adjunction: S₁ ∩ T ≤ S₂ iff T ≤ (S₁ → S₂).

    This is the defining property of the Heyting implication in Ω(G). -/
theorem himp_adjunction {G : FinDigraph} (S₁ S₂ T : DigraphSieve G) :
    (S₁.inter T).le S₂ ↔ T.le (S₁.himp S₂) := by
  constructor
  · -- Forward: S₁ ∩ T ≤ S₂ implies T ≤ S₁ → S₂
    intro h H f hTf K g hS1
    -- Need: S₂.mem K (comp g f)
    -- We know: T.mem H f, S₁.mem K (comp g f)
    -- By precomp_closed: T.mem K (comp g f) follows from T.mem H f
    have hTgf : T.mem K (DigraphHom.comp g f) := T.precomp_closed f g hTf
    exact h K (DigraphHom.comp g f) ⟨hS1, hTgf⟩
  · -- Backward: T ≤ S₁ → S₂ implies S₁ ∩ T ≤ S₂
    intro h H f ⟨hS1, hT⟩
    -- Need: S₂.mem H f
    -- h gives: T.mem H f → (S₁ → S₂).mem H f
    have himpl := h H f hT
    -- himpl : ∀ K g, S₁.mem K (comp g f) → S₂.mem K (comp g f)
    -- Take K = H, g = id
    have := himpl H (DigraphHom.id H)
    rw [DigraphHom.id_comp] at this
    exact this hS1

/-- Heyting negation is implication into ∅: (S → ∅) = ¬S.

    This connects the Heyting implication to the negation defined in SubobjectClassifier. -/
theorem himp_empty_eq_negation {G : FinDigraph} (S : DigraphSieve G) :
    ∀ (H : FinDigraph) (f : DigraphHom H G),
      (S.himp (DigraphSieve.empty G)).mem H f ↔ S.negation.mem H f := by
  intro H f
  -- himp(S, ∅).mem H f ↔ ∀ K h, S.mem K (comp h f) → False
  -- negation.mem H f ↔ ∀ K h, ¬S.mem K (comp h f)
  -- These are the same!
  constructor
  · exact fun h K g => h K g
  · exact fun h K g => h K g

/-- If both S₁ and S₂ contain the initial morphism, so does S₁ → S₂.

    Proof: (himp S₁ S₂).mem ∅ !_G means ∀ K h, S₁.mem K (comp h !_G) → S₂.mem K (comp h !_G).
    But comp h !_G = !_G (uniqueness of morphisms from K through ∅ to G).
    So this reduces to: S₁.mem K !_G → S₂.mem K !_G.
    Since comp h !_G = !_G for all K, h, this becomes: checking at K = ∅ with h = id.
    At K = ∅: S₁.mem ∅ !_G → S₂.mem ∅ !_G, which holds by hypothesis. -/
theorem himp_preserves_initial {G : FinDigraph} {S₁ S₂ : DigraphSieve G}
    (_h1 : S₁.mem emptyDigraph (emptyDigraph_to G))
    (h2 : S₂.mem emptyDigraph (emptyDigraph_to G)) :
    (S₁.himp S₂).mem emptyDigraph (emptyDigraph_to G) := by
  intro K h _
  -- h : K → emptyDigraph, so K.Vertex is empty
  -- By precomp_closed: S₂.mem emptyDigraph (!_G) and h : K → emptyDigraph
  -- gives S₂.mem K (comp h (!_G))
  exact S₂.precomp_closed (emptyDigraph_to G) h h2

/-!
## Part 4: Concrete Computations
-/

/-- The initial sieve is "below everything": atom → S = maximal for any non-empty S.
    For S₁ = initial sieve (only empty-source morphisms), S₂ = maximal:
    himp(init, max).mem H f = ∀ K h, IsEmpty K.Vertex → True = True.
    So himp(init, max) = max. -/
theorem himp_initial_maximal (G : FinDigraph) :
    ∀ (H : FinDigraph) (f : DigraphHom H G),
      ((DigraphSieve.initial G).himp (DigraphSieve.maximal G)).mem H f := by
  intro H f K _ _
  trivial

/-- The maximal sieve into the initial sieve gives the initial sieve.
    himp(max, init).mem H f = ∀ K h, True → IsEmpty K.Vertex.
    This requires ALL K mapping to H to have empty vertex type, which holds iff
    H itself has empty vertex type (take K = H, h = id). -/
theorem himp_maximal_initial (G : FinDigraph) (H : FinDigraph) (f : DigraphHom H G) :
    ((DigraphSieve.maximal G).himp (DigraphSieve.initial G)).mem H f ↔
    IsEmpty H.Vertex := by
  constructor
  · -- If f ∈ himp(max, init), take K = H, h = id
    intro h
    have := h H (DigraphHom.id H)
    rw [DigraphHom.id_comp] at this
    exact this trivial
  · -- If H is empty, then for any K, h : K → H, K must also be empty
    intro hempty K h _
    exact ⟨fun v => (hempty.false (h.toFun v)).elim⟩

/-!
## Part 5: The Heyting Gap

The key demonstration: implication produces non-degenerate values even though
negation collapses. We show this using the initial and maximal sieves.
-/

/-- **The Heyting Gap:** The implication ⊤ → atom(G) is neither ∅ nor ⊤.

    - It's not ∅: it contains the initial morphism !_G (since !_G ∈ atom).
    - It's not ⊤: for non-empty G with a vertex v, the identity id_G has
      (himp max init).mem G id ↔ IsEmpty G.Vertex, which fails.

    This demonstrates that the Heyting implication carries genuine information
    beyond what degenerate negation provides. -/
theorem heyting_gap :
    ∃ (G : FinDigraph) (S₁ S₂ : DigraphSieve G),
      -- himp is non-empty (contains initial morphism)
      (S₁.himp S₂).mem emptyDigraph (emptyDigraph_to G) ∧
      -- himp is not maximal (misses id_G)
      ¬(S₁.himp S₂).mem G (DigraphHom.id G) := by
  -- Take G = loopVertex, S₁ = maximal, S₂ = initial
  refine ⟨loopVertex, DigraphSieve.maximal loopVertex, DigraphSieve.initial loopVertex, ?_, ?_⟩
  · -- Initial morphism is in himp(max, init)
    intro K h _
    exact ⟨fun v => (IsEmpty.false (h.toFun v) : False).elim⟩
  · -- id_•₁ is NOT in himp(max, init)
    intro h
    have := (himp_maximal_initial loopVertex loopVertex (DigraphHom.id loopVertex)).mp h
    exact this.false ()

/-- The negation-collapse parallel: for any non-empty sieve S on any G,
    ¬S = S → ∅ = ∅ (degenerate negation), but S₁ → S₂ can be non-trivial
    (the Heyting gap). This mirrors L₃₀ where ¬x = ⊥ for all x ≠ ⊥
    but the Heyting implication S → F = IF is informative.

    Both phenomena have the same root cause: the unique atom theorem
    (every non-empty sieve shares a common element !_G) prevents
    complementation but leaves conditional reasoning intact. -/
theorem negation_collapse_with_informative_implication :
    -- (1) Negation is degenerate: ¬S = ∅ for non-empty S
    (∀ (G : FinDigraph) (S : DigraphSieve G),
      S.mem emptyDigraph (emptyDigraph_to G) →
      ∀ H f, ¬S.negation.mem H f) ∧
    -- (2) Implication is informative: ∃ non-trivial himp
    (∃ (G : FinDigraph) (S₁ S₂ : DigraphSieve G),
      (S₁.himp S₂).mem emptyDigraph (emptyDigraph_to G) ∧
      ¬(S₁.himp S₂).mem G (DigraphHom.id G)) :=
  ⟨fun _G S h H f => negation_of_nonempty_is_empty S h H f,
   heyting_gap⟩

end RTS.PresheafTopos
