/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Explicit Heyting Implication Computations

This file computes four concrete Heyting implications between geometric subfunctors
using TwoLabel {a, b}, demonstrating four distinct regimes of the geometric residual
via the Geometric Closure Theorem (Phase 186).

## Mathematical Content

Using the Geometric Closure Theorem:
  (S_φ ⟹ S_ψ)(G, v) ⟺ ψ.satisfies (ExtensionLTS G v φ) (inl v)

we compute the following:

1. **Independent diamonds**: ⟨a⟩⊤ → ⟨b⟩⊤ = ⟨b⟩⊤
   Extension adds a-edges only; b-structure unchanged.

2. **Non-trivial residual**: ⟨b⟩⊤ → (⟨a⟩⊤ ∧ ⟨b⟩⊤) = ⟨a⟩⊤
   Extension adds b-edges; ⟨b⟩⊤ auto-satisfied, ⟨a⟩⊤ unchanged.

3. **Depth-increasing**: ⟨a⟩⊤ → ⟨a⟩⟨b⟩⊤ = ⟨a⟩⟨b⟩⊤
   Fresh a-successor has no outgoing edges; can't satisfy ⟨b⟩⊤.

4. **Entailment**: ⟨a⟩⟨b⟩⊤ → ⟨a⟩⊤ = ⊤
   Fresh a-successor automatically exists; ⟨a⟩⊤ always satisfied.

## Key Definitions

- `himp_independent_diamonds`: ⟨a⟩⊤ → ⟨b⟩⊤ = ⟨b⟩⊤
- `himp_strip_free_part`: ⟨b⟩⊤ → (⟨a⟩⊤ ∧ ⟨b⟩⊤) = ⟨a⟩⊤
- `himp_depth_increasing`: ⟨a⟩⊤ → ⟨a⟩⟨b⟩⊤ = ⟨a⟩⟨b⟩⊤
- `himp_entailment`: ⟨a⟩⟨b⟩⊤ → ⟨a⟩⊤ = ⊤
- `geometric_himp_four_regimes`: Synthesis of all four regimes

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992)
- Caramello, "Theories, Sites, Toposes" (2018)
-/

import RuleSys.PresheafTopos.GeometricClosure

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

universe u

namespace RTS.PresheafTopos

/-!
## Part 1: TwoLabel Discrimination
-/

/-- TwoLabel.a and TwoLabel.b are distinct. -/
theorem TwoLabel.a_ne_b : TwoLabel.a ≠ TwoLabel.b := by decide

/-- TwoLabel.b and TwoLabel.a are distinct (symmetric form). -/
theorem TwoLabel.b_ne_a : TwoLabel.b ≠ TwoLabel.a := by decide

/-!
## Part 2: Formula Abbreviations

We define local abbreviations for the HMLPos formulas used in our four examples.
- φ_a = ⟨a⟩⊤ : "there exists an a-successor"
- φ_b = ⟨b⟩⊤ : "there exists a b-successor"
- φ_ab = ⟨a⟩⟨b⟩⊤ : "there exists an a-successor with a b-successor"
- φ_a_and_b = ⟨a⟩⊤ ∧ ⟨b⟩⊤ : "both an a-successor and a b-successor exist"
-/

private abbrev φ_a : HMLPos TwoLabel := diamondTop TwoLabel.a
private abbrev φ_b : HMLPos TwoLabel := diamondTop TwoLabel.b
private abbrev φ_ab : HMLPos TwoLabel := doubleDiamond TwoLabel.a TwoLabel.b
private abbrev φ_a_and_b : HMLPos TwoLabel := HMLPos.conj (diamondTop TwoLabel.a) (diamondTop TwoLabel.b)

/-!
## Part 3: Extension Edge Analysis

Key lemmas about edges in extensions by diamondTop formulas. These factor out
the repeated case analysis on `extensionEdge` and `rootEdge`.
-/

/-- In the extension by diamondTop a, a b-successor of inl v in the extension
    that is an inr witness vertex would require rootEdge (.diamond a .top) b w,
    which reduces to a = b. For distinct labels, this is impossible. -/
private theorem no_cross_label_witness_edge
    (G : FinLTS TwoLabel) (v : G.Vertex) (a b : TwoLabel) (h_ne : a ≠ b)
    (w : WitnessVertex TwoLabel (diamondTop a))
    (h : extensionEdge G v (diamondTop a) b (.inl v) (.inr w)) : False := by
  obtain ⟨_, h_root⟩ := h
  have := witnessVertex_diamondTop_unique a w
  subst this
  simp [rootEdge] at h_root
  exact h_ne h_root

/-!
## Part 4: Example 1 — Independent Diamonds

⟨a⟩⊤ → ⟨b⟩⊤ = ⟨b⟩⊤

Extension by diamondTop a adds only an a-edge from v to freshSucc a .top.
Since a ≠ b, there are no new b-edges. So ⟨b⟩⊤ in the extension is equivalent
to ⟨b⟩⊤ in the original G.
-/

/-- **Example 1**: ⟨a⟩⊤ → ⟨b⟩⊤ = ⟨b⟩⊤ (independent labels).
    When φ and ψ involve different labels, the Heyting implication is just ψ:
    the extension by φ adds no relevant structure for ψ. -/
theorem himp_independent_diamonds (G : FinLTS TwoLabel) (v : G.Vertex) :
    (φ_a.toSubfunctor.himp φ_b.toSubfunctor).pred G v ↔
    φ_b.satisfies G v := by
  rw [geometric_closure_theorem]
  -- Goal: φ_b.satisfies (ExtensionLTS G v φ_a) (.inl v) ↔ φ_b.satisfies G v
  constructor
  · -- Forward: b-successor in extension → b-successor in G
    intro ⟨w, h_edge, h_sat⟩
    match w with
    | .inl t =>
      exact ⟨t, h_edge, trivial⟩
    | .inr w' =>
      exact absurd h_edge (no_cross_label_witness_edge G v .a .b TwoLabel.a_ne_b w')
  · -- Backward: b-successor in G → b-successor in extension
    intro ⟨t, h_edge, _⟩
    exact ⟨.inl t, h_edge, trivial⟩

/-!
## Part 5: Example 2 — Non-trivial Residual (Strip Free Part)

⟨b⟩⊤ → (⟨a⟩⊤ ∧ ⟨b⟩⊤) = ⟨a⟩⊤

Extension by diamondTop b adds a fresh b-successor (freshSucc b .top).
In the extension, ⟨b⟩⊤ is automatically satisfied at inl v.
For ⟨a⟩⊤: rootEdge (.diamond b .top) a (freshSucc b .top) = (b = a) = False,
so a-successors are unchanged. The conjunction reduces to ⟨a⟩⊤ in G.
-/

/-- **Example 2**: ⟨b⟩⊤ → (⟨a⟩⊤ ∧ ⟨b⟩⊤) = ⟨a⟩⊤ (strips free part).
    The extension by ⟨b⟩⊤ automatically satisfies the ⟨b⟩⊤ conjunct,
    so the residual is just the remaining ⟨a⟩⊤. -/
theorem himp_strip_free_part (G : FinLTS TwoLabel) (v : G.Vertex) :
    (φ_b.toSubfunctor.himp φ_a_and_b.toSubfunctor).pred G v ↔
    φ_a.satisfies G v := by
  rw [geometric_closure_theorem]
  -- Goal: φ_a_and_b.satisfies (ExtensionLTS G v φ_b) (.inl v) ↔ φ_a.satisfies G v
  -- φ_a_and_b.satisfies = φ_a.satisfies ∧ φ_b.satisfies
  constructor
  · -- Forward: (⟨a⟩⊤ ∧ ⟨b⟩⊤) in extension → ⟨a⟩⊤ in G
    intro ⟨h_a_ext, _⟩
    obtain ⟨w, h_edge, _⟩ := h_a_ext
    match w with
    | .inl t =>
      exact ⟨t, h_edge, trivial⟩
    | .inr w' =>
      exact absurd h_edge (no_cross_label_witness_edge G v .b .a TwoLabel.b_ne_a w')
  · -- Backward: ⟨a⟩⊤ in G → (⟨a⟩⊤ ∧ ⟨b⟩⊤) in extension
    intro ⟨t, h_edge, _⟩
    constructor
    · -- ⟨a⟩⊤ in extension: use the same a-successor from G
      exact ⟨.inl t, h_edge, trivial⟩
    · -- ⟨b⟩⊤ in extension: use the fresh witness
      exact ⟨.inr (.freshSucc TwoLabel.b .top), ⟨rfl, rfl⟩, trivial⟩

/-!
## Part 6: Example 3 — Depth-Increasing

⟨a⟩⊤ → ⟨a⟩⟨b⟩⊤ = ⟨a⟩⟨b⟩⊤

Extension by diamondTop a adds freshSucc a .top. This vertex has NO outgoing edges
because WitnessVertex .top is empty (no internal edges from freshSucc).
So the fresh a-successor cannot satisfy ⟨b⟩⊤. Must use original a-successors.
-/

/-- The fresh successor in a diamondTop extension has no outgoing edges in the extension:
    for any label c and target vertex u, there is no edge from inr (freshSucc a .top) to u. -/
private theorem freshSucc_top_no_outgoing
    (G : FinLTS TwoLabel) (v : G.Vertex) (a : TwoLabel) (c : TwoLabel)
    (u : (ExtensionLTS G v (diamondTop a)).Vertex) :
    ¬(ExtensionLTS G v (diamondTop a)).edge c (.inr (.freshSucc a .top)) u := by
  intro h
  match u with
  | .inl _ => exact h
  | .inr w' =>
    have := witnessVertex_diamondTop_unique a w'
    subst this
    -- h : internalEdge (.diamond a .top) c (.freshSucc a .top) (.freshSucc a .top)
    -- This is False by definition
    exact h

/-- **Example 3**: ⟨a⟩⊤ → ⟨a⟩⟨b⟩⊤ = ⟨a⟩⟨b⟩⊤ (shallow extension can't satisfy deeper formula).
    The diamondTop extension adds a fresh a-successor with no outgoing edges,
    so it cannot satisfy ⟨b⟩⊤. The deeper formula ⟨a⟩⟨b⟩⊤ must be witnessed
    by original vertices in G. -/
theorem himp_depth_increasing (G : FinLTS TwoLabel) (v : G.Vertex) :
    (φ_a.toSubfunctor.himp φ_ab.toSubfunctor).pred G v ↔
    φ_ab.satisfies G v := by
  rw [geometric_closure_theorem]
  -- Goal: φ_ab.satisfies (ExtensionLTS G v φ_a) (.inl v) ↔ φ_ab.satisfies G v
  constructor
  · -- Forward: ⟨a⟩⟨b⟩⊤ in extension → ⟨a⟩⟨b⟩⊤ in G
    intro ⟨w, h_a_edge, u, h_b_edge, _⟩
    match w with
    | .inl t =>
      match u with
      | .inl s =>
        exact ⟨t, h_a_edge, s, h_b_edge, trivial⟩
      | .inr w' =>
        -- b-edge from inl t to inr w': extensionEdge gives t = v ∧ rootEdge φ_a b w'
        -- rootEdge (.diamond a .top) b w' with w' = freshSucc a .top gives a = b
        have h_root := h_b_edge.2
        have := witnessVertex_diamondTop_unique TwoLabel.a w'
        subst this
        simp [rootEdge] at h_root
    | .inr w' =>
      -- a-successor is the fresh witness vertex freshSucc a .top
      -- This vertex has no outgoing edges
      have hw := witnessVertex_diamondTop_unique TwoLabel.a w'
      subst hw
      exact absurd h_b_edge (freshSucc_top_no_outgoing G v TwoLabel.a TwoLabel.b u)
  · -- Backward: ⟨a⟩⟨b⟩⊤ in G → ⟨a⟩⟨b⟩⊤ in extension
    intro ⟨t, h_a_edge, s, h_b_edge, _⟩
    exact ⟨.inl t, h_a_edge, .inl s, h_b_edge, trivial⟩

/-!
## Part 7: Example 4 — Entailment Collapses to Top

⟨a⟩⟨b⟩⊤ → ⟨a⟩⊤ = ⊤

Extension by doubleDiamond a b adds:
- freshSucc a (.diamond b .top): a-successor of v
- succWitness a (.diamond b .top) (freshSucc b .top): b-successor of freshSucc

So rootEdge φ_ab a (freshSucc a (.diamond b .top)) = (a = a) = True.
The fresh a-successor always exists, so ⟨a⟩⊤ is automatically satisfied
for any (G, v).
-/

/-- **Example 4**: ⟨a⟩⟨b⟩⊤ → ⟨a⟩⊤ = ⊤ (entailment collapses to top).
    When φ logically implies ψ (doubleDiamond a b implies diamondTop a),
    the Heyting implication is trivially true: the free extension by the stronger
    formula provides the weaker one for free. -/
theorem himp_entailment (G : FinLTS TwoLabel) (v : G.Vertex) :
    (φ_ab.toSubfunctor.himp φ_a.toSubfunctor).pred G v ↔ True := by
  rw [geometric_closure_theorem]
  -- Goal: φ_a.satisfies (ExtensionLTS G v φ_ab) (.inl v) ↔ True
  constructor
  · intro _; trivial
  · -- Show ⟨a⟩⊤ in the doubleDiamond extension: provide the fresh a-successor
    intro _
    -- The witness is freshSucc a (.diamond b .top)
    refine ⟨.inr (.freshSucc TwoLabel.a (.diamond TwoLabel.b .top)), ?_, trivial⟩
    -- extensionEdge: v = v ∧ rootEdge φ_ab a (freshSucc a (.diamond b .top))
    -- rootEdge (.diamond a (.diamond b .top)) a (freshSucc a (.diamond b .top)) = (a = a)
    exact ⟨rfl, rfl⟩

/-!
## Part 8: Synthesis — Four Regimes of Geometric Heyting Implication

The four examples above demonstrate the four qualitatively different behaviors
of the Heyting implication between geometric subfunctors:

1. **Independent** (⟨a⟩⊤ → ⟨b⟩⊤ = ⟨b⟩⊤): When φ and ψ involve orthogonal
   structure (different labels), the extension adds nothing relevant to ψ.

2. **Non-trivial residual** (⟨b⟩⊤ → (⟨a⟩⊤ ∧ ⟨b⟩⊤) = ⟨a⟩⊤): When ψ partially
   overlaps φ, the Heyting implication strips out the free (φ-provided) part,
   leaving the genuine residual.

3. **Depth-increasing** (⟨a⟩⊤ → ⟨a⟩⟨b⟩⊤ = ⟨a⟩⟨b⟩⊤): When ψ is strictly deeper
   than φ at the same label, the shallow extension cannot contribute to ψ.

4. **Entailment** (⟨a⟩⟨b⟩⊤ → ⟨a⟩⊤ = ⊤): When φ implies ψ, the Heyting
   implication collapses to ⊤ (the full subfunctor).
-/

/-- **Four Regimes of Geometric Heyting Implication**: Synthesis theorem combining
    all four examples into a single conjunction, demonstrating the full range of
    behavior of the presheaf Heyting implication between geometric subfunctors. -/
theorem geometric_himp_four_regimes (G : FinLTS TwoLabel) (v : G.Vertex) :
    -- Regime 1: Independent (himp = ψ)
    ((φ_a.toSubfunctor.himp φ_b.toSubfunctor).pred G v ↔ φ_b.satisfies G v) ∧
    -- Regime 2: Non-trivial residual (himp strips free part)
    ((φ_b.toSubfunctor.himp φ_a_and_b.toSubfunctor).pred G v ↔ φ_a.satisfies G v) ∧
    -- Regime 3: Depth-increasing (himp = ψ, shallow can't satisfy deep)
    ((φ_a.toSubfunctor.himp φ_ab.toSubfunctor).pred G v ↔ φ_ab.satisfies G v) ∧
    -- Regime 4: Entailment (himp = ⊤)
    ((φ_ab.toSubfunctor.himp φ_a.toSubfunctor).pred G v ↔ True) :=
  ⟨himp_independent_diamonds G v,
   himp_strip_free_part G v,
   himp_depth_increasing G v,
   himp_entailment G v⟩

end RTS.PresheafTopos
