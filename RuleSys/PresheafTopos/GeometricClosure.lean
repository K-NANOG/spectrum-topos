/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric Closure Theorem

This file proves the Geometric Closure Theorem for geometric subfunctors of the
generic model U_T in the presheaf topos Set[T_LTS] = [f.p.LTS_L^op, Set].

## Mathematical Content

The geometric closure theorem characterizes the presheaf Heyting implication
S_φ ⟹ S_ψ of two geometric subfunctors (arising from HMLPos formulas φ and ψ)
in terms of the Free Extension Lemma. Specifically:

  (S_φ ⟹ S_ψ)(G, v) ⟺ ψ.satisfies (ExtensionLTS G v φ) (inl v)

The forward direction instantiates the Heyting implication with the free extension
homomorphism. The backward direction constructs a mediating homomorphism from the
extension into any target LTS using satisfaction witnesses, then applies forward
preservation.

## Key Definitions

- `LTSSubfunctor.le`: Ordering on subfunctors (pointwise implication)
- `LTSSubfunctor.meet`: Meet (intersection) of subfunctors
- `LTSSubfunctor.himp`: Presheaf Heyting implication of subfunctors
- `witnessMap`: Maps witness vertices into a target LTS using satisfaction proofs
- `mediatingHom`: The mediating homomorphism ExtensionLTS G v φ → H
- `geometric_closure_theorem`: Main iff characterization
- `geometric_closure_negation_corollary`: Connection to Phase 185 negation collapse
- `geometric_himp_adjunction`: Standard Heyting adjunction for geometric subfunctors

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992) -- Heyting algebra in presheaf toposes
- Caramello, "Theories, Sites, Toposes" (2018) -- geometric logic and classifying toposes
-/

import RuleSys.PresheafTopos.NegationCollapse

set_option autoImplicit false

universe u

namespace RTS.PresheafTopos

/-!
## Part 1: Subfunctor Ordering and Meet
-/

/-- Ordering on subfunctors: pointwise implication of predicates. -/
def LTSSubfunctor.le {L : Type} [Fintype L] [DecidableEq L]
    (S₁ S₂ : LTSSubfunctor L) : Prop :=
  ∀ (G : FinLTS L) (v : G.Vertex), S₁.pred G v → S₂.pred G v

/-- Meet (intersection) of subfunctors with naturality inherited from both components. -/
def LTSSubfunctor.meet {L : Type} [Fintype L] [DecidableEq L]
    (S₁ S₂ : LTSSubfunctor L) : LTSSubfunctor L where
  pred := fun G v => S₁.pred G v ∧ S₂.pred G v
  natural := fun f v ⟨h1, h2⟩ => ⟨S₁.natural f v h1, S₂.natural f v h2⟩

/-!
## Part 2: Presheaf Heyting Implication on Subfunctors
-/

/-- The presheaf Heyting implication of subfunctors S₁ ⟹ S₂.

    (S₁ ⟹ S₂)(G, v) holds iff for every H and h : G → H,
    S₁(H, h(v)) implies S₂(H, h(v)).

    This is the standard formula for implication in [C^op, Set]:
      (S₁ ⟹ S₂)(G, v) = ∀ H, ∀ h : G → H, S₁(H, h(v)) → S₂(H, h(v))

    Naturality: if v ∈ (S₁ ⟹ S₂)(G) and f : G → K, then for any h : K → H,
    (h ∘ f) : G → H is a morphism, so S₁(H, (h∘f)(v)) → S₂(H, (h∘f)(v)),
    which gives S₁(H, h(f(v))) → S₂(H, h(f(v))), proving f(v) ∈ (S₁ ⟹ S₂)(K). -/
def LTSSubfunctor.himp {L : Type} [Fintype L] [DecidableEq L]
    (S₁ S₂ : LTSSubfunctor L) : LTSSubfunctor L where
  pred := fun G v =>
    ∀ (H : FinLTS L) (h : LTSHom G H), S₁.pred H (h.toFun v) → S₂.pred H (h.toFun v)
  natural := fun {G K} f v hv H h => by
    intro h_s1
    have := hv H (LTSHom.comp f h)
    simp [LTSHom.comp] at this
    exact this h_s1

/-!
## Part 3: Forward Direction of Geometric Closure
-/

/-- Forward direction: if (S_φ ⟹ S_ψ)(G, v) holds, then ψ is satisfied at inl v
    in the free extension ExtensionLTS G v φ.

    Proof: Instantiate the Heyting implication with H = ExtensionLTS G v φ and
    h = extensionInj G v φ. Since φ is satisfied at inl v in the extension
    (by witness_satisfies_at_root), we get ψ satisfied at inl v. -/
theorem geometric_closure_forward {L : Type} [Fintype L] [DecidableEq L]
    (phi psi : HMLPos L) (G : FinLTS L) (v : G.Vertex)
    (h_himp : (phi.toSubfunctor.himp psi.toSubfunctor).pred G v) :
    psi.satisfies (ExtensionLTS G v phi) (.inl v) := by
  have h_ext := h_himp (ExtensionLTS G v phi) (extensionInj G v phi)
  exact h_ext (witness_satisfies_at_root G v phi)

/-!
## Part 4: Witness Map Construction

The witness map sends each witness vertex (demanded by φ) to a vertex in H,
using the satisfaction proof to choose the actual witnesses via Exists.choose.
This is the heart of the mediating homomorphism construction.
-/

/-- Map witness vertices of φ into the vertex type of H, given that φ is satisfied
    at some root vertex in H. Uses Exists.choose to pick actual witnesses for
    diamond modalities.

    The function is noncomputable because it uses Exists.choose (choice principle)
    to select witnesses from existential satisfaction proofs. -/
noncomputable def witnessMap {L : Type} [Fintype L] [DecidableEq L]
    (H : FinLTS L) : (phi : HMLPos L) → (root : H.Vertex) →
    phi.satisfies H root → WitnessVertex L phi → H.Vertex
  | .diamond _a _psi, _root, h_sat, .freshSucc _ _ =>
    h_sat.choose
  | .diamond _a psi, _root, h_sat, .succWitness _ _ w =>
    witnessMap H psi h_sat.choose h_sat.choose_spec.2 w
  | .conj phi _psi, root, h_sat, .ofLeft _ _ w =>
    witnessMap H phi root h_sat.1 w
  | .conj _phi psi, root, h_sat, .ofRight _ _ w =>
    witnessMap H psi root h_sat.2 w

/-!
## Part 5: Witness Map Edge Preservation

The witnessMap preserves the edge structure of the witness tree: rootEdge and
internalEdge in the witness tree correspond to actual edges in H.
-/

/-- rootEdge in the witness tree maps to an edge from root in H. -/
theorem witnessMap_rootEdge {L : Type} [Fintype L] [DecidableEq L]
    (H : FinLTS L) : (phi : HMLPos L) → (root : H.Vertex) →
    (h_sat : phi.satisfies H root) →
    (a : L) → (w : WitnessVertex L phi) →
    rootEdge phi a w → H.edge a root (witnessMap H phi root h_sat w)
  | .diamond b psi, root, h_sat, a, .freshSucc _ _, h_re => by
    -- h_re : b = a, need: H.edge a root h_sat.choose
    simp [rootEdge] at h_re
    rw [← h_re]
    simp [witnessMap]
    exact h_sat.choose_spec.1
  | .diamond _ _, _, _, _, .succWitness _ _ _, h_re => by
    exact absurd h_re id
  | .conj phi psi, root, h_sat, a, .ofLeft _ _ w, h_re => by
    simp [witnessMap]
    exact witnessMap_rootEdge H phi root h_sat.1 a w h_re
  | .conj phi psi, root, h_sat, a, .ofRight _ _ w, h_re => by
    simp [witnessMap]
    exact witnessMap_rootEdge H psi root h_sat.2 a w h_re

/-- internalEdge in the witness tree maps to an edge between witness images in H. -/
theorem witnessMap_internalEdge {L : Type} [Fintype L] [DecidableEq L]
    (H : FinLTS L) : (phi : HMLPos L) → (root : H.Vertex) →
    (h_sat : phi.satisfies H root) →
    (a : L) → (w w' : WitnessVertex L phi) →
    internalEdge phi a w w' →
    H.edge a (witnessMap H phi root h_sat w) (witnessMap H phi root h_sat w')
  | .diamond b psi, root, h_sat, a, .freshSucc _ _, .succWitness _ _ w', h_ie => by
    -- h_ie : rootEdge psi a w'
    simp [witnessMap]
    exact witnessMap_rootEdge H psi h_sat.choose h_sat.choose_spec.2 a w' h_ie
  | .diamond b psi, root, h_sat, a, .succWitness _ _ w, .succWitness _ _ w', h_ie => by
    -- h_ie : internalEdge psi a w w'
    simp [witnessMap]
    exact witnessMap_internalEdge H psi h_sat.choose h_sat.choose_spec.2 a w w' h_ie
  | .diamond _ _, _, _, _, .freshSucc _ _, .freshSucc _ _, h_ie => by
    exact absurd h_ie id
  | .diamond _ _, _, _, _, .succWitness _ _ _, .freshSucc _ _, h_ie => by
    exact absurd h_ie id
  | .conj phi psi, _, h_sat, a, .ofLeft _ _ w, .ofLeft _ _ w', h_ie => by
    simp [witnessMap]
    exact witnessMap_internalEdge H phi _ h_sat.1 a w w' h_ie
  | .conj phi psi, _, h_sat, a, .ofRight _ _ w, .ofRight _ _ w', h_ie => by
    simp [witnessMap]
    exact witnessMap_internalEdge H psi _ h_sat.2 a w w' h_ie
  | .conj _ _, _, _, _, .ofLeft _ _ _, .ofRight _ _ _, h_ie => by
    exact absurd h_ie id
  | .conj _ _, _, _, _, .ofRight _ _ _, .ofLeft _ _ _, h_ie => by
    exact absurd h_ie id

/-!
## Part 6: Mediating Homomorphism
-/

/-- The mediating homomorphism from ExtensionLTS G v φ to H.

    Given h : G → H with φ satisfied at h(v) in H, we construct a homomorphism
    from the free extension to H that:
    - maps inl s to h(s) (preserving the original vertices)
    - maps inr w to witnessMap H φ (h(v)) h_sat w (using chosen witnesses)

    Edge preservation follows from:
    - inl-inl: h preserves G-edges
    - inl-inr: rootEdge maps to actual edges via witnessMap_rootEdge
    - inr-inr: internalEdge maps to actual edges via witnessMap_internalEdge
    - inr-inl: impossible (no such edges in ExtensionLTS) -/
noncomputable def mediatingHom {L : Type} [Fintype L] [DecidableEq L]
    {G H : FinLTS L} (h : LTSHom G H) (v : G.Vertex) (phi : HMLPos L)
    (h_sat : phi.satisfies H (h.toFun v)) :
    LTSHom (ExtensionLTS G v phi) H where
  toFun := fun
    | .inl s => h.toFun s
    | .inr w => witnessMap H phi (h.toFun v) h_sat w
  map_edge := fun a s t hedge => by
    match s, t with
    | .inl s', .inl t' =>
      exact h.map_edge a s' t' hedge
    | .inl s', .inr w =>
      obtain ⟨h_eq, h_re⟩ := hedge
      rw [h_eq]
      exact witnessMap_rootEdge H phi (h.toFun v) h_sat a w h_re
    | .inr w, .inr w' =>
      exact witnessMap_internalEdge H phi (h.toFun v) h_sat a w w' hedge
    | .inr _, .inl _ =>
      exact absurd hedge id

/-- The mediating homomorphism agrees with h on original vertices. -/
theorem mediatingHom_on_original {L : Type} [Fintype L] [DecidableEq L]
    {G H : FinLTS L} (h : LTSHom G H) (v : G.Vertex) (phi : HMLPos L)
    (h_sat : phi.satisfies H (h.toFun v)) (s : G.Vertex) :
    (mediatingHom h v phi h_sat).toFun (.inl s) = h.toFun s := rfl

/-!
## Part 7: Backward Direction of Geometric Closure
-/

/-- Backward direction: if ψ is satisfied at inl v in ExtensionLTS G v φ,
    then (S_φ ⟹ S_ψ)(G, v) holds.

    Proof: Given H and h : G → H with φ satisfied at h(v) in H, construct the
    mediating homomorphism m : ExtensionLTS G v φ → H. Since ψ is satisfied
    at inl v in the extension, and m preserves inl v to h(v), forward preservation
    gives ψ satisfied at h(v) in H. -/
theorem geometric_closure_backward {L : Type} [Fintype L] [DecidableEq L]
    (phi psi : HMLPos L) (G : FinLTS L) (v : G.Vertex)
    (h_ext : psi.satisfies (ExtensionLTS G v phi) (.inl v)) :
    (phi.toSubfunctor.himp psi.toSubfunctor).pred G v := by
  intro H h h_phi
  -- h_phi : phi.satisfies H (h.toFun v)
  -- Construct the mediating homomorphism
  let m := mediatingHom h v phi h_phi
  -- m : LTSHom (ExtensionLTS G v phi) H with m(inl s) = h(s)
  -- By forward preservation of ψ along m:
  have h_pres := HMLPos.preserved_by_hom m (.inl v) psi h_ext
  -- h_pres : psi.satisfies H (m.toFun (inl v))
  -- m.toFun (inl v) = h.toFun v
  exact h_pres

/-!
## Part 8: The Geometric Closure Theorem
-/

/-- **The Geometric Closure Theorem**: The presheaf Heyting implication of geometric
    subfunctors S_φ and S_ψ is characterized by satisfaction in the free extension.

    (S_φ ⟹ S_ψ)(G, v) ⟺ ψ.satisfies (ExtensionLTS G v φ) (inl v)

    Forward: instantiate the Heyting implication with the free extension.
    Backward: construct a mediating homomorphism using satisfaction witnesses. -/
theorem geometric_closure_theorem {L : Type} [Fintype L] [DecidableEq L]
    (phi psi : HMLPos L) (G : FinLTS L) (v : G.Vertex) :
    (phi.toSubfunctor.himp psi.toSubfunctor).pred G v ↔
    psi.satisfies (ExtensionLTS G v phi) (.inl v) :=
  ⟨geometric_closure_forward phi psi G v, geometric_closure_backward phi psi G v⟩

/-!
## Part 9: Negation Corollary
-/

/-- **Geometric Closure Negation Corollary**: The Heyting implication S_φ ⟹ ⊥
    is equivalent to the presheaf negation ¬S_φ, and both collapse to ⊥.

    By the geometric closure theorem with ψ = some unsatisfiable formula,
    (S_φ ⟹ ⊥)(G, v) ⟺ ⊥.satisfies (ExtensionLTS G v φ) (inl v).
    But ⊥ has no satisfying models, so this is always False.

    We prove the connection differently: the Heyting implication into ⊥ coincides
    pointwise with the presheaf negation, and both are empty by Phase 185. -/
theorem geometric_closure_negation_corollary {L : Type} [Fintype L] [DecidableEq L]
    (phi : HMLPos L) :
    -- himp(S_φ, ⊥) is pointwise equivalent to negation of S_φ
    (∀ (G : FinLTS L) (v : G.Vertex),
      (phi.toSubfunctor.himp (LTSSubfunctor.bot L)).pred G v ↔
      phi.toSubfunctor.negation.pred G v) ∧
    -- Both collapse to ⊥ (are everywhere false)
    (∀ (G : FinLTS L) (v : G.Vertex),
      ¬ (phi.toSubfunctor.himp (LTSSubfunctor.bot L)).pred G v) := by
  constructor
  · -- himp(S_φ, ⊥) ↔ negation S_φ pointwise
    intro G v
    constructor
    · intro h_himp H h h_phi
      exact h_himp H h h_phi
    · intro h_neg H h h_phi
      exact h_neg H h h_phi
  · -- Both collapse
    intro G v h_himp
    -- h_himp : ∀ H h, phi.satisfies H (h(v)) → False
    -- This is exactly negation, which is false by Phase 185
    exact geometric_negation_collapse phi G v (fun H h => h_himp H h)

/-!
## Part 10: Heyting Adjunction for Geometric Subfunctors
-/

/-- **Heyting Adjunction**: For geometric subfunctors, meet(S₁, T) ≤ S₂ iff T ≤ himp(S₁, S₂).

    This is the defining property of the Heyting implication at the subfunctor level. -/
theorem geometric_himp_adjunction {L : Type} [Fintype L] [DecidableEq L]
    (S₁ S₂ T : LTSSubfunctor L) :
    (S₁.meet T).le S₂ ↔ T.le (S₁.himp S₂) := by
  constructor
  · -- Forward: meet(S₁, T) ≤ S₂ implies T ≤ himp(S₁, S₂)
    intro h_le G v h_T H h h_S1
    -- Need: S₂.pred H (h.toFun v)
    -- h_T : T.pred G v, h_S1 : S₁.pred H (h.toFun v)
    -- By naturality of T: T.pred H (h.toFun v)
    have h_T_H : T.pred H (h.toFun v) := T.natural h v h_T
    -- meet(S₁, T)(H, h(v)) holds
    exact h_le H (h.toFun v) ⟨h_S1, h_T_H⟩
  · -- Backward: T ≤ himp(S₁, S₂) implies meet(S₁, T) ≤ S₂
    intro h_le G v ⟨h_S1, h_T⟩
    -- h_le : ∀ G v, T.pred G v → (himp S₁ S₂).pred G v
    -- h_S1 : S₁.pred G v, h_T : T.pred G v
    -- From h_le: himp(S₁, S₂)(G, v)
    have h_himp := h_le G v h_T
    -- h_himp : ∀ H h, S₁.pred H (h(v)) → S₂.pred H (h(v))
    -- Take H = G, h = id
    exact h_himp G (LTSHom.id G) (by simp [LTSHom.id]; exact h_S1)

/-!
## Part 11: Summary

The Geometric Closure Theorem provides a computational characterization of the
Heyting implication between geometric subfunctors. Together with the Negation
Collapse (Phase 185) and the Free Extension Lemma (Phase 184), it completes the
picture of internal logic in Set[T_LTS]:

1. **Free Extension** (184): Every pointed LTS can be extended to satisfy any HMLPos φ.
2. **Negation Collapse** (185): ¬S_φ = ⊥ for all geometric subfunctors.
3. **Geometric Closure** (186): (S_φ ⟹ S_ψ)(G,v) ⟺ ψ holds in the φ-extension of (G,v).

The Heyting implication remains informative (non-degenerate) even though negation
collapses -- this is the subfunctor-level Heyting gap, analogous to the sieve-level
gap proved in Phase 160 (HeytingImplication.lean).
-/

end RTS.PresheafTopos
