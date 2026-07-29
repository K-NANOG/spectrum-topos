/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Free Extension Lemma: HMLPos and Witness Infrastructure

This file defines positive existential Hennessy-Milner Logic (HMLPos) for labeled
transition systems and the witness vertex infrastructure needed for the Free Extension
Lemma.

HMLPos formulas are the geometric formulas over the theory T_LTS (Phase 162
correspondence). They consist of:
- `top`: the trivially true formula
- `conj`: finite conjunction
- `diamond a phi`: existential modality "there exists an a-successor satisfying phi"

Notably absent are `bot`, `disj`, and `neg`, which are NOT positive-existential/geometric.

The Free Extension Lemma states: for any HMLPos formula phi and any LTS G with vertex v,
if phi is "consistent" with (G,v), then there exists an extension G' of G in which v
satisfies phi. The extension is constructed by gluing a "witness tree" onto G at v.

## Key Definitions

- `HMLPos L`: Positive existential HML formulas over label type L
- `HMLPos.satisfies`: Satisfaction relation on FinLTS
- `HMLPos.preserved_by_hom`: Forward preservation by homomorphisms
- `WitnessVertex`: Fresh vertices demanded by existential quantifiers in a formula
- `rootEdge`: Edge relation from attachment point to witness vertices
- `internalEdge`: Edge relation between witness vertices

## References

- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
- van Glabbeek, "The linear time--branching time spectrum I" (1990)
- Sobocinski, "Relational presheaves, change of base and weak simulation" (2015)
-/

import RuleSys.PresheafTopos.LabeledLTS
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

universe u

namespace RTS.PresheafTopos

/-!
## Part 1: Positive Existential HML (HMLPos)
-/

/-- Positive existential Hennessy-Milner Logic for labeled transition systems.
    These are the geometric formulas over T_LTS: top, conjunction, and diamond modality.
    No negation, disjunction, or bottom -- these would break the positive-existential fragment. -/
inductive HMLPos (L : Type) : Type where
  /-- The trivially true formula -/
  | top : HMLPos L
  /-- Conjunction of two formulas -/
  | conj : HMLPos L -> HMLPos L -> HMLPos L
  /-- Diamond modality: there exists an a-successor satisfying phi -/
  | diamond : L -> HMLPos L -> HMLPos L
  deriving DecidableEq

/-!
## Part 2: Satisfaction Predicate
-/

/-- Satisfaction of an HMLPos formula at a vertex v of a finite LTS G.
    - top: always satisfied
    - conj phi psi: both phi and psi satisfied at v
    - diamond a phi: there exists an a-successor w of v satisfying phi -/
def HMLPos.satisfies {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) : HMLPos L -> Prop
  | .top => True
  | .conj phi psi => satisfies G v phi /\ satisfies G v psi
  | .diamond a phi => exists w : G.Vertex, G.edge a v w /\ satisfies G w phi

/-!
## Part 3: Forward Preservation by Homomorphisms
-/

/-- Positive existential formulas are preserved by LTS homomorphisms (forward direction).
    If phi is satisfied at v in G, and f : G -> H is a homomorphism, then phi is satisfied
    at f(v) in H. This is the Hennessy-Milner analogue of preservation of geometric sequents
    by model homomorphisms. -/
theorem HMLPos.preserved_by_hom {L : Type} [Fintype L] [DecidableEq L]
    {G H : FinLTS L} (f : LTSHom G H) (v : G.Vertex)
    (phi : HMLPos L) (h : phi.satisfies G v) : phi.satisfies H (f.toFun v) := by
  induction phi generalizing v with
  | top => trivial
  | conj phi psi ih_phi ih_psi =>
    obtain ⟨h_left, h_right⟩ := h
    exact ⟨ih_phi v h_left, ih_psi v h_right⟩
  | diamond a phi ih =>
    obtain ⟨w, h_edge, h_sat⟩ := h
    exact ⟨f.toFun w, f.map_edge a v w h_edge, ih w h_sat⟩

/-!
## Part 4: Concrete Formula Abbreviations
-/

/-- The diamond-top formula: "there exists an a-successor" (i.e., vertex has an a-edge). -/
@[reducible] def diamondTop {L : Type} (a : L) : HMLPos L := .diamond a .top

/-- The double-diamond formula: "there exists an a-successor with a b-successor". -/
@[reducible] def doubleDiamond {L : Type} (a b : L) : HMLPos L :=
  .diamond a (.diamond b .top)

/-- diamondTop a is satisfied at v iff v has an a-successor. -/
theorem diamondTop_iff {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (a : L) :
    (diamondTop a).satisfies G v <-> exists w : G.Vertex, G.edge a v w := by
  simp [HMLPos.satisfies]

/-- doubleDiamond a b is satisfied at v iff v has an a-successor with a b-successor. -/
theorem doubleDiamond_iff {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (a b : L) :
    (doubleDiamond a b).satisfies G v <->
    exists w u : G.Vertex, G.edge a v w /\ G.edge b w u := by
  constructor
  · rintro ⟨w, h_aw, _, h_bu, _⟩
    exact ⟨w, _, h_aw, h_bu⟩
  · rintro ⟨w, u, h_aw, h_bu⟩
    exact ⟨w, h_aw, u, h_bu, trivial⟩

/-!
## Part 5: Witness Vertices

The witness vertices are the fresh states demanded by existential quantifiers in an
HMLPos formula. For each diamond modality `diamond a phi`, one fresh a-successor is
created (`freshSucc`), plus all witnesses needed by `phi` are lifted (`succWitness`).
For conjunction `conj phi psi`, witnesses from both conjuncts are combined via
`ofLeft`/`ofRight`.

Key property: `WitnessVertex L .top` is empty (no constructors apply -- top demands
no witnesses).
-/

/-- Fresh vertices demanded by existential quantifiers in an HMLPos formula.
    Indexed by the formula: each diamond adds a fresh successor plus recursive witnesses,
    each conjunction combines witnesses from both sides. Top has no witnesses. -/
inductive WitnessVertex (L : Type) : HMLPos L -> Type where
  /-- The fresh a-successor for a diamond formula -/
  | freshSucc : (a : L) -> (psi : HMLPos L) -> WitnessVertex L (.diamond a psi)
  /-- A deeper witness lifted from the sub-formula of a diamond -/
  | succWitness : (a : L) -> (psi : HMLPos L) -> WitnessVertex L psi ->
      WitnessVertex L (.diamond a psi)
  /-- A witness from the left conjunct -/
  | ofLeft : (phi psi : HMLPos L) -> WitnessVertex L phi ->
      WitnessVertex L (.conj phi psi)
  /-- A witness from the right conjunct -/
  | ofRight : (phi psi : HMLPos L) -> WitnessVertex L psi ->
      WitnessVertex L (.conj phi psi)

/-!
## Part 6: DecidableEq Instance for WitnessVertex
-/

/-- DecidableEq instance for WitnessVertex by structural recursion on the formula.
    Uses match-based structural recursion (not tactic-based induction) to avoid
    code generator rejection. -/
instance witnessVertexDecEq {L : Type} [DecidableEq L] :
    (phi : HMLPos L) -> DecidableEq (WitnessVertex L phi)
  | .top => fun a _ => by cases a
  | .diamond a psi => fun w1 w2 => by
    have : DecidableEq (WitnessVertex L psi) := witnessVertexDecEq psi
    match w1, w2 with
    | .freshSucc _ _, .freshSucc _ _ => exact isTrue rfl
    | .freshSucc _ _, .succWitness _ _ _ => exact isFalse (fun h => by cases h)
    | .succWitness _ _ _, .freshSucc _ _ => exact isFalse (fun h => by cases h)
    | .succWitness _ _ w, .succWitness _ _ w' =>
      match this w w' with
      | isTrue h => exact isTrue (by rw [h])
      | isFalse h => exact isFalse (fun heq => by cases heq; exact h rfl)
  | .conj phi psi => fun w1 w2 => by
    have : DecidableEq (WitnessVertex L phi) := witnessVertexDecEq phi
    have : DecidableEq (WitnessVertex L psi) := witnessVertexDecEq psi
    match w1, w2 with
    | .ofLeft _ _ w, .ofLeft _ _ w' =>
      match ‹DecidableEq (WitnessVertex L phi)› w w' with
      | isTrue h => exact isTrue (by rw [h])
      | isFalse h => exact isFalse (fun heq => by cases heq; exact h rfl)
    | .ofLeft _ _ _, .ofRight _ _ _ => exact isFalse (fun h => by cases h)
    | .ofRight _ _ _, .ofLeft _ _ _ => exact isFalse (fun h => by cases h)
    | .ofRight _ _ w, .ofRight _ _ w' =>
      match ‹DecidableEq (WitnessVertex L psi)› w w' with
      | isTrue h => exact isTrue (by rw [h])
      | isFalse h => exact isFalse (fun heq => by cases heq; exact h rfl)

/-!
## Part 7: Fintype Instance for WitnessVertex
-/

/-- Fintype instance for WitnessVertex by structural recursion on the formula.
    - WitnessVertex L .top is empty (Fintype with empty Finset)
    - WitnessVertex L (.diamond a psi) ~ Unit + WitnessVertex L psi
    - WitnessVertex L (.conj phi psi) ~ WitnessVertex L phi + WitnessVertex L psi -/
private def witnessVertexEquivDiamond {L : Type} (a : L) (psi : HMLPos L) :
    (Unit ⊕ WitnessVertex L psi) ≃ WitnessVertex L (.diamond a psi) where
  toFun := fun
    | .inl () => .freshSucc a psi
    | .inr w => .succWitness a psi w
  invFun := fun
    | .freshSucc _ _ => .inl ()
    | .succWitness _ _ w => .inr w
  left_inv := fun
    | .inl () => rfl
    | .inr _ => rfl
  right_inv := fun
    | .freshSucc _ _ => rfl
    | .succWitness _ _ _ => rfl

private def witnessVertexEquivConj {L : Type} (phi psi : HMLPos L) :
    (WitnessVertex L phi ⊕ WitnessVertex L psi) ≃ WitnessVertex L (.conj phi psi) where
  toFun := fun
    | Sum.inl w => .ofLeft phi psi w
    | Sum.inr w => .ofRight phi psi w
  invFun := fun
    | .ofLeft _ _ w => Sum.inl w
    | .ofRight _ _ w => Sum.inr w
  left_inv := fun
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl
  right_inv := fun
    | .ofLeft _ _ _ => rfl
    | .ofRight _ _ _ => rfl

instance witnessVertexFintype {L : Type} [DecidableEq L] [Fintype L] :
    (phi : HMLPos L) -> Fintype (WitnessVertex L phi)
  | .top => {
      elems := Finset.empty
      complete := fun w => by cases w
    }
  | .diamond a psi => by
    haveI := witnessVertexDecEq (L := L) psi
    haveI := witnessVertexFintype psi
    exact Fintype.ofEquiv _ (witnessVertexEquivDiamond a psi)
  | .conj phi psi => by
    haveI := witnessVertexDecEq (L := L) phi
    haveI := witnessVertexDecEq (L := L) psi
    haveI := witnessVertexFintype phi
    haveI := witnessVertexFintype psi
    exact Fintype.ofEquiv _ (witnessVertexEquivConj phi psi)

/-!
## Part 8: Edge Predicates for Witness Tree
-/

/-- Edge relation from the attachment point (root) to witness vertices.
    For diamond a psi: the freshSucc is an a-successor of the root.
    For conj phi psi: recurse into the appropriate conjunct.
    Deeper witnesses (succWitness) are NOT directly connected to the root. -/
def rootEdge {L : Type} [DecidableEq L] :
    (phi : HMLPos L) -> L -> WitnessVertex L phi -> Prop
  | .diamond a _, b, .freshSucc _ _ => a = b
  | .diamond _ _, _, .succWitness _ _ _ => False
  | .conj phi _, a, .ofLeft _ _ w => rootEdge phi a w
  | .conj _ psi, a, .ofRight _ _ w => rootEdge psi a w

/-- Decidable instance for rootEdge by structural recursion. -/
instance rootEdgeDecidable {L : Type} [DecidableEq L] :
    (phi : HMLPos L) -> (a : L) -> (w : WitnessVertex L phi) ->
    Decidable (rootEdge phi a w)
  | .diamond _ _, b, .freshSucc a _ => inferInstanceAs (Decidable (a = b))
  | .diamond _ _, _, .succWitness _ _ _ => isFalse id
  | .conj phi _, a, .ofLeft _ _ w => rootEdgeDecidable phi a w
  | .conj _ psi, a, .ofRight _ _ w => rootEdgeDecidable psi a w

/-- Edge relation between witness vertices (internal edges of the witness tree).
    For diamond a psi: freshSucc acts as the root of the sub-tree for psi, so
    freshSucc connects to succWitness vertices via rootEdge of psi. Edges between
    succWitness vertices delegate to internalEdge of psi.
    For conj: edges within each conjunct are preserved, cross-conjunct edges are False. -/
def internalEdge {L : Type} [DecidableEq L] :
    (phi : HMLPos L) -> L -> WitnessVertex L phi -> WitnessVertex L phi -> Prop
  | .diamond _ psi, b, .freshSucc _ _, .succWitness _ _ w => rootEdge psi b w
  | .diamond _ psi, b, .succWitness _ _ w, .succWitness _ _ w' => internalEdge psi b w w'
  | .diamond _ _, _, .freshSucc _ _, .freshSucc _ _ => False
  | .diamond _ _, _, .succWitness _ _ _, .freshSucc _ _ => False
  | .conj phi _, b, .ofLeft _ _ w, .ofLeft _ _ w' => internalEdge phi b w w'
  | .conj _ psi, b, .ofRight _ _ w, .ofRight _ _ w' => internalEdge psi b w w'
  | .conj _ _, _, .ofLeft _ _ _, .ofRight _ _ _ => False
  | .conj _ _, _, .ofRight _ _ _, .ofLeft _ _ _ => False

/-- Decidable instance for internalEdge by structural recursion. -/
instance internalEdgeDecidable {L : Type} [DecidableEq L] :
    (phi : HMLPos L) -> (a : L) -> (w w' : WitnessVertex L phi) ->
    Decidable (internalEdge phi a w w')
  | .diamond _ psi, b, .freshSucc _ _, .succWitness _ _ w =>
    rootEdgeDecidable psi b w
  | .diamond _ psi, b, .succWitness _ _ w, .succWitness _ _ w' =>
    internalEdgeDecidable psi b w w'
  | .diamond _ _, _, .freshSucc _ _, .freshSucc _ _ => isFalse id
  | .diamond _ _, _, .succWitness _ _ _, .freshSucc _ _ => isFalse id
  | .conj phi _, b, .ofLeft _ _ w, .ofLeft _ _ w' =>
    internalEdgeDecidable phi b w w'
  | .conj _ psi, b, .ofRight _ _ w, .ofRight _ _ w' =>
    internalEdgeDecidable psi b w w'
  | .conj _ _, _, .ofLeft _ _ _, .ofRight _ _ _ => isFalse id
  | .conj _ _, _, .ofRight _ _ _, .ofLeft _ _ _ => isFalse id

/-!
## Part 9: Emptiness and Element Lemmas
-/

/-- WitnessVertex L .top is empty: top demands no witnesses. -/
theorem witnessVertex_top_empty {L : Type} [DecidableEq L] [Fintype L]
    (w : WitnessVertex L (.top : HMLPos L)) : False := by
  cases w

/-- The unique witness vertex of diamond a .top is freshSucc a .top. -/
theorem witnessVertex_diamondTop_unique {L : Type} [DecidableEq L] [Fintype L]
    (a : L) (w : WitnessVertex L (.diamond a .top)) :
    w = .freshSucc a .top := by
  match w with
  | .freshSucc _ _ => rfl
  | .succWitness _ _ w' => exact (witnessVertex_top_empty w').elim

/-- The two witness vertices of diamond a (diamond b .top). -/
theorem witnessVertex_doubleDiamond_cases {L : Type} [DecidableEq L] [Fintype L]
    (a b : L) (w : WitnessVertex L (.diamond a (.diamond b .top))) :
    w = .freshSucc a (.diamond b .top) \/
    w = .succWitness a (.diamond b .top) (.freshSucc b .top) := by
  match w with
  | .freshSucc _ _ => left; rfl
  | .succWitness _ _ w' =>
    right
    have := witnessVertex_diamondTop_unique b w'
    rw [this]

/-!
## Part 10: Extension Edge Relation
-/

/-- Edge relation on the extended vertex set G.Vertex + WitnessVertex.
    - inl-inl: edges from G are preserved
    - inl-inr: edges from the attachment point v to witness vertices via rootEdge
    - inr-inr: internal edges between witness vertices via internalEdge
    - inr-inl: no backward edges from witnesses to G -/
def extensionEdge {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) :
    L -> (G.Vertex ⊕ WitnessVertex L phi) -> (G.Vertex ⊕ WitnessVertex L phi) -> Prop
  | a, .inl s, .inl t => G.edge a s t
  | a, .inl s, .inr w => s = v /\ rootEdge phi a w
  | a, .inr w, .inr w' => internalEdge phi a w w'
  | _, .inr _, .inl _ => False

/-- Decidability of extensionEdge by case analysis on Sum constructors. -/
instance extensionEdgeDecidable {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) (a : L) :
    DecidableRel (extensionEdge G v phi a) := by
  intro x y
  match x, y with
  | .inl s, .inl t => exact inferInstanceAs (Decidable (G.edge a s t))
  | .inl s, .inr w =>
    exact inferInstanceAs (Decidable (s = v /\ rootEdge phi a w))
  | .inr w, .inr w' =>
    exact inferInstanceAs (Decidable (internalEdge phi a w w'))
  | .inr _, .inl _ => exact isFalse id

/-!
## Part 11: Extension LTS
-/

/-- The extension of G at vertex v by formula phi: the LTS on G.Vertex + WitnessVertex
    with edges from G preserved, plus witness tree edges attached at v. -/
def ExtensionLTS {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) : FinLTS L where
  Vertex := G.Vertex ⊕ WitnessVertex L phi
  vertexFintype := inferInstance
  vertexDecEq := inferInstance
  edge := extensionEdge G v phi
  edgeDecidable := extensionEdgeDecidable G v phi

/-!
## Part 12: Injection Homomorphism
-/

/-- The injection homomorphism from G into ExtensionLTS G v phi.
    Maps each vertex to its inl image. Edge preservation follows because
    extensionEdge on inl-inl reduces to G.edge. -/
def extensionInj {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) :
    LTSHom G (ExtensionLTS G v phi) where
  toFun := Sum.inl
  map_edge := fun _ _ _ hedge => hedge

/-- The injection homomorphism is injective. -/
theorem extensionInj_injective {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) :
    Function.Injective (extensionInj G v phi).toFun :=
  Sum.inl_injective

/-!
## Part 13: Witness Tree Satisfaction

The key technical result: the witness tree for a formula phi, when attached at
vertex v of G, makes v satisfy phi in the extension. This requires showing that
each witness vertex satisfies its corresponding subformula.

We factor the proof into:
1. `rootEdge_gives_extension_edge`: rootEdge produces edges in the extension
2. `internalEdge_gives_extension_edge`: internalEdge produces edges in the extension
3. `witness_satisfies_internal`: each witness vertex satisfies its local subformula
4. `witness_satisfies_at_root`: the root v satisfies phi in the extension
-/

/-- rootEdge lifts to extensionEdge: if rootEdge phi a w, then there is an a-edge
    from inl v to inr w in the extension. -/
theorem rootEdge_gives_extension_edge {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) (a : L)
    (w : WitnessVertex L phi) (h : rootEdge phi a w) :
    extensionEdge G v phi a (.inl v) (.inr w) :=
  ⟨rfl, h⟩

/-- internalEdge lifts to extensionEdge: if internalEdge phi a w w', then there is
    an a-edge from inr w to inr w' in the extension. -/
theorem internalEdge_gives_extension_edge {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) (a : L)
    (w w' : WitnessVertex L phi) (h : internalEdge phi a w w') :
    extensionEdge G v phi a (.inr w) (.inr w') :=
  h

/-- Helper: for a formula psi and an embedding of WitnessVertex L psi into some
    vertex type V, if the embedding preserves the edge structure (rootEdge maps to
    edges from root, internalEdge maps to edges between witnesses), then the root
    satisfies psi.

    This abstracts the common pattern used for both the outer root (inl v) and
    inner fresh successors (inr (freshSucc a psi)). -/
private theorem satisfies_from_witness_structure
    {L : Type} [Fintype L] [DecidableEq L]
    (H : FinLTS L)
    (psi : HMLPos L)
    (root : H.Vertex)
    (embed : WitnessVertex L psi -> H.Vertex)
    (h_rootEdge : forall (a : L) (w : WitnessVertex L psi),
      rootEdge psi a w -> H.edge a root (embed w))
    (h_internalEdge : forall (a : L) (w w' : WitnessVertex L psi),
      internalEdge psi a w w' -> H.edge a (embed w) (embed w')) :
    psi.satisfies H root := by
  induction psi generalizing root with
  | top => trivial
  | conj phi' psi' ih_phi ih_psi =>
    constructor
    · exact ih_phi root (fun w => embed (.ofLeft phi' psi' w))
        (fun a w h => h_rootEdge a (.ofLeft phi' psi' w) h)
        (fun a w w' h => h_internalEdge a (.ofLeft phi' psi' w) (.ofLeft phi' psi' w') h)
    · exact ih_psi root (fun w => embed (.ofRight phi' psi' w))
        (fun a w h => h_rootEdge a (.ofRight phi' psi' w) h)
        (fun a w w' h => h_internalEdge a (.ofRight phi' psi' w) (.ofRight phi' psi' w') h)
  | diamond b chi ih_chi =>
    refine ⟨embed (.freshSucc b chi), h_rootEdge b (.freshSucc b chi) rfl, ?_⟩
    exact ih_chi (embed (.freshSucc b chi)) (fun w => embed (.succWitness b chi w))
      (fun a w h => h_internalEdge a (.freshSucc b chi) (.succWitness b chi w) h)
      (fun a w w' h => h_internalEdge a (.succWitness b chi w) (.succWitness b chi w') h)

/-- The root vertex v satisfies phi in the extension ExtensionLTS G v phi.
    This is the key technical result: the witness tree attached at v provides
    all the fresh successors demanded by phi. -/
theorem witness_satisfies_at_root {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) :
    phi.satisfies (ExtensionLTS G v phi) (.inl v) :=
  satisfies_from_witness_structure (ExtensionLTS G v phi) phi (.inl v)
    (fun w => .inr w)
    (fun _a _w h => ⟨rfl, h⟩)
    (fun _a _w _w' h => h)

/-!
## Part 14: The Free Extension Lemma
-/

/-- **The Free Extension Lemma**: For any finite labeled transition system G,
    vertex v, and positive existential HML formula phi, there exists an extension
    H of G (with an injection homomorphism G -> H) such that v satisfies phi in H.

    This is the computational counterpart of the geometric model extension property:
    every geometric formula can be made true by extending the model. It underlies
    the negation collapse (Phase 185) and the geometric closure theorem (Phase 186). -/
theorem freeExtensionLemma {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (phi : HMLPos L) :
    exists (H : FinLTS L) (h : LTSHom G H), phi.satisfies H (h.toFun v) :=
  ⟨ExtensionLTS G v phi, extensionInj G v phi, witness_satisfies_at_root G v phi⟩

end RTS.PresheafTopos
