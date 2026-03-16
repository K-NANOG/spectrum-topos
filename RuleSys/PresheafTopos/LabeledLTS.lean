/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Labeled Transition Systems: The Category f.p.LTS_L

This file defines the category of finite labeled transition systems with
label-preserving homomorphisms, generalizing the |L|=1 FinDigraph infrastructure
to support multiple labels.

For a label type L, an L-labeled transition system (L-LTS) is a finite set of
states with decidable L-indexed binary relations. The morphisms are functions
that preserve all labeled transitions in the forward direction.

## Key Definitions

- `TwoLabel`: Label alphabet {a, b} with Fintype and DecidableEq
- `FinLTS L`: Finite L-labeled transition system
- `LTSHom G H`: Label-preserving homomorphism between L-LTS
- `CategoryTheory.Category (FinLTS L)`: Category instance
- `emptyLTS`, `singleLTS`, `selfLoopLTS`: Small objects at |L|=2

## References

- Sobocinski, "Relational presheaves, change of base and weak simulation" (JCSS 2015)
- van Glabbeek, "The linear time--branching time spectrum I" (1990)
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992) -- presheaf toposes
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

universe u

namespace RTS.PresheafTopos

/-!
## Part 1: Label Types
-/

/-- Two-label alphabet: actions a and b.
    The minimal non-trivial label set for distinguishing labeled from unlabeled. -/
inductive TwoLabel where
  | a | b
  deriving DecidableEq, Repr

instance : Fintype TwoLabel where
  elems := {.a, .b}
  complete := fun x => by cases x <;> simp

/-!
## Part 2: Finite Labeled Transition Systems
-/

/-- A finite L-labeled transition system: a finite set of vertices with a decidable
    L-indexed family of binary edge relations. For each label a : L, edge a s t means
    there is an a-labeled transition from state s to state t.

    This generalizes FinDigraph (which is FinLTS for |L|=1) to arbitrary finite
    label alphabets. -/
structure FinLTS (L : Type) [Fintype L] [DecidableEq L] where
  /-- The vertex (state) type -/
  Vertex : Type
  /-- Finiteness of vertices -/
  [vertexFintype : Fintype Vertex]
  /-- Decidable equality on vertices -/
  [vertexDecEq : DecidableEq Vertex]
  /-- The L-indexed edge relation: edge a s t means s -a-> t -/
  edge : L → Vertex → Vertex → Prop
  /-- Decidability of edges for each label -/
  [edgeDecidable : ∀ a, DecidableRel (edge a)]

attribute [instance] FinLTS.vertexFintype FinLTS.vertexDecEq FinLTS.edgeDecidable

/-!
## Part 3: Label-Preserving Homomorphisms
-/

/-- A label-preserving homomorphism between L-labeled transition systems: a function
    on vertices that preserves all labeled transitions in the forward direction.
    If s -a-> t in G, then f(s) -a-> f(t) in H, for every label a. -/
structure LTSHom {L : Type} [Fintype L] [DecidableEq L] (G H : FinLTS L) where
  /-- The underlying function on vertices -/
  toFun : G.Vertex → H.Vertex
  /-- Forward edge preservation for all labels -/
  map_edge : ∀ (a : L) (s t : G.Vertex), G.edge a s t → H.edge a (toFun s) (toFun t)

namespace LTSHom

variable {L : Type} [Fintype L] [DecidableEq L]

/-- Extensionality for LTS homomorphisms -/
@[ext]
theorem ext {G H : FinLTS L} {f g : LTSHom G H}
    (h : ∀ v, f.toFun v = g.toFun v) : f = g := by
  cases f; cases g
  simp only [mk.injEq]
  funext v
  exact h v

/-- Identity homomorphism -/
def id (G : FinLTS L) : LTSHom G G where
  toFun := _root_.id
  map_edge := fun _ _ _ h => h

/-- Composition of homomorphisms -/
def comp {G H K : FinLTS L} (f : LTSHom G H) (g : LTSHom H K) :
    LTSHom G K where
  toFun := g.toFun ∘ f.toFun
  map_edge := fun a s t h => g.map_edge a _ _ (f.map_edge a s t h)

theorem comp_assoc {G H K M : FinLTS L}
    (f : LTSHom G H) (g : LTSHom H K) (h : LTSHom K M) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext; intro v; rfl

theorem id_comp {G H : FinLTS L} (f : LTSHom G H) :
    comp (id G) f = f := by
  apply ext; intro v; rfl

theorem comp_id {G H : FinLTS L} (f : LTSHom G H) :
    comp f (id H) = f := by
  apply ext; intro v; rfl

end LTSHom

/-!
## Part 4: Category Instance
-/

instance {L : Type} [Fintype L] [DecidableEq L] :
    CategoryTheory.CategoryStruct (FinLTS L) where
  Hom := LTSHom
  id := LTSHom.id
  comp := fun f g => LTSHom.comp f g

instance {L : Type} [Fintype L] [DecidableEq L] :
    CategoryTheory.Category (FinLTS L) where
  id_comp := fun f => LTSHom.id_comp f
  comp_id := fun f => LTSHom.comp_id f
  assoc := fun f g h => LTSHom.comp_assoc f g h

/-!
## Part 5: Small Objects (|L| = 2)
-/

/-- The empty LTS (0 vertices). Initial object in f.p.LTS_L. -/
@[reducible] def emptyLTS : FinLTS TwoLabel where
  Vertex := Empty
  edge := fun _ v _ => isEmptyElim v
  edgeDecidable := fun _ _ v => isEmptyElim v

/-- A single vertex with no edges (deadlock state). -/
@[reducible] def singleLTS : FinLTS TwoLabel where
  Vertex := Unit
  edge := fun _ _ _ => False

/-- A single vertex with both a and b self-loops. -/
@[reducible] def selfLoopLTS : FinLTS TwoLabel where
  Vertex := Unit
  edge := fun _ _ _ => True

/-!
## Part 6: Initial Object
-/

/-- The empty LTS is initial: there exists a unique homomorphism emptyLTS -> G for any G. -/
def fromEmpty (G : FinLTS TwoLabel) : LTSHom emptyLTS G where
  toFun v := isEmptyElim v
  map_edge _ s _ _ := isEmptyElim s

/-- The homomorphism from emptyLTS is unique (by extensionality on the empty type). -/
theorem emptyLTS_hom_unique (G : FinLTS TwoLabel)
    (f g : LTSHom emptyLTS G) : f = g := by
  apply LTSHom.ext
  intro v
  exact isEmptyElim v

/-!
## Part 7: Labeled Sieves
-/

/-- A sieve on an L-labeled LTS G: a collection of morphisms into G
    from arbitrary L-LTS, closed under precomposition.
    This is the labeled generalization of DigraphSieve. -/
structure LTSSieve {L : Type} [Fintype L] [DecidableEq L] (G : FinLTS L) where
  /-- The membership predicate: for each H, which homomorphisms H -> G are in the sieve -/
  mem : (H : FinLTS L) → LTSHom H G → Prop
  /-- Closure under precomposition: if f in S and h : K -> H, then f . h in S -/
  precomp_closed : ∀ {H K : FinLTS L} (f : LTSHom H G) (h : LTSHom K H),
    mem H f → mem K (LTSHom.comp h f)

namespace LTSSieve

variable {L : Type} [Fintype L] [DecidableEq L]

/-- The maximal sieve: contains all morphisms into G. -/
def maximal (G : FinLTS L) : LTSSieve G where
  mem := fun _ _ => True
  precomp_closed := fun _ _ _ => trivial

/-- The empty sieve: contains no morphisms into G. -/
def empty (G : FinLTS L) : LTSSieve G where
  mem := fun _ _ => False
  precomp_closed := fun _ _ h => h

/-- Pullback (restriction) of a sieve along a morphism. Given S on G and f : H -> G,
    the pullback f*S on H contains g : K -> H iff f . g in S. -/
def pullback {G H : FinLTS L} (S : LTSSieve G) (f : LTSHom H G) : LTSSieve H where
  mem := fun K g => S.mem K (LTSHom.comp g f)
  precomp_closed := fun {_K M} g h hmem => by
    show S.mem M (LTSHom.comp (LTSHom.comp h g) f)
    rw [LTSHom.comp_assoc]
    exact S.precomp_closed _ h hmem

end LTSSieve

/-!
## Part 8: Labeled Path LTS (Trace LTS)
-/

/-- The labeled path LTS for a word w : List L. Vertices are Fin (w.length + 1),
    and there is an a-labeled edge from i to i+1 iff w[i] = a.

    traceLTS [] is a single vertex with no edges (isomorphic to singleLTS).
    traceLTS [a, b] has vertices {0, 1, 2} with edges 0 -a-> 1 -b-> 2. -/
@[reducible] def traceLTS {L : Type} [Fintype L] [DecidableEq L]
    (w : List L) : FinLTS L where
  Vertex := Fin (w.length + 1)
  edge := fun l i j => ∃ (h : i.val < w.length),
    w.get ⟨i.val, h⟩ = l ∧ j.val = i.val + 1

/-!
## Part 9: Labeled Traces
-/

/-- A labeled trace (path with labels) of length |t| starting from vertex v in G.
    - nil: the empty trace at v
    - cons: an a-labeled step from v to w, followed by trace t from w -/
inductive hasTrace {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) : G.Vertex → List L → Prop where
  | nil (v : G.Vertex) : hasTrace G v []
  | cons {v w : G.Vertex} (l : L) (t : List L) :
    G.edge l v w → hasTrace G w t → hasTrace G v (l :: t)

/-- The labeled trace set of G from vertex v: the set of all achievable labeled traces. -/
def labeledTraceSet {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) : Set (List L) :=
  {w | hasTrace G v w}

/-- Labeled trace equivalence: two rooted L-LTS have the same labeled trace set. -/
def labeledTraceEquiv {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (H : FinLTS L) (w : H.Vertex) : Prop :=
  labeledTraceSet G v = labeledTraceSet H w

/-!
## Part 10: Labeled Reachability
-/

/-- Reachability in a labeled LTS: v can reach u via a sequence of edges with
    arbitrary labels. This is the reflexive-transitive closure of the union of
    all labeled edge relations. -/
inductive LabeledReachable {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) : G.Vertex → G.Vertex → Prop where
  | refl (v : G.Vertex) : LabeledReachable G v v
  | step {v w u : G.Vertex} (l : L) : G.edge l v w → LabeledReachable G w u →
    LabeledReachable G v u

/-- Labeled reachability is transitive. -/
theorem LabeledReachable.trans {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {v w u : G.Vertex}
    (h1 : LabeledReachable G v w) (h2 : LabeledReachable G w u) :
    LabeledReachable G v u := by
  induction h1 with
  | refl _ => exact h2
  | step l he _ ih => exact LabeledReachable.step l he (ih h2)

/-!
## Part 11: Path-Homomorphism Correspondence (Labeled)
-/

/-- Forward: a labeled trace w from v in G implies the existence of a root-preserving
    homomorphism traceLTS w -> G. Since hasTrace is in Prop, we prove existence (also Prop)
    rather than constructing the homomorphism directly.

    Note: For the forward direction we use a weaker existential statement to stay within
    Prop, matching the pattern from PathDigraph.lean. -/
theorem trace_implies_hom {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {v : G.Vertex} {w : List L}
    (p : hasTrace G v w) :
    ∃ f : LTSHom (traceLTS w) G, f.toFun ⟨0, Nat.zero_lt_succ w.length⟩ = v := by
  induction w generalizing v with
  | nil =>
    cases p
    exact ⟨{
      toFun := fun _ => v
      map_edge := fun _ s _ ⟨hs, _, _⟩ => absurd hs (by exact Nat.not_lt_zero s.val)
    }, rfl⟩
  | cons l t ih_w =>
    -- p : hasTrace G v (l :: t)
    -- Must be hasTrace.cons: v -l-> w', hasTrace G w' t
    have hlen : (l :: t).length = t.length + 1 := rfl
    match p with
    | .cons _ _ edge_vw ht =>
      obtain ⟨f, hroot⟩ := ih_w ht
      refine ⟨{
        toFun := fun i => if h : i.val = 0 then v
          else f.toFun ⟨i.val - 1, by have := i.isLt; omega⟩
        map_edge := ?_
      }, by simp⟩
      intro a s j ⟨hs_lt, hlabel, hj⟩
      by_cases hs : s.val = 0
      · -- s = 0 maps to v, j = 1 maps to f(0) = w'
        have hj_ne : j.val ≠ 0 := by omega
        simp only [dif_pos hs, dif_neg hj_ne]
        have hj_bound : j.val - 1 < t.length + 1 := by
          have := j.isLt; omega
        have hjz : (⟨j.val - 1, hj_bound⟩ : Fin (t.length + 1)) =
              ⟨0, Nat.zero_lt_succ t.length⟩ := by
          apply Fin.ext; simp; omega
        rw [hjz, hroot]
        -- a = l: from hlabel with s.val = 0
        have ha : a = l := by
          have : (l :: t).get ⟨s.val, hs_lt⟩ = (l :: t).get ⟨0, by omega⟩ := by
            congr 1; exact Fin.ext hs
          rw [this] at hlabel; exact hlabel.symm
        rw [ha]; exact edge_vw
      · -- s > 0, j > 0: delegate to f
        have hj_ne : j.val ≠ 0 := by omega
        simp only [dif_neg hs, dif_neg hj_ne]
        have hs_bound : s.val - 1 < t.length + 1 := by omega
        have hj_bound : j.val - 1 < t.length + 1 := by
          have := j.isLt; omega
        have edge_in_tail : (traceLTS t).edge a ⟨s.val - 1, hs_bound⟩
            ⟨j.val - 1, hj_bound⟩ := by
          refine ⟨by simp; omega, ?_, by simp; omega⟩
          -- t[s.val-1] = a from (l::t)[s.val] = a
          have : (l :: t).get ⟨s.val, hs_lt⟩ =
              t.get ⟨s.val - 1, by omega⟩ := by
            have hs_pos : 0 < s.val := by omega
            match s, hs_pos with
            | ⟨_ + 1, _⟩, _ => rfl
          rw [← this]; exact hlabel
        exact f.map_edge a _ _ edge_in_tail

/-- Reverse: a homomorphism traceLTS w -> G gives a labeled trace w from f(0). -/
theorem homToTrace {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {w : List L} (f : LTSHom (traceLTS w) G) :
    hasTrace G (f.toFun ⟨0, Nat.zero_lt_succ w.length⟩) w := by
  induction w with
  | nil => exact hasTrace.nil _
  | cons l t ih =>
    have hlen : (l :: t).length = t.length + 1 := rfl
    -- traceLTS (l :: t) has edge l from 0 to 1
    have h0_bound : 0 < (l :: t).length + 1 := by omega
    have h1_bound : 1 < (l :: t).length + 1 := by omega
    have hedge : (traceLTS (l :: t)).edge l ⟨0, h0_bound⟩ ⟨1, h1_bound⟩ :=
      ⟨by show 0 < (l :: t).length; omega,
       by show (l :: t).get ⟨0, _⟩ = l; rfl,
       by show (1 : Fin ((l :: t).length + 1)).val = 0 + 1; rfl⟩
    have edge_in_G := f.map_edge l _ _ hedge
    -- The tail of f restricted to {1, ..., |t|+1} gives a hom traceLTS t -> G
    let tail : LTSHom (traceLTS t) G := {
      toFun := fun i => f.toFun ⟨i.val + 1, by have := i.isLt; omega⟩
      map_edge := by
        intro a s j ⟨hs_lt, hlabel, hj_eq⟩
        have hs1_bound : s.val + 1 < (l :: t).length + 1 := by omega
        have hj1_bound : j.val + 1 < (l :: t).length + 1 := by
          have := j.isLt; omega
        have hedge' : (traceLTS (l :: t)).edge a
            ⟨s.val + 1, hs1_bound⟩ ⟨j.val + 1, hj1_bound⟩ :=
          ⟨by show (⟨s.val + 1, hs1_bound⟩ : Fin _).val < (l :: t).length; simp; omega,
           by show (l :: t).get ⟨s.val + 1, _⟩ = a
              change t.get ⟨s.val, _⟩ = a; exact hlabel,
           by show (⟨j.val + 1, hj1_bound⟩ : Fin _).val =
                   (⟨s.val + 1, hs1_bound⟩ : Fin _).val + 1; simp; omega⟩
        exact f.map_edge a _ _ hedge'
    }
    have tail_trace := ih tail
    have htail : tail.toFun ⟨0, Nat.zero_lt_succ t.length⟩ =
                 f.toFun ⟨1, by omega⟩ := by
      simp [tail]
    rw [htail] at tail_trace
    exact hasTrace.cons l t edge_in_G tail_trace

/-!
## Part 12: Labeled Rooted Trees
-/

/-- A labeled LTS is a rooted tree if there exists a root vertex such that:
    1. No labeled edges point to the root (for any label)
    2. Every non-root vertex has exactly one parent (unique across all labels)
    3. Every vertex is reachable from the root -/
def LabeledIsRootedTree {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) : Prop :=
  ∃ (root : G.Vertex),
    (∀ (a : L) (v : G.Vertex), ¬G.edge a v root) ∧
    (∀ v, v ≠ root → ∃! p, ∃ a, G.edge a p v) ∧
    (∀ v, LabeledReachable G root v)

/-!
## Part 13: Fan LTS
-/

/-- The labeled fan LTS: root vertex 0 with k children, where the edge to child i
    is labeled by labels[i]. Total vertices: labels.length + 1.

    fanLTS [] is a single isolated vertex.
    fanLTS [a, b] has root 0 with edges 0 -a-> 1, 0 -b-> 2. -/
@[reducible] def fanLTS {L : Type} [Fintype L] [DecidableEq L]
    (labels : List L) : FinLTS L where
  Vertex := Fin (labels.length + 1)
  edge := fun a s t => s.val = 0 ∧ ∃ (i : Fin labels.length),
    t.val = i.val + 1 ∧ a = labels.get i

/-!
## Part 14: Three-Label Alphabet and Van Glabbeek Examples
-/

/-- Three-label alphabet: actions a, b, c.
    Used for van Glabbeek separating counterexamples where three distinct continuation
    actions are needed (e.g., `a.b + a.c` vs `a.(b+c)`).

    Note: A `ThreeLabelAlphabet` also exists in SubtoposLattice.LabeledExamples.
    We define a local version to avoid importing heavyweight dependencies. -/
inductive ThreeLabel where
  | a | b | c
  deriving DecidableEq, Repr

instance : Fintype ThreeLabel where
  elems := {.a, .b, .c}
  complete := fun x => by cases x <;> simp

/-- Edge predicate for vgPairA: decidable. -/
private def vgPairA_edge : ThreeLabel → Fin 5 → Fin 5 → Prop
  | ThreeLabel.a, s, t => (s.val = 0 ∧ t.val = 1) ∨ (s.val = 0 ∧ t.val = 2)
  | ThreeLabel.b, s, t => s.val = 1 ∧ t.val = 3
  | ThreeLabel.c, s, t => s.val = 2 ∧ t.val = 4

private instance (lbl : ThreeLabel) : DecidableRel (vgPairA_edge lbl) := by
  intro s t; cases lbl <;> simp [vgPairA_edge] <;> exact inferInstance

/-- Van Glabbeek example A: CCS process `a.b + a.c`
    Vertices: Fin 5 = {s0, s1, s2, s3, s4}
    Edges: s0 -a-> s1, s0 -a-> s2, s1 -b-> s3, s2 -c-> s4
    Two a-branches from root, left continues with b, right continues with c. -/
def vgPairA : FinLTS ThreeLabel where
  Vertex := Fin 5
  edge := vgPairA_edge

/-- Edge predicate for vgPairB: decidable. -/
private def vgPairB_edge : ThreeLabel → Fin 3 → Fin 3 → Prop
  | ThreeLabel.a, s, t => s.val = 0 ∧ t.val = 1
  | ThreeLabel.b, s, t => s.val = 1 ∧ t.val = 2
  | ThreeLabel.c, s, t => s.val = 1 ∧ t.val = 2

private instance (lbl : ThreeLabel) : DecidableRel (vgPairB_edge lbl) := by
  intro s t; cases lbl <;> simp [vgPairB_edge] <;> exact inferInstance

/-- Van Glabbeek example B: CCS process `a.(b + c)`
    Vertices: Fin 3 = {s0, s1, s2}
    Edges: s0 -a-> s1, s1 -b-> s2, s1 -c-> s2
    Single a-branch from root, then nondeterministic b or c. -/
def vgPairB : FinLTS ThreeLabel where
  Vertex := Fin 3
  edge := vgPairB_edge

/-- Edge predicate for vgPairC: decidable. -/
private def vgPairC_edge : ThreeLabel → Fin 7 → Fin 7 → Prop
  | ThreeLabel.a, s, t =>
    (s.val = 0 ∧ t.val = 1) ∨ (s.val = 0 ∧ t.val = 2) ∨ (s.val = 0 ∧ t.val = 3)
  | ThreeLabel.b, s, t => (s.val = 1 ∧ t.val = 4) ∨ (s.val = 3 ∧ t.val = 6)
  | ThreeLabel.c, s, t => (s.val = 2 ∧ t.val = 5) ∨ (s.val = 3 ∧ t.val = 6)

private instance (lbl : ThreeLabel) : DecidableRel (vgPairC_edge lbl) := by
  intro s t; cases lbl <;> simp [vgPairC_edge] <;> exact inferInstance

/-- Van Glabbeek example C: CCS process `a.b + a.c + a.(b+c)`
    Vertices: Fin 7 = {s0, s1, s2, s3, s4, s5, s6}
    Edges: s0 -a-> s1, s0 -a-> s2, s0 -a-> s3,
           s1 -b-> s4, s2 -c-> s5, s3 -b-> s6, s3 -c-> s6
    Three a-branches: left b-only, middle c-only, right b+c. -/
def vgPairC : FinLTS ThreeLabel where
  Vertex := Fin 7
  edge := vgPairC_edge

/-!
## Part 15: Trace Equivalence Witness

Both vgPairA and vgPairB have the same labeled trace set from their roots:
{[], [a], [a, b], [a, c]}

This is the canonical van Glabbeek separation: trace-equivalent but not bisimilar.
-/

/-- vgPairA has trace [] from root. -/
theorem vgPairA_trace_nil :
    hasTrace vgPairA (show vgPairA.Vertex from ⟨0, by omega⟩) [] :=
  hasTrace.nil _

/-- vgPairA has trace [a] from root: s0 -a-> s1. -/
theorem vgPairA_trace_a :
    hasTrace vgPairA (show vgPairA.Vertex from ⟨0, by omega⟩) [ThreeLabel.a] := by
  exact @hasTrace.cons _ _ _ vgPairA ⟨0, by omega⟩ ⟨1, by omega⟩ ThreeLabel.a []
    (Or.inl ⟨rfl, rfl⟩) (hasTrace.nil _)

/-- vgPairA has trace [a, b] from root: s0 -a-> s1 -b-> s3. -/
theorem vgPairA_trace_ab :
    hasTrace vgPairA (show vgPairA.Vertex from ⟨0, by omega⟩) [ThreeLabel.a, ThreeLabel.b] := by
  exact @hasTrace.cons _ _ _ vgPairA ⟨0, by omega⟩ ⟨1, by omega⟩ ThreeLabel.a [ThreeLabel.b]
    (Or.inl ⟨rfl, rfl⟩)
    (@hasTrace.cons _ _ _ vgPairA ⟨1, by omega⟩ ⟨3, by omega⟩ ThreeLabel.b []
      ⟨rfl, rfl⟩ (hasTrace.nil _))

/-- vgPairA has trace [a, c] from root: s0 -a-> s2 -c-> s4. -/
theorem vgPairA_trace_ac :
    hasTrace vgPairA (show vgPairA.Vertex from ⟨0, by omega⟩) [ThreeLabel.a, ThreeLabel.c] := by
  exact @hasTrace.cons _ _ _ vgPairA ⟨0, by omega⟩ ⟨2, by omega⟩ ThreeLabel.a [ThreeLabel.c]
    (Or.inr ⟨rfl, rfl⟩)
    (@hasTrace.cons _ _ _ vgPairA ⟨2, by omega⟩ ⟨4, by omega⟩ ThreeLabel.c []
      ⟨rfl, rfl⟩ (hasTrace.nil _))

/-- vgPairB has trace [] from root. -/
theorem vgPairB_trace_nil :
    hasTrace vgPairB (show vgPairB.Vertex from ⟨0, by omega⟩) [] :=
  hasTrace.nil _

/-- vgPairB has trace [a] from root: s0 -a-> s1. -/
theorem vgPairB_trace_a :
    hasTrace vgPairB (show vgPairB.Vertex from ⟨0, by omega⟩) [ThreeLabel.a] := by
  exact @hasTrace.cons _ _ _ vgPairB ⟨0, by omega⟩ ⟨1, by omega⟩ ThreeLabel.a []
    ⟨rfl, rfl⟩ (hasTrace.nil _)

/-- vgPairB has trace [a, b] from root: s0 -a-> s1 -b-> s2. -/
theorem vgPairB_trace_ab :
    hasTrace vgPairB (show vgPairB.Vertex from ⟨0, by omega⟩) [ThreeLabel.a, ThreeLabel.b] := by
  exact @hasTrace.cons _ _ _ vgPairB ⟨0, by omega⟩ ⟨1, by omega⟩ ThreeLabel.a [ThreeLabel.b]
    ⟨rfl, rfl⟩
    (@hasTrace.cons _ _ _ vgPairB ⟨1, by omega⟩ ⟨2, by omega⟩ ThreeLabel.b []
      ⟨rfl, rfl⟩ (hasTrace.nil _))

/-- vgPairB has trace [a, c] from root: s0 -a-> s1 -c-> s2. -/
theorem vgPairB_trace_ac :
    hasTrace vgPairB (show vgPairB.Vertex from ⟨0, by omega⟩) [ThreeLabel.a, ThreeLabel.c] := by
  exact @hasTrace.cons _ _ _ vgPairB ⟨0, by omega⟩ ⟨1, by omega⟩ ThreeLabel.a [ThreeLabel.c]
    ⟨rfl, rfl⟩
    (@hasTrace.cons _ _ _ vgPairB ⟨1, by omega⟩ ⟨2, by omega⟩ ThreeLabel.c []
      ⟨rfl, rfl⟩ (hasTrace.nil _))

/-- Helper: no edges from vertex v in vgPairA if v.val >= 3. -/
private theorem vgPairA_dead (v : vgPairA.Vertex) (hv : v.val ≥ 3) (l : ThreeLabel)
    (w : vgPairA.Vertex) : ¬vgPairA.edge l v w := by
  unfold vgPairA; intro h; cases l <;> simp [vgPairA_edge] at h <;> omega

/-- Helper: no edges from vertex v in vgPairB if v.val >= 2. -/
private theorem vgPairB_dead (v : vgPairB.Vertex) (hv : v.val ≥ 2) (l : ThreeLabel)
    (w : vgPairB.Vertex) : ¬vgPairB.edge l v w := by
  unfold vgPairB; intro h; cases l <;> simp [vgPairB_edge] at h <;> omega

/-- Helper: no edges from any vertex v with v.val >= 3 in vgPairA. -/
private theorem vgPairA_no_trace_from_dead (v : vgPairA.Vertex) (hv : v.val ≥ 3)
    (w : List ThreeLabel) (h : hasTrace vgPairA v w) : w = [] := by
  cases h with
  | nil => rfl
  | cons l t e _ =>
    change vgPairA_edge l v _ at e
    exfalso; cases l <;> simp [vgPairA_edge] at e <;> omega

/-- Helper: traces from s1 (val=1) in vgPairA are exactly {[], [b]}. -/
private theorem vgPairA_traces_from_1 (v : vgPairA.Vertex) (hv : v.val = 1)
    (w : List ThreeLabel) (h : hasTrace vgPairA v w) :
    w = [] ∨ w = [ThreeLabel.b] := by
  cases h with
  | nil => left; rfl
  | cons l t e ht =>
    change vgPairA_edge l v _ at e
    match l with
    | ThreeLabel.a => simp [vgPairA_edge] at e; omega
    | ThreeLabel.c => simp [vgPairA_edge] at e; omega
    | ThreeLabel.b =>
      simp [vgPairA_edge] at e; obtain ⟨_, hw⟩ := e
      have := vgPairA_no_trace_from_dead _ (by omega) t ht
      right; rw [this]

/-- Helper: traces from s2 (val=2) in vgPairA are exactly {[], [c]}. -/
private theorem vgPairA_traces_from_2 (v : vgPairA.Vertex) (hv : v.val = 2)
    (w : List ThreeLabel) (h : hasTrace vgPairA v w) :
    w = [] ∨ w = [ThreeLabel.c] := by
  cases h with
  | nil => left; rfl
  | cons l t e ht =>
    change vgPairA_edge l v _ at e
    match l with
    | ThreeLabel.a => simp [vgPairA_edge] at e; omega
    | ThreeLabel.b => simp [vgPairA_edge] at e; omega
    | ThreeLabel.c =>
      simp [vgPairA_edge] at e; obtain ⟨_, hw⟩ := e
      have := vgPairA_no_trace_from_dead _ (by omega) t ht
      right; rw [this]

/-- Helper: traces from s0 (val=0) in vgPairA are exactly {[], [a], [a,b], [a,c]}. -/
private theorem vgPairA_traces_from_0 (v : vgPairA.Vertex) (hv : v.val = 0)
    (w : List ThreeLabel) (h : hasTrace vgPairA v w) :
    w = [] ∨ w = [ThreeLabel.a] ∨ w = [ThreeLabel.a, ThreeLabel.b] ∨
    w = [ThreeLabel.a, ThreeLabel.c] := by
  cases h with
  | nil => left; rfl
  | cons l t e ht =>
    change vgPairA_edge l v _ at e
    match l with
    | ThreeLabel.b => simp [vgPairA_edge] at e; omega
    | ThreeLabel.c => simp [vgPairA_edge] at e; omega
    | ThreeLabel.a =>
      simp [vgPairA_edge] at e
      rcases e with ⟨_, hw⟩ | ⟨_, hw⟩
      · -- Target s1 (val = 1)
        rcases vgPairA_traces_from_1 _ (by omega) t ht with rfl | rfl
        · right; left; rfl
        · right; right; left; rfl
      · -- Target s2 (val = 2)
        rcases vgPairA_traces_from_2 _ (by omega) t ht with rfl | rfl
        · right; left; rfl
        · right; right; right; rfl

/-- Helper: no edges from vertex v with v.val >= 2 in vgPairB. -/
private theorem vgPairB_no_trace_from_dead (v : vgPairB.Vertex) (hv : v.val ≥ 2)
    (w : List ThreeLabel) (h : hasTrace vgPairB v w) : w = [] := by
  cases h with
  | nil => rfl
  | cons l t e _ =>
    change vgPairB_edge l v _ at e
    exfalso; cases l <;> simp [vgPairB_edge] at e <;> omega

/-- Helper: traces from s1 (val=1) in vgPairB are exactly {[], [b], [c]}. -/
private theorem vgPairB_traces_from_1 (v : vgPairB.Vertex) (hv : v.val = 1)
    (w : List ThreeLabel) (h : hasTrace vgPairB v w) :
    w = [] ∨ w = [ThreeLabel.b] ∨ w = [ThreeLabel.c] := by
  cases h with
  | nil => left; rfl
  | cons l t e ht =>
    change vgPairB_edge l v _ at e
    match l with
    | ThreeLabel.a => simp [vgPairB_edge] at e; omega
    | ThreeLabel.b =>
      simp [vgPairB_edge] at e; obtain ⟨_, hw⟩ := e
      have := vgPairB_no_trace_from_dead _ (by omega) t ht
      right; left; rw [this]
    | ThreeLabel.c =>
      simp [vgPairB_edge] at e; obtain ⟨_, hw⟩ := e
      have := vgPairB_no_trace_from_dead _ (by omega) t ht
      right; right; rw [this]

/-- Helper: traces from s0 (val=0) in vgPairB are exactly {[], [a], [a,b], [a,c]}. -/
private theorem vgPairB_traces_from_0 (v : vgPairB.Vertex) (hv : v.val = 0)
    (w : List ThreeLabel) (h : hasTrace vgPairB v w) :
    w = [] ∨ w = [ThreeLabel.a] ∨ w = [ThreeLabel.a, ThreeLabel.b] ∨
    w = [ThreeLabel.a, ThreeLabel.c] := by
  cases h with
  | nil => left; rfl
  | cons l t e ht =>
    change vgPairB_edge l v _ at e
    match l with
    | ThreeLabel.b => simp [vgPairB_edge] at e; omega
    | ThreeLabel.c => simp [vgPairB_edge] at e; omega
    | ThreeLabel.a =>
      simp [vgPairB_edge] at e; obtain ⟨_, hw⟩ := e
      rcases vgPairB_traces_from_1 _ (by omega) t ht with rfl | rfl | rfl
      · right; left; rfl
      · right; right; left; rfl
      · right; right; right; rfl

/-- vgPairA and vgPairB are trace equivalent: both have trace set {[], [a], [a,b], [a,c]}
    from their respective root vertices. -/
theorem vgPairA_traceEquiv_vgPairB :
    labeledTraceEquiv vgPairA (show vgPairA.Vertex from ⟨0, by omega⟩)
                      vgPairB (show vgPairB.Vertex from ⟨0, by omega⟩) := by
  unfold labeledTraceEquiv labeledTraceSet
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · -- A → B
    intro h
    rcases vgPairA_traces_from_0 _ rfl w h with rfl | rfl | rfl | rfl
    · exact vgPairB_trace_nil
    · exact vgPairB_trace_a
    · exact vgPairB_trace_ab
    · exact vgPairB_trace_ac
  · -- B → A
    intro h
    rcases vgPairB_traces_from_0 _ rfl w h with rfl | rfl | rfl | rfl
    · exact vgPairA_trace_nil
    · exact vgPairA_trace_a
    · exact vgPairA_trace_ab
    · exact vgPairA_trace_ac

end RTS.PresheafTopos
