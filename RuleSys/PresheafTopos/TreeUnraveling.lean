/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Bounded Tree Unraveling for Labeled Transition Systems

Given a pointed FinLTS (G, v) and depth bound d : ℕ, we construct a new FinLTS whose
vertices are computation paths from v of length ≤ d. This yields a rooted tree
bisimilar to (G, v) up to depth d.

## Key Definitions

- `TreeVertex`: Bounded computation paths from a root vertex
- `treeUnravelLTS`: The unraveled tree as a FinLTS
- `treeProjection`: Label-preserving homomorphism projecting the tree back to G

## Key Results

- `treeUnravel_isRootedTree`: The unraveled LTS is a rooted tree
- `treeProjection_back`: Back condition — every G-edge from the endpoint of a
  non-maximal path lifts to the tree
- `treeUnravel_depth_bound`: Every vertex has path length ≤ d
- `treeUnravel_endpoint_edge`: Tree edges correspond to G edges between endpoints

## References

- Joyal-Nielsen-Winskel, "Bisimulation from open maps" (1996)
- Grädel-Thomas-Wilke, "Automata, Logics, and Infinite Games" (2002), §2
-/

import RuleSys.PresheafTopos.LabeledBisimTopology
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector

set_option autoImplicit false

namespace RTS.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: Valid Paths and TreeVertex
-/

/-- A computation path from root vertex `v` in LTS `G` is valid if each consecutive
    step follows an edge in G. Defined recursively on the list structure. -/
def ValidPath (G : FinLTS L) (v : G.Vertex) : List (L × G.Vertex) → Prop
  | [] => True
  | [(a, w)] => G.edge a v w
  | (a, w) :: (b, u) :: rest => G.edge a v w ∧ ValidPath G w ((b, u) :: rest)

instance ValidPath.decidable (G : FinLTS L) (v : G.Vertex) :
    DecidablePred (ValidPath G v) := by
  intro path
  induction path generalizing v with
  | nil => exact isTrue trivial
  | cons p ps ih =>
    obtain ⟨a, w⟩ := p
    cases ps with
    | nil =>
      simp only [ValidPath]
      exact G.edgeDecidable a v w
    | cons q qs =>
      obtain ⟨b, u⟩ := q
      simp only [ValidPath]
      haveI := G.edgeDecidable a v w
      haveI := ih w
      exact inferInstance

/-- The endpoint of a computation path: the last vertex visited, or the root if empty. -/
def pathEndpoint (G : FinLTS L) (v : G.Vertex) : List (L × G.Vertex) → G.Vertex
  | [] => v
  | [(_, w)] => w
  | (_, w) :: (b, u) :: rest => pathEndpoint G w ((b, u) :: rest)

/-- TreeVertex: computation paths from root v of length ≤ d that follow edges in G. -/
def TreeVertex (G : FinLTS L) (v : G.Vertex) (d : ℕ) : Type :=
  { path : List (L × G.Vertex) // ValidPath G v path ∧ path.length ≤ d }

/-- The endpoint of a tree vertex in the original LTS. -/
def TreeVertex.endpoint {G : FinLTS L} {v : G.Vertex} {d : ℕ}
    (p : TreeVertex G v d) : G.Vertex :=
  pathEndpoint G v p.val

/-- The path length (number of steps) of a tree vertex. -/
def TreeVertex.pathLength {G : FinLTS L} {v : G.Vertex} {d : ℕ}
    (p : TreeVertex G v d) : ℕ :=
  p.val.length

/-- The root path: empty path at the root vertex. -/
def TreeVertex.rootPath (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    TreeVertex G v d :=
  ⟨[], ⟨trivial, Nat.zero_le d⟩⟩

theorem TreeVertex.rootPath_endpoint (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    (TreeVertex.rootPath G v d).endpoint = v := rfl

theorem TreeVertex.rootPath_pathLength (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    (TreeVertex.rootPath G v d).pathLength = 0 := rfl

/-- DecidableEq for TreeVertex via the underlying list. -/
instance TreeVertex.instDecidableEq (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    DecidableEq (TreeVertex G v d) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩
  by_cases h : p = q
  · exact isTrue (Subtype.ext h)
  · exact isFalse (fun heq => h (congrArg Subtype.val heq))

/-- TreeVertex is finite: it is a decidable subtype of bounded-length lists over a
    finite alphabet. We show this via equivalence with a sigma type of vectors. -/
instance TreeVertex.instFintype (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    Fintype (TreeVertex G v d) := by
  letI := G.vertexFintype
  letI := G.vertexDecEq
  letI : Fintype (L × G.Vertex) := instFintypeProd L G.Vertex
  letI : DecidableEq (L × G.Vertex) := instDecidableEqProd
  -- Bounded-length lists over a finite type are finite
  letI : Fintype { l : List (L × G.Vertex) // l.length ≤ d } :=
    Fintype.ofEquiv (Σ (k : Fin (d + 1)), List.Vector (L × G.Vertex) k.val)
      { toFun := fun ⟨k, ⟨l, hl⟩⟩ => ⟨l, hl ▸ Nat.le_of_lt_succ k.isLt⟩
        invFun := fun ⟨l, hl⟩ => ⟨⟨l.length, Nat.lt_succ_of_le hl⟩, ⟨l, rfl⟩⟩
        left_inv := fun ⟨k, ⟨l, hl⟩⟩ => by
          cases k with
          | mk kv hk =>
            simp only at hl
            subst hl
            rfl
        right_inv := fun ⟨l, hl⟩ => by simp }
  -- TreeVertex is a decidable subtype of bounded-length lists
  exact Fintype.ofEquiv
    { bl : { l : List (L × G.Vertex) // l.length ≤ d } // ValidPath G v bl.val }
    { toFun := fun ⟨⟨l, hl⟩, hv⟩ => ⟨l, ⟨hv, hl⟩⟩
      invFun := fun ⟨l, hv, hl⟩ => ⟨⟨l, hl⟩, hv⟩
      left_inv := fun ⟨⟨l, hl⟩, hv⟩ => rfl
      right_inv := fun ⟨l, hv, hl⟩ => rfl }

/-!
## Part 2: Path Operations
-/

/-- ValidPath is preserved when we drop the first step and re-root. -/
theorem ValidPath_tail (G : FinLTS L) (v : G.Vertex)
    (a : L) (w : G.Vertex) (rest : List (L × G.Vertex))
    (hvalid : ValidPath G v ((a, w) :: rest)) : ValidPath G w rest := by
  cases rest with
  | nil => trivial
  | cons p ps =>
    obtain ⟨b, u⟩ := p
    exact hvalid.2

/-- If a path from v is valid and its endpoint has an edge to w,
    then the extended path is valid. -/
theorem ValidPath_extend (G : FinLTS L) (v : G.Vertex)
    (path : List (L × G.Vertex)) (a : L) (w : G.Vertex)
    (hvalid : ValidPath G v path) (hedge : G.edge a (pathEndpoint G v path) w) :
    ValidPath G v (path ++ [(a, w)]) := by
  induction path generalizing v with
  | nil =>
    simp only [List.nil_append, pathEndpoint] at hedge ⊢
    exact hedge
  | cons p ps ih =>
    obtain ⟨b, u⟩ := p
    cases ps with
    | nil =>
      simp only [ValidPath, pathEndpoint] at hvalid hedge ⊢
      exact ⟨hvalid, hedge⟩
    | cons q qs =>
      simp only [List.cons_append, ValidPath, pathEndpoint] at hvalid hedge ⊢
      exact ⟨hvalid.1, ih u hvalid.2 hedge⟩

/-- Dropping the last element preserves validity. -/
theorem ValidPath_dropLast (G : FinLTS L) (v : G.Vertex)
    (init : List (L × G.Vertex)) (a : L) (w : G.Vertex)
    (hvalid : ValidPath G v (init ++ [(a, w)])) :
    ValidPath G v init := by
  induction init generalizing v with
  | nil => exact trivial
  | cons p ps ih =>
    obtain ⟨b, u⟩ := p
    cases ps with
    | nil =>
      simp [ValidPath, List.cons_append] at hvalid ⊢
      exact hvalid.1
    | cons q qs =>
      simp only [List.cons_append, ValidPath] at hvalid ⊢
      exact ⟨hvalid.1, ih u hvalid.2⟩

/-- The endpoint of an extended path is the newly appended vertex. -/
theorem pathEndpoint_append_singleton (G : FinLTS L) (v : G.Vertex)
    (path : List (L × G.Vertex)) (a : L) (w : G.Vertex) :
    pathEndpoint G v (path ++ [(a, w)]) = w := by
  induction path generalizing v with
  | nil => simp [pathEndpoint]
  | cons p ps ih =>
    obtain ⟨b, u⟩ := p
    cases ps with
    | nil => simp [pathEndpoint]
    | cons q qs =>
      simp only [List.cons_append, pathEndpoint]
      exact ih u

/-- The edge from the init endpoint to the appended vertex. -/
theorem pathEndpoint_edge_of_append (G : FinLTS L) (v : G.Vertex)
    (init : List (L × G.Vertex)) (a : L) (w : G.Vertex)
    (hvalid : ValidPath G v (init ++ [(a, w)])) :
    G.edge a (pathEndpoint G v init) w := by
  induction init generalizing v with
  | nil =>
    simp [pathEndpoint, ValidPath, List.nil_append] at hvalid ⊢
    exact hvalid
  | cons p ps ih =>
    obtain ⟨b, u⟩ := p
    cases ps with
    | nil =>
      simp [pathEndpoint, ValidPath] at hvalid ⊢
      exact hvalid.2
    | cons q qs =>
      simp only [List.cons_append, ValidPath, pathEndpoint] at hvalid ⊢
      exact ih u hvalid.2

/-- Every non-empty list can be split into init ++ [last]. -/
private theorem list_exists_append_last {α : Type} :
    ∀ (l : List α), l ≠ [] → ∃ (init : List α) (x : α), l = init ++ [x]
  | [], h => absurd rfl h
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: rest, _ => by
    have ⟨init, z, heq⟩ := list_exists_append_last (y :: rest) (List.cons_ne_nil y rest)
    exact ⟨x :: init, z, by rw [heq, List.cons_append]⟩

/-!
## Part 3: TreeVertex Extension
-/

/-- Extend a tree vertex by one step when possible. -/
def TreeVertex.extend {G : FinLTS L} {v : G.Vertex} {d : ℕ}
    (p : TreeVertex G v d) (a : L) (w : G.Vertex)
    (hedge : G.edge a p.endpoint w) (hlen : p.pathLength < d) :
    TreeVertex G v d :=
  ⟨p.val ++ [(a, w)],
   ⟨ValidPath_extend G v p.val a w p.property.1 hedge,
    by rw [List.length_append, List.length_singleton]; exact hlen⟩⟩

theorem TreeVertex.extend_val {G : FinLTS L} {v : G.Vertex} {d : ℕ}
    (p : TreeVertex G v d) (a : L) (w : G.Vertex)
    (hedge : G.edge a p.endpoint w) (hlen : p.pathLength < d) :
    (p.extend a w hedge hlen).val = p.val ++ [(a, w)] := rfl

theorem TreeVertex.extend_endpoint {G : FinLTS L} {v : G.Vertex} {d : ℕ}
    (p : TreeVertex G v d) (a : L) (w : G.Vertex)
    (hedge : G.edge a p.endpoint w) (hlen : p.pathLength < d) :
    (p.extend a w hedge hlen).endpoint = w := by
  simp [TreeVertex.extend, TreeVertex.endpoint, pathEndpoint_append_singleton]

theorem TreeVertex.extend_pathLength {G : FinLTS L} {v : G.Vertex} {d : ℕ}
    (p : TreeVertex G v d) (a : L) (w : G.Vertex)
    (hedge : G.edge a p.endpoint w) (hlen : p.pathLength < d) :
    (p.extend a w hedge hlen).pathLength = p.pathLength + 1 := by
  simp [TreeVertex.extend, TreeVertex.pathLength, List.length_append]

/-!
## Part 4: The Tree Unraveling LTS
-/

/-- Edge predicate for the tree unraveling: q extends p by exactly one step (a, w)
    where G.edge a (endpoint p) w. -/
def treeEdgePred (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : TreeVertex G v d) : Prop :=
  q.val = p.val ++ [(a, q.endpoint)] ∧ G.edge a p.endpoint q.endpoint

instance treeEdgePred_decidable (G : FinLTS L) (v : G.Vertex) (d : ℕ) (a : L) :
    DecidableRel (treeEdgePred G v d a) := by
  intro p q
  simp only [treeEdgePred]
  haveI := inferInstanceAs (Decidable (q.val = p.val ++ [(a, q.endpoint)]))
  haveI := G.edgeDecidable a p.endpoint q.endpoint
  exact inferInstance

/-- The bounded tree unraveling of (G, v) at depth d.
    Vertices are valid computation paths of length ≤ d,
    edges extend paths by one step. -/
def treeUnravelLTS (G : FinLTS L) (v : G.Vertex) (d : ℕ) : FinLTS L where
  Vertex := TreeVertex G v d
  edge := treeEdgePred G v d

/-!
## Part 5: Projection Homomorphism
-/

/-- The projection maps each tree vertex to its endpoint in G. -/
def treeProjection (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    LTSHom (treeUnravelLTS G v d) G where
  toFun := TreeVertex.endpoint
  map_edge := fun _ _ _ ⟨_, hedge⟩ => hedge

/-- The projection sends the root path to v. -/
theorem treeProjection_root (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    (treeProjection G v d).toFun (TreeVertex.rootPath G v d) = v := rfl

/-!
## Part 6: Rooted Tree Property
-/

/-- The root path has no incoming edges in the tree. -/
theorem treeUnravel_no_edge_to_root (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p : (treeUnravelLTS G v d).Vertex) :
    ¬(treeUnravelLTS G v d).edge a p (TreeVertex.rootPath G v d) := by
  intro ⟨heq, _⟩
  simp [TreeVertex.rootPath] at heq

/-- The tree unraveling is a labeled rooted tree. -/
theorem treeUnravel_isRootedTree (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    LabeledIsRootedTree (treeUnravelLTS G v d) := by
  refine ⟨TreeVertex.rootPath G v d, ?_, ?_, ?_⟩
  · -- (1) No incoming edges to root
    intro a p he
    exact treeUnravel_no_edge_to_root G v d a p he
  · -- (2) Unique parent for non-root vertices
    intro q hne
    have hq_ne : q.val ≠ [] := by
      intro h; apply hne; exact Subtype.ext h
    obtain ⟨init, ⟨a, w⟩, heq⟩ := list_exists_append_last q.val hq_ne
    have hinit_valid : ValidPath G v init :=
      ValidPath_dropLast G v init a w (heq ▸ q.property.1)
    have hinit_len : init.length ≤ d := by
      have h1 := q.property.2
      rw [heq, List.length_append, List.length_singleton] at h1
      exact Nat.le_of_succ_le h1
    let parent : TreeVertex G v d := ⟨init, hinit_valid, hinit_len⟩
    have hq_ep : q.endpoint = w := by
      simp only [TreeVertex.endpoint]
      rw [heq]
      exact pathEndpoint_append_singleton G v init a w
    refine ⟨parent, ?_, ?_⟩
    · -- Edge from parent to q
      refine ⟨a, ?_, ?_⟩
      · -- q.val = parent.val ++ [(a, q.endpoint)]
        show q.val = init ++ [(a, q.endpoint)]
        rw [heq, hq_ep]
      · -- G.edge a parent.endpoint q.endpoint
        show G.edge a (pathEndpoint G v init) q.endpoint
        rw [hq_ep]
        exact pathEndpoint_edge_of_append G v init a w (heq ▸ q.property.1)
    · -- Uniqueness
      intro p' ⟨a', heq', _⟩
      have h1 : p'.val ++ [(a', q.endpoint)] = init ++ [(a, w)] := by
        rw [← heq', ← heq]
      have : p'.val = init :=
        (List.append_inj h1 (by
          have : (p'.val ++ [(a', q.endpoint)]).length = (init ++ [(a, w)]).length :=
            congrArg List.length h1
          simp [List.length_append] at this
          exact this)).1
      exact Subtype.ext this
  · -- (3) All reachable from root
    intro q
    suffices h : ∀ (n : ℕ) (path : List (L × G.Vertex))
        (hv : ValidPath G v path) (hlen : path.length ≤ d)
        (hn : path.length = n),
        LabeledReachable (treeUnravelLTS G v d)
          (TreeVertex.rootPath G v d) ⟨path, hv, hlen⟩ by
      exact h q.val.length q.val q.property.1 q.property.2 rfl
    intro n
    induction n with
    | zero =>
      intro path hv hlen hn
      have hpath : path = [] := by
        cases path with
        | nil => rfl
        | cons _ _ => simp at hn
      subst hpath
      exact LabeledReachable.refl _
    | succ k ih =>
      intro path hv hlen hn
      have hne : path ≠ [] := by intro h; rw [h] at hn; simp at hn
      obtain ⟨init, ⟨a, w⟩, heq⟩ := list_exists_append_last path hne
      have hinit_len_eq : init.length = k := by
        have : path.length = init.length + 1 := by
          rw [heq, List.length_append, List.length_singleton]
        rw [hn] at this
        exact Nat.succ.inj this.symm
      have hinit_valid : ValidPath G v init :=
        ValidPath_dropLast G v init a w (heq ▸ hv)
      have hinit_len : init.length ≤ d := by
        rw [hinit_len_eq]
        exact Nat.le_of_succ_le (hinit_len_eq ▸ (by
          rw [heq, List.length_append, List.length_singleton] at hlen
          exact hlen))
      have ih_reach := ih init hinit_valid hinit_len hinit_len_eq
      have hedge_aw : G.edge a (pathEndpoint G v init) w :=
        pathEndpoint_edge_of_append G v init a w (heq ▸ hv)
      have hq_ep : pathEndpoint G v path = w := by
        rw [heq]; exact pathEndpoint_append_singleton G v init a w
      have tree_edge : (treeUnravelLTS G v d).edge a
          ⟨init, hinit_valid, hinit_len⟩
          ⟨path, hv, hlen⟩ := by
        constructor
        · show path = init ++ [(a, pathEndpoint G v path)]
          rw [heq, pathEndpoint_append_singleton]
        · show G.edge a (pathEndpoint G v init) (pathEndpoint G v path)
          rw [hq_ep]
          exact hedge_aw
      exact ih_reach.trans
        (LabeledReachable.step a tree_edge (LabeledReachable.refl _))

/-!
## Part 7: Back Condition and API Lemmas
-/

/-- Forward condition: tree edges project to G edges. -/
theorem treeProjection_forward (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a p q) :
    G.edge a p.endpoint q.endpoint :=
  h.2

/-- Depth bound: every tree vertex has path length ≤ d. -/
theorem treeUnravel_depth_bound (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (p : (treeUnravelLTS G v d).Vertex) :
    p.pathLength ≤ d :=
  p.property.2

/-- Tree edges correspond to G edges between endpoints. -/
theorem treeUnravel_endpoint_edge (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a p q) :
    G.edge a ((treeProjection G v d).toFun p) ((treeProjection G v d).toFun q) :=
  h.2

/-- Back condition: every G-edge from a non-maximal path's endpoint lifts to the tree. -/
theorem treeProjection_back (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (p : (treeUnravelLTS G v d).Vertex) (hlen : p.pathLength < d)
    (a : L) (w : G.Vertex) (hedge : G.edge a p.endpoint w) :
    ∃ q : (treeUnravelLTS G v d).Vertex,
      (treeUnravelLTS G v d).edge a p q ∧
      (treeProjection G v d).toFun q = w := by
  let q := p.extend a w hedge hlen
  refine ⟨q, ?_, ?_⟩
  · -- Tree edge from p to q
    show treeEdgePred G v d a p q
    constructor
    · show q.val = p.val ++ [(a, q.endpoint)]
      rw [TreeVertex.extend_val, TreeVertex.extend_endpoint]
    · rw [TreeVertex.extend_endpoint]
      exact hedge
  · show q.endpoint = w
    exact TreeVertex.extend_endpoint p a w hedge hlen

end RTS.PresheafTopos
