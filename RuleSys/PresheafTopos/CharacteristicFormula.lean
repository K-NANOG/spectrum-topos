/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Characteristic Formulas for Tree Unravelings

This file defines the characteristic HML formula of a vertex in a bounded tree
unraveling, and proves that satisfaction of this formula exactly characterizes
the existence of a label-preserving homomorphism from the tree.

## Key Definitions

- `conjAll`: conjunction of all formulas in a list
- `characteristicHML`: the characteristic formula of a tree vertex
- `characteristicHML_depth_le`: depth bound on the characteristic formula

## Key Results

- `characteristicHML_of_hom`: LTSHom → satisfaction (forward direction)
- `characteristicHML_iff`: χ(T,root).satisfies H w ↔ ∃ f : LTSHom T H, f(root) = w

## References

- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
- van Glabbeek, "The linear time--branching time spectrum I" (1990)
-/

import RuleSys.PresheafTopos.EqualityElimination

set_option autoImplicit false

namespace RTS.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: n-ary Conjunction via List folding
-/

/-- Fold a list of formulas into a conjunction, with ⊤ as base. -/
def conjAll : List (LabeledHML L) → LabeledHML L
  | [] => .top
  | φ :: rest => .conj φ (conjAll rest)

/-- Satisfaction of conjAll: all formulas in the list are satisfied. -/
theorem conjAll_satisfies (G : FinLTS L) (v : G.Vertex)
    (φs : List (LabeledHML L)) :
    (conjAll φs).satisfies G v ↔ ∀ φ, φ ∈ φs → φ.satisfies G v := by
  induction φs with
  | nil =>
    simp [conjAll, LabeledHML.satisfies]
  | cons φ rest ih =>
    simp only [conjAll, LabeledHML.satisfies, List.mem_cons]
    constructor
    · rintro ⟨hφ, hrest⟩ χ (rfl | hχ)
      · exact hφ
      · exact ih.mp hrest χ hχ
    · intro h
      exact ⟨h φ (Or.inl rfl), ih.mpr fun χ hχ => h χ (Or.inr hχ)⟩

omit [Fintype L] [DecidableEq L] in
/-- Depth of conjAll: bounded by max depth of elements. -/
theorem conjAll_depth_le (φs : List (LabeledHML L)) (bound : ℕ)
    (h : ∀ φ, φ ∈ φs → φ.depth ≤ bound) :
    (conjAll φs).depth ≤ bound := by
  induction φs with
  | nil =>
    simp [conjAll, LabeledHML.depth]
  | cons φ rest ih =>
    simp only [conjAll, LabeledHML.depth]
    apply Nat.max_le.mpr
    constructor
    · exact h φ List.mem_cons_self
    · exact ih fun χ hχ => h χ (List.mem_cons_of_mem φ hχ)

/-!
## Part 2: Tree Children List
-/

/-- The list of (label, child) pairs for a tree vertex t. -/
noncomputable def treeChildList (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex) :
    List (L × (treeUnravelLTS G v d).Vertex) :=
  ((Finset.univ (α := L) ×ˢ Finset.univ (α := (treeUnravelLTS G v d).Vertex)).filter
    fun aq => (treeUnravelLTS G v d).edge aq.1 t aq.2).val.toList

/-- Every child pair is in the list. -/
theorem treeChildList_complete (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t q : (treeUnravelLTS G v d).Vertex) (a : L)
    (h : (treeUnravelLTS G v d).edge a t q) :
    (a, q) ∈ treeChildList G v d t := by
  simp only [treeChildList, Multiset.mem_toList, Finset.mem_val,
    Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  exact h

/-- Every element in the list is a valid child pair. -/
theorem treeChildList_spec (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex)
    (aq : L × (treeUnravelLTS G v d).Vertex)
    (h : aq ∈ treeChildList G v d t) :
    (treeUnravelLTS G v d).edge aq.1 t aq.2 := by
  simp only [treeChildList, Multiset.mem_toList, Finset.mem_val,
    Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at h
  exact h

/-- At max depth (d - t.pathLength = 0), there are no children. -/
theorem treeChildList_empty_at_max (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex)
    (hk : d - t.pathLength = 0) :
    treeChildList G v d t = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro aq haq
  have hedge := treeChildList_spec G v d t aq haq
  have hpl := treeEdge_succ_pathLength G v d aq.1 t aq.2 hedge
  have hbd := treeUnravel_depth_bound G v d aq.2
  omega

/-!
## Part 3: Characteristic Formula by Natural Number Recursion
-/

/-- Auxiliary: characteristic formula with explicit depth budget k.
    When k = 0, returns ⊤ (no more diamonds can be added).
    When k = n + 1, returns the conjunction of ◇a(χ_n(q)) for all children. -/
noncomputable def characteristicHMLAux (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    ℕ → (treeUnravelLTS G v d).Vertex → LabeledHML L
  | 0, _ => .top
  | k + 1, t =>
    conjAll ((treeChildList G v d t).map fun aq =>
      LabeledHML.diamond aq.1 (characteristicHMLAux G v d k aq.2))

/-- The characteristic formula uses d - t.pathLength as the depth budget. -/
noncomputable def characteristicHML (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex) : LabeledHML L :=
  characteristicHMLAux G v d (d - t.pathLength) t

/-!
## Part 4: Budget Agreement

The key technical lemma: characteristicHMLAux k t = characteristicHMLAux (d - t.pathLength) t
whenever k ≥ d - t.pathLength. This is needed to show the unfolding equation.
-/

/-- With any budget k ≥ d - t.pathLength, the characteristic formula is the same. -/
theorem characteristicHMLAux_budget_agree (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (k : ℕ) (t : (treeUnravelLTS G v d).Vertex)
    (hk : d - t.pathLength ≤ k) :
    characteristicHMLAux G v d k t = characteristicHMLAux G v d (d - t.pathLength) t := by
  induction k generalizing t with
  | zero =>
    have h0 : d - t.pathLength = 0 := by omega
    rw [h0]
  | succ n ih =>
    by_cases h0 : d - t.pathLength = 0
    · -- Both sides give ⊤ since no children exist
      rw [h0]
      have hempty := treeChildList_empty_at_max G v d t h0
      simp [characteristicHMLAux, hempty, conjAll]
    · -- d - t.pathLength = m + 1 for some m
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [hm]
      simp only [characteristicHMLAux]
      congr 1
      apply List.map_congr_left
      intro aq haq
      have hedge := treeChildList_spec G v d t aq haq
      have hpl := treeEdge_succ_pathLength G v d aq.1 t aq.2 hedge
      have hbd := treeUnravel_depth_bound G v d aq.2
      have hleq : d - aq.2.pathLength ≤ n := by omega
      have hgoal : d - aq.2.pathLength = m := by
        have : d ≥ t.pathLength + 1 := by omega
        omega
      rw [ih aq.2 hleq, hgoal]

/-- The characteristic formula unfolds: χ(t) = ⋀ ◇a(χ(q)) for children (a,q) of t. -/
theorem characteristicHML_unfold (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex) :
    characteristicHML G v d t =
    conjAll ((treeChildList G v d t).map fun aq =>
      LabeledHML.diamond aq.1 (characteristicHML G v d aq.2)) := by
  simp only [characteristicHML]
  by_cases h0 : d - t.pathLength = 0
  · -- No children at max depth: both sides are ⊤
    have hempty := treeChildList_empty_at_max G v d t h0
    rw [h0]
    simp [hempty, conjAll, characteristicHMLAux]
  · -- d - t.pathLength = k + 1 for some k
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [hk, characteristicHMLAux]
    congr 1
    apply List.map_congr_left
    intro aq haq
    have hedge := treeChildList_spec G v d t aq haq
    have hpl := treeEdge_succ_pathLength G v d aq.1 t aq.2 hedge
    have hbd := treeUnravel_depth_bound G v d aq.2
    have hleq : d - aq.2.pathLength ≤ k := by omega
    exact congrArg (LabeledHML.diamond aq.1) (characteristicHMLAux_budget_agree G v d k aq.2 hleq)

/-!
## Part 5: Satisfaction and Depth Bound
-/

/-- Satisfaction of characteristicHML reduces to checking all tree children. -/
theorem characteristicHML_satisfies_iff (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (H : FinLTS L) (w : H.Vertex)
    (t : (treeUnravelLTS G v d).Vertex) :
    (characteristicHML G v d t).satisfies H w ↔
    ∀ a (q : (treeUnravelLTS G v d).Vertex),
      (treeUnravelLTS G v d).edge a t q →
      ∃ w' : H.Vertex, H.edge a w w' ∧
        (characteristicHML G v d q).satisfies H w' := by
  rw [characteristicHML_unfold, conjAll_satisfies]
  constructor
  · intro hall a q hedge
    have hmem := treeChildList_complete G v d t q a hedge
    have hmap := List.mem_map_of_mem
      (f := fun (aq : L × (treeUnravelLTS G v d).Vertex) =>
        LabeledHML.diamond aq.1 (characteristicHML G v d aq.2)) hmem
    have := hall _ hmap
    simp only [LabeledHML.satisfies] at this
    exact this
  · intro h φ hφ
    obtain ⟨aq, haq_mem, rfl⟩ := List.mem_map.mp hφ
    simp only [LabeledHML.satisfies]
    exact h aq.1 aq.2 (treeChildList_spec G v d t aq haq_mem)

/-- Depth of characteristicHMLAux is bounded by k. -/
theorem characteristicHMLAux_depth_le (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (k : ℕ) (t : (treeUnravelLTS G v d).Vertex) :
    (characteristicHMLAux G v d k t).depth ≤ k := by
  induction k generalizing t with
  | zero =>
    simp [characteristicHMLAux, LabeledHML.depth]
  | succ n ih =>
    simp only [characteristicHMLAux]
    apply conjAll_depth_le
    intro φ hφ
    obtain ⟨aq, _, rfl⟩ := List.mem_map.mp hφ
    simp only [LabeledHML.depth]
    have := ih aq.2
    omega

/-- The depth of the characteristic formula is bounded by d - t.pathLength. -/
theorem characteristicHML_depth_le (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex) :
    (characteristicHML G v d t).depth ≤ d - t.pathLength := by
  simp only [characteristicHML]
  exact characteristicHMLAux_depth_le G v d (d - t.pathLength) t

/-!
## Part 6: Forward Direction — Homomorphism implies Satisfaction

If f : LTSHom (treeUnravelLTS G v d) H sends the root to w, then
χ(root).satisfies H w. The proof proceeds by induction on the depth budget.
-/

/-- Auxiliary forward lemma: if f maps tree edges to H-edges and f(t) = w,
    then characteristicHMLAux k t is satisfied by H at w, for any k ≥ d - t.pathLength. -/
theorem characteristicHMLAux_of_hom (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (H : FinLTS L) (f : LTSHom (treeUnravelLTS G v d) H)
    (k : ℕ) (t : (treeUnravelLTS G v d).Vertex)
    (hk : d - t.pathLength ≤ k) :
    (characteristicHMLAux G v d k t).satisfies H (f.toFun t) := by
  induction k generalizing t with
  | zero =>
    simp [characteristicHMLAux, LabeledHML.satisfies]
  | succ n ih =>
    simp only [characteristicHMLAux]
    rw [conjAll_satisfies]
    intro φ hφ
    obtain ⟨aq, haq_mem, rfl⟩ := List.mem_map.mp hφ
    simp only [LabeledHML.satisfies]
    have hedge := treeChildList_spec G v d t aq haq_mem
    refine ⟨f.toFun aq.2, f.map_edge aq.1 t aq.2 hedge, ?_⟩
    have hpl := treeEdge_succ_pathLength G v d aq.1 t aq.2 hedge
    have hbd := treeUnravel_depth_bound G v d aq.2
    exact ih aq.2 (by omega)

/-- Forward direction: an LTSHom from the tree to H implies satisfaction of the
    characteristic formula. -/
theorem characteristicHML_of_hom (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (H : FinLTS L) (f : LTSHom (treeUnravelLTS G v d) H)
    (t : (treeUnravelLTS G v d).Vertex) :
    (characteristicHML G v d t).satisfies H (f.toFun t) := by
  simp only [characteristicHML]
  exact characteristicHMLAux_of_hom G v d H f (d - t.pathLength) t le_rfl

/-!
## Part 7: Backward Direction — Satisfaction implies Homomorphism

Given χ(root).satisfies H w, we construct an LTSHom from the tree to H.
The key idea: satisfaction of the characteristic formula at a vertex gives
diamond witnesses for all children. We thread these witnesses through an
induction on path length to build the full homomorphism.

The approach: build the assignment function and its properties simultaneously
by Nat recursion on a path-length budget. At each level, we extend the
assignment to one more tree depth using diamond witnesses from the
characteristic formula satisfaction at the parent level.
-/

/-- A non-empty list can be written as init ++ [last]. -/
private theorem list_append_last {α : Type} (l : List α) (h : l ≠ []) :
    ∃ (init : List α) (x : α), l = init ++ [x] := by
  induction l with
  | nil => exact absurd rfl h
  | cons a rest ih =>
    match rest, ih with
    | [], _ => exact ⟨[], a, rfl⟩
    | b :: bs, ih' =>
      obtain ⟨init, x, heq⟩ := ih' (List.cons_ne_nil b bs)
      exact ⟨a :: init, x, by rw [heq, List.cons_append]⟩

/-- Every non-root tree vertex has a parent: there exist a label and parent vertex
    with a tree edge to it. -/
theorem treeVertex_has_parent (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (q : (treeUnravelLTS G v d).Vertex) (hne : q ≠ TreeVertex.rootPath G v d) :
    ∃ (a : L) (p : (treeUnravelLTS G v d).Vertex),
      (treeUnravelLTS G v d).edge a p q := by
  have hq_ne : q.val ≠ [] := by
    intro h; apply hne; exact Subtype.ext h
  obtain ⟨init, ⟨a, w⟩, heq⟩ := list_append_last q.val hq_ne
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
  refine ⟨a, parent, ?_, ?_⟩
  · show q.val = init ++ [(a, q.endpoint)]
    rw [heq, hq_ep]
  · show G.edge a (pathEndpoint G v init) q.endpoint
    rw [hq_ep]
    exact pathEndpoint_edge_of_append G v init a w (heq ▸ q.property.1)

/-- Extract the parent label of a non-root tree vertex (for noncomputable definitions). -/
noncomputable def treeParentLabel (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (q : (treeUnravelLTS G v d).Vertex) (hne : q ≠ TreeVertex.rootPath G v d) : L :=
  (treeVertex_has_parent G v d q hne).choose

/-- Extract the parent vertex of a non-root tree vertex. -/
noncomputable def treeParentVertex (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (q : (treeUnravelLTS G v d).Vertex) (hne : q ≠ TreeVertex.rootPath G v d) :
    (treeUnravelLTS G v d).Vertex :=
  (treeVertex_has_parent G v d q hne).choose_spec.choose

/-- The parent edge property. -/
theorem treeParent_edge (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (q : (treeUnravelLTS G v d).Vertex) (hne : q ≠ TreeVertex.rootPath G v d) :
    (treeUnravelLTS G v d).edge
      (treeParentLabel G v d q hne)
      (treeParentVertex G v d q hne) q :=
  (treeVertex_has_parent G v d q hne).choose_spec.choose_spec

/-- Build the vertex assignment by Nat recursion on path-length budget n.
    The backward direction is proved existentially using Classical.choice. -/
theorem characteristicHML_backward_aux (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (H : FinLTS L) (w : H.Vertex)
    (hsat : (characteristicHML G v d (TreeVertex.rootPath G v d)).satisfies H w) :
    (n : ℕ) →
    ∃ f : (treeUnravelLTS G v d).Vertex → H.Vertex,
      (∀ t : (treeUnravelLTS G v d).Vertex, t.pathLength ≤ n →
        (characteristicHML G v d t).satisfies H (f t)) ∧
      f (TreeVertex.rootPath G v d) = w ∧
      (∀ (a : L) (t q : (treeUnravelLTS G v d).Vertex),
        (treeUnravelLTS G v d).edge a t q →
        q.pathLength ≤ n → H.edge a (f t) (f q))
  | 0 => ⟨fun _ => w,
    fun t ht => by
      have hpl : t.pathLength = 0 := by omega
      have hroot : t = TreeVertex.rootPath G v d := by
        apply Subtype.ext
        exact List.eq_nil_of_length_eq_zero hpl
      rw [hroot]; exact hsat,
    rfl,
    fun a t q hedge hql => by
      have hpl := treeEdge_succ_pathLength G v d a t q hedge
      omega⟩
  | n + 1 => by
    obtain ⟨f_prev, hsat_prev, hroot_prev, hedge_prev⟩ :=
      characteristicHML_backward_aux G v d H w hsat n
    -- For each vertex t at level n + 1, extract the diamond witness
    -- t has a unique parent p at level n, and hsat_prev gives χ(p).satisfies H (f_prev p)
    -- From this, for each child (a, q) of p, we get a witness w' with H.edge and χ(q).satisfies
    -- We just need to assign these witnesses coherently.
    -- Strategy: define the new function by cases on pathLength
    -- For pathLength ≤ n, keep f_prev
    -- For pathLength = n + 1, use the parent's diamond witness
    -- For pathLength > n + 1, use w (doesn't matter)

    -- For each non-root vertex q at level n + 1, extract its parent
    -- and the diamond witness. Since we're in Prop (∃), we can use obtain.
    -- But we need the function to be in data... We're returning ∃ now, so we can
    -- construct the function inside the proof.

    -- Build a function that chooses witnesses for all level-(n+1) vertices
    have h_witnesses : ∀ (t : (treeUnravelLTS G v d).Vertex),
        t.pathLength = n + 1 →
        ∃ (w' : H.Vertex),
          (characteristicHML G v d t).satisfies H w' ∧
          (∀ (a : L) (p : (treeUnravelLTS G v d).Vertex),
            (treeUnravelLTS G v d).edge a p t →
            H.edge a (f_prev p) w') := by
      intro t hpl
      have hne : t ≠ TreeVertex.rootPath G v d := by
        intro h; simp [h, TreeVertex.rootPath, TreeVertex.pathLength] at hpl
      obtain ⟨a, p, hedge⟩ := treeVertex_has_parent G v d t hne
      have hplen := treeEdge_succ_pathLength G v d a p t hedge
      have hpok : p.pathLength ≤ n := by omega
      have hpsat := hsat_prev p hpok
      obtain ⟨w', hedge_w, hsat_w⟩ :=
        (characteristicHML_satisfies_iff G v d H (f_prev p) p).mp hpsat a t hedge
      exact ⟨w', hsat_w, fun a' p' hedge' => by
        have huniq := treeEdge_unique_parent_label G v d a' a p' p t hedge' hedge
        rw [huniq.1, huniq.2]
        exact hedge_w⟩
    -- Use Classical.choice to select witnesses for each level-(n+1) vertex
    classical
    let witness : (t : (treeUnravelLTS G v d).Vertex) → t.pathLength = n + 1 → H.Vertex :=
      fun t hpl => (h_witnesses t hpl).choose
    let witness_sat : ∀ t (hpl : t.pathLength = n + 1),
        (characteristicHML G v d t).satisfies H (witness t hpl) :=
      fun t hpl => (h_witnesses t hpl).choose_spec.1
    let witness_edge : ∀ t (hpl : t.pathLength = n + 1) (a : L) (p : _),
        (treeUnravelLTS G v d).edge a p t → H.edge a (f_prev p) (witness t hpl) :=
      fun t hpl => (h_witnesses t hpl).choose_spec.2
    -- Define the new function
    let f_new : (treeUnravelLTS G v d).Vertex → H.Vertex := fun t =>
      if h : t.pathLength ≤ n then f_prev t
      else if h2 : t.pathLength = n + 1 then witness t h2
      else w
    refine ⟨f_new, ?_, ?_, ?_⟩
    · -- (1) Satisfaction at all vertices with pathLength ≤ n + 1
      intro t ht
      simp only [f_new]
      split
      · exact hsat_prev t (by assumption)
      next hle =>
      split
      · exact witness_sat t (by assumption)
      next h2 =>
        omega
    · -- (2) Root maps to w
      simp only [f_new]
      have : (TreeVertex.rootPath G v d).pathLength ≤ n := by
        simp [TreeVertex.rootPath, TreeVertex.pathLength]
      simp [this]
      exact hroot_prev
    · -- (3) Edge preservation for edges with q.pathLength ≤ n + 1
      intro a t q hedge hql
      have hplen := treeEdge_succ_pathLength G v d a t q hedge
      have htl : t.pathLength ≤ n := by omega
      -- Compute f_new t: since t.pathLength ≤ n, f_new t = f_prev t
      have hft : f_new t = f_prev t := dif_pos htl
      rw [hft]
      by_cases hql' : q.pathLength ≤ n
      · -- q also at level ≤ n: f_new q = f_prev q
        have hfq : f_new q = f_prev q := dif_pos hql'
        rw [hfq]
        exact hedge_prev a t q hedge hql'
      · -- q at level n + 1: f_new q = witness q hqpl
        have hqpl : q.pathLength = n + 1 := by omega
        have hfq : f_new q = witness q hqpl := by
          show (if h : q.pathLength ≤ n then _ else _) = _
          rw [dif_neg hql']
          exact dif_pos hqpl
        rw [hfq]
        exact witness_edge q hqpl a t hedge

/-- Backward direction: satisfaction of the characteristic formula at the root
    implies existence of an LTSHom from the tree to H sending root to w. -/
theorem characteristicHML_to_hom (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (H : FinLTS L) (w : H.Vertex)
    (hsat : (characteristicHML G v d (TreeVertex.rootPath G v d)).satisfies H w) :
    ∃ f : LTSHom (treeUnravelLTS G v d) H,
      f.toFun (TreeVertex.rootPath G v d) = w := by
  -- Use the construction at budget d (covers all vertices since pathLength ≤ d)
  obtain ⟨f, _, hroot, hedge⟩ := characteristicHML_backward_aux G v d H w hsat d
  exact ⟨⟨f, fun a t q he => hedge a t q he (treeUnravel_depth_bound G v d q)⟩, hroot⟩

/-!
## Part 8: Combined Characterization Theorem
-/

/-- **Characteristic Formula Theorem**: satisfaction of χ(T, root) at H, w
    is equivalent to the existence of a label-preserving homomorphism from
    the tree to H sending the root to w.

    This is the fundamental connection between characteristic formulas and
    tree homomorphisms that underlies the Hennessy-Milner theorem. -/
theorem characteristicHML_iff (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (H : FinLTS L) (w : H.Vertex) :
    (characteristicHML G v d (TreeVertex.rootPath G v d)).satisfies H w ↔
    ∃ f : LTSHom (treeUnravelLTS G v d) H,
      f.toFun (TreeVertex.rootPath G v d) = w :=
  ⟨characteristicHML_to_hom G v d H w,
   fun ⟨f, hf⟩ => hf ▸ characteristicHML_of_hom G v d H f (TreeVertex.rootPath G v d)⟩

end RTS.PresheafTopos
