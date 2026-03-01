/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric Tree Decomposition via Characteristic Formulas

On any tree unraveling, every geometric formula (at the root) is equivalent to an
HML formula of depth <= d. The construction uses characteristic formulas: the
decomposition formula is chi(T, root) when phi holds at the root, and bot otherwise.

## Key Results

- `disjAll`: n-ary disjunction for LabeledHML
- `characteristicHML_self_satisfies`: chi(t) is satisfied at t (via identity hom)
- `characteristicHML_root_hom_transfer`: transfer from chi(root) satisfaction to phi
- `geo_tree_decomposition`: the main decomposition theorem

## References

- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
- van Glabbeek, "The linear time--branching time spectrum I" (1990)
-/

import RuleSys.PresheafTopos.CharacteristicFormula

set_option autoImplicit false

namespace Ruliology.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: n-ary Disjunction via List folding
-/

/-- Fold a list of formulas into a disjunction, with bot as base. -/
def disjAll : List (LabeledHML L) -> LabeledHML L
  | [] => .bot
  | phi :: rest => .disj phi (disjAll rest)

/-- Satisfaction of disjAll: some formula in the list is satisfied. -/
theorem disjAll_satisfies (G : FinLTS L) (v : G.Vertex)
    (phis : List (LabeledHML L)) :
    (disjAll phis).satisfies G v ↔ ∃ phi, phi ∈ phis ∧ phi.satisfies G v := by
  induction phis with
  | nil =>
    simp [disjAll, LabeledHML.satisfies]
  | cons phi rest ih =>
    simp only [disjAll, LabeledHML.satisfies, List.mem_cons]
    constructor
    . rintro (hphi | hrest)
      . exact ⟨phi, Or.inl rfl, hphi⟩
      . obtain ⟨chi, hchi_mem, hchi_sat⟩ := ih.mp hrest
        exact ⟨chi, Or.inr hchi_mem, hchi_sat⟩
    . rintro ⟨chi, rfl | hchi_mem, hchi_sat⟩
      . exact Or.inl hchi_sat
      . exact Or.inr (ih.mpr ⟨chi, hchi_mem, hchi_sat⟩)

omit [Fintype L] [DecidableEq L] in
/-- Depth of disjAll: bounded by max depth of elements. -/
theorem disjAll_depth_le (phis : List (LabeledHML L)) (bound : Nat)
    (h : ∀ phi, phi ∈ phis → phi.depth ≤ bound) :
    (disjAll phis).depth <= bound := by
  induction phis with
  | nil =>
    simp [disjAll, LabeledHML.depth]
  | cons phi rest ih =>
    simp only [disjAll, LabeledHML.depth]
    apply Nat.max_le.mpr
    constructor
    . exact h phi List.mem_cons_self
    . exact ih fun chi hchi => h chi (List.mem_cons_of_mem phi hchi)

/-!
## Part 2: Characteristic Formula Self-Satisfaction
-/

/-- The characteristic formula of any tree vertex t is satisfied at t itself.
    Proof: apply `characteristicHML_of_hom` with the identity homomorphism,
    noting that `LTSHom.id.toFun t = t`. -/
theorem characteristicHML_self_satisfies (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex) :
    (characteristicHML G v d t).satisfies (treeUnravelLTS G v d) t := by
  have := characteristicHML_of_hom G v d (treeUnravelLTS G v d)
    (LTSHom.id (treeUnravelLTS G v d)) t
  simp [LTSHom.id] at this
  exact this

/-- Transfer via root characteristic formula: if chi(root) is satisfied at some
    vertex w in H, and phi is satisfied at the tree root, then phi is satisfied
    at w in H.

    Proof: characteristicHML_iff gives a homomorphism f : T -> H with f(root) = w.
    Then LTSGeoFormula.preserved_by_hom transfers phi from T to H. -/
theorem characteristicHML_root_hom_transfer (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (H : FinLTS L) (w : H.Vertex) (φ : LTSGeoFormula L 1)
    (hchi : (characteristicHML G v d (TreeVertex.rootPath G v d)).satisfies H w)
    (hphi : φ.satisfies (treeUnravelLTS G v d)
              (fun _ => TreeVertex.rootPath G v d)) :
    φ.satisfies H (fun _ => w) := by
  -- Extract the homomorphism from characteristicHML_iff
  obtain ⟨f, hf⟩ := (characteristicHML_iff G v d H w).mp hchi
  -- Transfer phi via this homomorphism
  have htrans := LTSGeoFormula.preserved_by_hom f
    (fun _ => TreeVertex.rootPath G v d) φ hphi
  -- f.toFun ∘ (fun _ => root) = fun _ => f.toFun root = fun _ => w
  have heq : f.toFun ∘ (fun _ : Fin 1 => TreeVertex.rootPath G v d) =
      fun _ => f.toFun (TreeVertex.rootPath G v d) := by ext; simp
  rw [heq, hf] at htrans
  exact htrans

/-!
## Part 3: Geo-Tree Decomposition
-/

/-- The decomposition formula is equivalent to phi at the root of the tree,
    and universally implies phi at any LTS. This is the combined statement. -/
theorem geo_tree_decomposition_aux (φ : LTSGeoFormula L 1)
    (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    ∃ ψ : LabeledHML L, ψ.depth ≤ d ∧
      (φ.satisfies (treeUnravelLTS G v d)
         (fun _ => TreeVertex.rootPath G v d) ↔
       ψ.satisfies (treeUnravelLTS G v d) (TreeVertex.rootPath G v d)) ∧
      (∀ (H : FinLTS L) (w : H.Vertex),
         ψ.satisfies H w →
         φ.satisfies H (fun _ => w)) := by
  -- Case split on whether phi holds at the root
  by_cases hsat : φ.satisfies (treeUnravelLTS G v d)
      (fun _ => TreeVertex.rootPath G v d)
  · -- phi holds: use chi(root) as the decomposition formula
    refine ⟨characteristicHML G v d (TreeVertex.rootPath G v d), ?_, ?_, ?_⟩
    · -- Depth bound: characteristicHML at root has depth ≤ d
      have h := characteristicHML_depth_le G v d (TreeVertex.rootPath G v d)
      simp [TreeVertex.rootPath, TreeVertex.pathLength] at h
      exact h
    · -- Root equivalence
      constructor
      · intro _
        exact characteristicHML_self_satisfies G v d (TreeVertex.rootPath G v d)
      · intro hchi
        exact hsat
    · -- Universal transfer: chi(root).satisfies H w → phi.satisfies H (fun _ => w)
      intro H w hchi
      exact characteristicHML_root_hom_transfer G v d H w φ hchi hsat
  · -- phi does not hold: use bot as the decomposition formula
    refine ⟨LabeledHML.bot, ?_, ?_, ?_⟩
    · -- Depth bound: bot has depth 0 ≤ d
      simp [LabeledHML.depth]
    · -- Root equivalence: phi ↔ bot (both false)
      constructor
      · intro h; exact absurd h hsat
      · intro h; exact h.elim
    · -- Universal transfer: bot.satisfies H w → phi (vacuous)
      intro H w h
      exact h.elim

/-- **Geometric Tree Decomposition Theorem**: for any geometric formula phi and
    tree unraveling T = treeUnravelLTS G v d, there exists an HML formula psi with:
    1. psi.depth <= d
    2. phi iff psi at the root of T
    3. psi.satisfies H w implies phi.satisfies H (fun _ => w) for all H, w

    This is the root-only decomposition (Option B): equivalence holds at the root,
    and the universal transfer property holds everywhere. No bisim-invariance or
    existDepth hypotheses are needed. -/
theorem geo_tree_decomposition (φ : LTSGeoFormula L 1)
    (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    ∃ ψ : LabeledHML L, ψ.depth ≤ d ∧
      (φ.satisfies (treeUnravelLTS G v d)
         (fun _ => TreeVertex.rootPath G v d) ↔
       ψ.satisfies (treeUnravelLTS G v d) (TreeVertex.rootPath G v d)) ∧
      (∀ (H : FinLTS L) (w : H.Vertex),
         ψ.satisfies H w →
         φ.satisfies H (fun _ => w)) :=
  geo_tree_decomposition_aux φ G v d

end Ruliology.PresheafTopos
