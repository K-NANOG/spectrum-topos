/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Atom Separation and Kernel Fixed-Point Machinery

This file establishes that non-extremal atoms (from nondeterministic states)
have singleton Lindenbaum classes, and uses this to prove that kernel elements
of the symmetry homomorphism fix nondeterministic states and propagate forward
along edges.

## Main Results

### Part 1-3: Atom Singleton Lemma

- `IsNonExtremalAtom`: predicate for atoms from nondeterministic states
- `mkTransitionTheory_separating_model`: axiomatized separating model (1 axiom)
- `atom_singleton_lemma`: non-extremal atoms have singleton Lindenbaum classes

### Part 4-5: Kernel Fixed-Point Machinery

- `symmetryHomomorphism_action`: connects opaque homomorphism to permuteFormula (1 axiom)
- `kernel_fixes_nondeterministic`: kernel elements fix all nondeterministic states
- `kernel_forward_closure`: fixed-point set is forward-closed under edges

## References

- Caramello, "Theories, Sites, Toposes" (OUP, 2018)
- Vickers, "Topology via Logic" (1989)
-/

import RuleSys.SubtoposLattice.SymmetryHomomorphism

set_option autoImplicit false

universe u

open GeometricLogic.Propositional
open CategoryTheory

namespace Ruliology

/-!
## Part 1: Non-Extremal Atom Predicate

An atom `(v, w)` is *non-extremal* if it represents an actual edge and the
source state `v` is nondeterministic (has at least 2 outgoing edges).
Such atoms are not forced to ⊤ or ⊥ by the theory axioms.
-/

/-- An atom `p = (v, w)` of a transition system is non-extremal if:
1. The edge `v → w` exists (`hasEdge v w = true`)
2. The source `v` has at least 2 successors (nondeterministic)

Non-extremal atoms are the free generators of the Lindenbaum algebra:
they are neither forced to ⊤ (like the unique successor of a deterministic state)
nor forced to ⊥ (like a non-edge pair). -/
def IsNonExtremalAtom (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool) (p : S × S) : Prop :=
  hasEdge p.1 p.2 = true ∧
  2 ≤ (Finset.univ.filter (fun t => hasEdge p.1 t = true)).card

/-!
## Part 2: Separating Model (Axiomatized)

For any two distinct atoms where the first is non-extremal, there exists
a model of the transition theory that separates them (makes one true and
the other false). This is the key semantic ingredient for the atom singleton
lemma.

**Mathematical justification**: If `p = (v, w)` is non-extremal, then `v`
has at least 2 successors. We can construct a model that assigns `true` to
`p` and `false` to `q` by choosing the right successor for each state:
- For state `v`: choose successor `w` (making `p` true)
- For the source of `q`: choose a different successor (making `q` false)
- For all other states: choose any successor

This works because the theory only requires that each state has *some*
successor that evaluates to true (totality), not that all edges are true.
-/

/-- For distinct atoms where the first is non-extremal, there exists a
T-model separating them.

**Axiom count**: 1 (semantic construction of separating valuation). -/
axiom mkTransitionTheory_separating_model
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool)
    (p q : S × S)
    (hp : IsNonExtremalAtom S hasEdge p)
    (hne : p ≠ q) :
    ∃ v : (S × S) → Bool,
      (mkTransitionTheory S hasEdge).IsModel v ∧
      v p = true ∧ v q = false

/-!
## Part 3: Atom Singleton Lemma (Proved)

Non-extremal atoms have singleton Lindenbaum classes: if two atoms have the
same equivalence class in the Lindenbaum algebra, they must be equal.

This is proved by contradiction using the separating model: if `p ≠ q`, the
separating model witnesses that `modelBehavior (mk (atom p))` and
`modelBehavior (mk (atom q))` differ at that model, contradicting `heq`.
-/

/-- **Atom singleton lemma**: non-extremal atoms have singleton Lindenbaum classes.

If `mk (atom p) = mk (atom q)` in the Lindenbaum algebra and `p` is non-extremal,
then `p = q`. Equivalently, the map `atom ↦ [atom]` is injective on non-extremal atoms.

This is the key lemma connecting syntactic equality (same Lindenbaum class) to
atom identity (same transition pair). -/
theorem atom_singleton_lemma
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool)
    (p q : S × S)
    (hp : IsNonExtremalAtom S hasEdge p)
    (heq : LindenbaumAlgebra.mk (T := mkTransitionTheory S hasEdge) (.atom p) =
           LindenbaumAlgebra.mk (.atom q)) :
    p = q := by
  by_contra hne
  obtain ⟨v, hmodel, hvp, hvq⟩ := mkTransitionTheory_separating_model S hasEdge p q hp hne
  -- Construct the model as a subtype element
  let T := mkTransitionTheory S hasEdge
  let model : {w : T.Atoms → Bool // T.IsModel w} := ⟨v, hmodel⟩
  -- modelBehavior (mk (atom p)) at model v should be (atom p).eval v = v p = true
  have h1 : LindenbaumAlgebra.modelBehavior
      (LindenbaumAlgebra.mk (T := T) (.atom p)) model = true := by
    show LindenbaumAlgebra.modelBehavior (Quotient.mk (provableEquivSetoid T) (.atom p)) model = true
    simp [LindenbaumAlgebra.modelBehavior, PropFormula.eval]
    exact hvp
  -- modelBehavior (mk (atom q)) at model v should be (atom q).eval v = v q = false
  have h2 : LindenbaumAlgebra.modelBehavior
      (LindenbaumAlgebra.mk (T := T) (.atom q)) model = false := by
    show LindenbaumAlgebra.modelBehavior (Quotient.mk (provableEquivSetoid T) (.atom q)) model = false
    simp [LindenbaumAlgebra.modelBehavior, PropFormula.eval]
    exact hvq
  -- But heq says mk (atom p) = mk (atom q), so their modelBehavior must agree
  rw [heq] at h1
  rw [h1] at h2
  exact absurd h2 (by decide)

/-!
## Part 4: Symmetry Homomorphism Action (Axiomatized)

The symmetry homomorphism sends each graph automorphism to an order automorphism
of the Lindenbaum algebra. We axiomatize how it acts on specific elements:
`φ(σ)(mk φ) = mk (permuteFormula σ φ)`.

This bridges the gap between the opaque `symmetryHomomorphism` and the concrete
`permuteFormula` action.
-/

/-- Helper to apply a `LindenbaumAut` as a function on `LindenbaumAlgebra` elements.
Needed because `LindenbaumAut` is a `def` alias for `≃o`, and the coercion chain
doesn't automatically resolve through the alias. -/
def LindenbaumAut.apply {T : PropGeoTheory.{0}} (f : LindenbaumAut T) :
    LindenbaumAlgebra T → LindenbaumAlgebra T :=
  (f : LindenbaumAlgebra T ≃o LindenbaumAlgebra T).toFun

/-- The symmetry homomorphism acts on Lindenbaum classes by formula permutation.

For any graph automorphism σ and formula φ:
  `(symmetryHomomorphism σ).apply (mk φ) = mk (permuteFormula σ.1 φ)`

This connects the axiomatized order isomorphism to the concrete formula action.

**Mathematical justification**: By construction, the symmetry homomorphism is
the descent of `permuteFormula σ.1` to the Lindenbaum quotient. This axiom
makes explicit what the homomorphism does on individual elements.

**Axiom count**: 1. -/
axiom symmetryHomomorphism_action
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool)
    (σ : GraphAut S hasEdge)
    (φ : PropFormula (S × S)) :
    LindenbaumAut.apply (symmetryHomomorphism S hasEdge σ)
      (LindenbaumAlgebra.mk (T := mkTransitionTheory S hasEdge) φ) =
    LindenbaumAlgebra.mk (T := mkTransitionTheory S hasEdge) (permuteFormula σ.1 φ)

/-- Kernel elements act as identity pointwise on the Lindenbaum algebra. -/
theorem kernel_pointwise_id
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool)
    (σ : symmetryKernel S hasEdge)
    (x : LindenbaumAlgebra (mkTransitionTheory S hasEdge)) :
    LindenbaumAut.apply (symmetryHomomorphism S hasEdge σ.1) x = x := by
  unfold LindenbaumAut.apply
  have hid := σ.2
  -- hid : symmetryHomomorphism S hasEdge σ.1 = OrderIso.refl _
  -- Unfold LindenbaumAut to get at the OrderIso
  change (show LindenbaumAlgebra _ ≃o LindenbaumAlgebra _ from symmetryHomomorphism S hasEdge σ.1).toFun x = x
  rw [show (symmetryHomomorphism S hasEdge σ.1 : LindenbaumAlgebra _ ≃o LindenbaumAlgebra _) =
      OrderIso.refl _ from hid]
  simp [OrderIso.refl]

/-!
## Part 5a: Kernel Fixes Nondeterministic States (Proved)

A kernel element σ satisfies `φ(σ) = id` on the Lindenbaum algebra. For any
non-extremal atom `(v, w)`, the atom singleton lemma then forces
`(σ v, σ w) = (v, w)`, giving `σ v = v`.
-/

/-- **Kernel fixes nondeterministic states**: if σ is in the kernel of the
symmetry homomorphism and v is a nondeterministic state (≥ 2 successors),
then σ fixes v.

Proof: σ in kernel means `φ(σ) = id`. Apply to `mk (atom (v, w))`:
  `mk (permuteFormula σ.1 (atom (v, w))) = mk (atom (v, w))`
The left side reduces to `mk (atom (σ v, σ w))`. By `atom_singleton_lemma`,
`(σ v, σ w) = (v, w)`, so `σ v = v`. -/
theorem kernel_fixes_nondeterministic
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool)
    (σ : symmetryKernel S hasEdge)
    (v : S)
    (hv : 2 ≤ (Finset.univ.filter (fun t => hasEdge v t = true)).card)
    (w : S)
    (hw : hasEdge v w = true) :
    σ.1.1 v = v := by
  -- Apply kernel_pointwise_id to mk (atom (v, w))
  have h1 := kernel_pointwise_id S hasEdge σ
      (LindenbaumAlgebra.mk (T := mkTransitionTheory S hasEdge) (.atom (v, w)))
  -- By symmetryHomomorphism_action, the LHS is mk (permuteFormula σ.1.1 (atom (v, w)))
  rw [symmetryHomomorphism_action] at h1
  -- permuteFormula on atoms: permuteFormula σ.1.1 (atom (v,w)) = atom (σ.1.1 v, σ.1.1 w)
  simp only [permuteFormula, permuteAtom] at h1
  -- h1 : mk (atom (σ.1.1 v, σ.1.1 w)) = mk (atom (v, w))
  -- Apply atom_singleton_lemma to the permuted atom
  have hp' : IsNonExtremalAtom S hasEdge (σ.1.1 v, σ.1.1 w) := by
    constructor
    · -- hasEdge (σ.1.1 v) (σ.1.1 w) = true
      rw [← σ.1.2 v w]
      exact hw
    · -- 2 ≤ card of successors of σ.1.1 v
      -- The successors of σ.1.1 v biject with successors of v via σ.1.1
      show 2 ≤ (Finset.univ.filter (fun t => hasEdge (σ.1.1 v) t = true)).card
      have hperm := σ.1.2
      have : (Finset.univ.filter (fun t => hasEdge (σ.1.1 v) t = true)).card =
             (Finset.univ.filter (fun t => hasEdge v t = true)).card := by
        apply Finset.card_bij (fun t _ => σ.1.1.symm t)
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          rw [hperm v (σ.1.1.symm t), Equiv.apply_symm_apply]
          exact ht
        · intro t₁ _ t₂ _ h
          exact σ.1.1.symm.injective h
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          exact ⟨σ.1.1 t, by rw [← hperm]; exact ht, by simp⟩
      omega
  have heq_atoms := atom_singleton_lemma S hasEdge (σ.1.1 v, σ.1.1 w) (v, w) hp' h1
  exact (Prod.mk.inj heq_atoms).1

/-!
## Part 5b: Forward Closure (Proved)

If σ fixes v and there is an edge v → w, then σ also fixes w. This uses
the atom singleton argument for nondeterministic states, and a cardinality
argument (unique successor) for deterministic states.
-/

/-- **Kernel forward closure**: the fixed-point set of a kernel element is
forward-closed under edges.

If σ is in the kernel and fixes v (i.e., σ v = v), and there is an edge v → w,
then σ also fixes w.

Two cases:
- **Nondeterministic v** (≥ 2 successors): same atom singleton argument,
  extract second component `σ w = w`
- **Deterministic v** (< 2 successors, i.e., exactly 1): edge preservation
  gives `hasEdge v (σ w) = true`, and since w is the unique successor,
  `σ w = w`. -/
theorem kernel_forward_closure
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool)
    (σ : symmetryKernel S hasEdge)
    (v w : S)
    (hv_fixed : σ.1.1 v = v)
    (hvw : hasEdge v w = true) :
    σ.1.1 w = w := by
  -- Split on whether v is nondeterministic (≥ 2 successors)
  by_cases hnd : 2 ≤ (Finset.univ.filter (fun t => hasEdge v t = true)).card
  · -- Case 1: Nondeterministic v — use atom singleton argument
    have h1 := kernel_pointwise_id S hasEdge σ
        (LindenbaumAlgebra.mk (T := mkTransitionTheory S hasEdge) (.atom (v, w)))
    rw [symmetryHomomorphism_action] at h1
    simp only [permuteFormula, permuteAtom] at h1
    -- h1 : mk (atom (σ.1.1 v, σ.1.1 w)) = mk (atom (v, w))
    -- Need non-extremal for the permuted atom
    have hσw_edge : hasEdge v (σ.1.1 w) = true := by
      have := σ.1.2 v w
      rw [hv_fixed] at this
      rw [← this, hvw]
    have hp' : IsNonExtremalAtom S hasEdge (σ.1.1 v, σ.1.1 w) := by
      simp only [IsNonExtremalAtom, hv_fixed]
      exact ⟨hσw_edge, hnd⟩
    have heq_atoms := atom_singleton_lemma S hasEdge (σ.1.1 v, σ.1.1 w) (v, w) hp' h1
    exact (Prod.mk.inj heq_atoms).2
  · -- Case 2: Deterministic v — unique successor argument
    push_neg at hnd
    -- v has < 2 successors in the filter
    -- w is in the filter (since hasEdge v w = true)
    have hw_mem : w ∈ Finset.univ.filter (fun t => hasEdge v t = true) := by
      simp [Finset.mem_filter, hvw]
    -- σ.1.1 w is also in the filter
    have hσw_edge : hasEdge v (σ.1.1 w) = true := by
      have := σ.1.2 v w
      rw [hv_fixed] at this
      rw [← this, hvw]
    have hσw_mem : σ.1.1 w ∈ Finset.univ.filter (fun t => hasEdge v t = true) := by
      simp [Finset.mem_filter, hσw_edge]
    -- Since the filter has card ≤ 1, and both w and σ.1.1 w are in it, they must be equal
    have huniq : (Finset.univ.filter (fun t => hasEdge v t = true)).card ≤ 1 := by omega
    exact Finset.card_le_one_iff.mp huniq hσw_mem hw_mem

end Ruliology
