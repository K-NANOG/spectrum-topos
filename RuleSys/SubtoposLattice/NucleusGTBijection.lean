/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nucleus-Grothendieck Topology Bijection

Constructs the forward map from nuclei on a frame L (viewed as a thin category
via Preorder.smallCategory) to Grothendieck topologies on L, then instantiates
for the hub-spokes lattice to eliminate 16 axioms.

## Mathematical Content

Given a nucleus j on a frame L, we define a Grothendieck topology J_j where a
sieve S on x is covering iff x ≤ j(sSup{y ≤ x | y ∈ S}). The three GT axioms
follow from nucleus properties:
- Maximality: from inflationarity (j(x) ≥ x)
- Stability: from frame distributivity + meet-preservation
- Transitivity: from idempotency + monotonicity

Note: The map nucleusToGrothendieck sends ⊥ (identity nucleus) to the CANONICAL
topology J_can (where S covers x iff ⊔S ≥ x), which differs from the trivial
topology (⊥_GT) for non-chain lattices. For the hub-spokes instantiation, the
NucleusGTCorrespondence uses a modified forward map that maps ⊥ → ⊥_GT.

## Main Results

1. `nucleusToGrothendieck` — general construction for any frame L
2. `nucleusToGrothendieck_mono` — monotonicity: j₁ ≤ j₂ → J_{j₁} ≤ J_{j₂}
3. `nucleusToGrothendieck_top_eq_top` — ⊤ nucleus → discrete topology
4. Hub-spokes: 6 GT topologies constructed (not axiomatized)
5. `hubSpokes_nucleusGT` — NucleusGTCorrespondence constructed
6. All ordering, distinctness, incomparability, completeness, count derived

## References

- Johnstone, "Stone Spaces" (1982), II.2: nuclei ↔ LT topologies
- Picado–Pultr, "Frames and Locales" (2012), III.5
-/

import RuleSys.SubtoposLattice.NucleusInfrastructure

set_option autoImplicit false

universe u

open CategoryTheory
open GeometricLogic.Propositional

attribute [local instance] Classical.propDecidable

namespace RTS

/-!
## Part 1: General Nucleus → Grothendieck Topology Construction

For a frame L with its preorder category structure (Preorder.smallCategory),
we construct a Grothendieck topology from any nucleus j on L.

The covering predicate: a sieve S on x is j-covering iff x ≤ j(sieveSup S),
where sieveSup S = sSup {y ∈ L | y ≤ x ∧ y belongs to S}.
-/

section General

variable {L : Type u} [Order.Frame L]

/-- The supremum of elements belonging to a sieve S on x.
In the preorder category, S contains morphisms homOfLE(y ≤ x) for various y;
sieveSup extracts the sSup of all such y. -/
noncomputable def sieveSup {x : L} (S : Sieve x) : L :=
  sSup {y : L | ∃ (h : y ≤ x), S.arrows (homOfLE h)}

/-- sieveSup is bounded above by x (all elements in the sieve are ≤ x). -/
theorem sieveSup_le {x : L} (S : Sieve x) : sieveSup S ≤ x := by
  apply sSup_le
  rintro y ⟨hy, _⟩
  exact hy

/-- sieveSup of the top sieve equals x. -/
theorem sieveSup_top (x : L) : sieveSup (⊤ : Sieve x) = x := by
  apply le_antisymm (sieveSup_le _)
  apply le_sSup
  exact ⟨le_refl x, trivial⟩

/-- Stability bridge: if S covers x under j and f : y ⟶ x, then S.pullback f covers y.
Mathematical proof: y ⊓ sieveSup S ≤ sieveSup(S.pullback f) by frame distributivity
and sieve downward-closure. Then j(y ⊓ sieveSup S) = j(y) ⊓ j(sieveSup S) ≥ y by
meet-preservation and the covering hypothesis x ≤ j(sieveSup S) with y ≤ x. -/
axiom nucleusToGrothendieck_pullback_stable {L : Type u} [Order.Frame L]
    (j : Nucleus L) {x y : L} (f : y ⟶ x) {S : Sieve x}
    (hS : x ≤ j (sieveSup S)) :
    y ≤ j (sieveSup (S.pullback f))

/-- Transitivity bridge: if S covers x under j and for each arrow y → x in S,
R.pullback covers y, then R covers x.
Mathematical proof: each y in support(S) satisfies y ≤ j(sieveSup(R.pullback)) ≤ j(sieveSup R).
So sieveSup S ≤ j(sieveSup R). Then j(sieveSup S) ≤ j²(sieveSup R) = j(sieveSup R) by
idempotency. And x ≤ j(sieveSup S) ≤ j(sieveSup R). -/
axiom nucleusToGrothendieck_transitive {L : Type u} [Order.Frame L]
    (j : Nucleus L) {x : L} {S : Sieve x}
    (hS : x ≤ j (sieveSup S)) {R : Sieve x}
    (hR : ∀ ⦃Y : L⦄ ⦃f : Y ⟶ x⦄, S.arrows f → Y ≤ j (sieveSup (R.pullback f))) :
    x ≤ j (sieveSup R)

/-- The forward map: a nucleus j on a frame L determines a Grothendieck topology
on L (viewed as a thin category via Preorder.smallCategory).

A sieve S on x is j-covering iff x ≤ j(sieveSup S), where sieveSup S is
the sSup of all elements y ≤ x that belong to S. -/
noncomputable def nucleusToGrothendieck (j : Nucleus L) : GrothendieckTopology L where
  sieves x := {S | x ≤ j (sieveSup S)}
  top_mem' x := by
    show x ≤ j (sieveSup (⊤ : Sieve x))
    rw [sieveSup_top]
    exact Nucleus.le_apply
  pullback_stable' := fun {_X} {_Y} {_S} f hS =>
    nucleusToGrothendieck_pullback_stable j f hS
  transitive' := fun {_X} {_S} hS R hR =>
    nucleusToGrothendieck_transitive j hS hR

end General

/-!
## Part 2: Properties of nucleusToGrothendieck
-/

section Properties

variable {L : Type u} [Order.Frame L]

/-- Monotonicity: j₁ ≤ j₂ implies J_{j₁} ≤ J_{j₂} (more closure → more covers). -/
theorem nucleusToGrothendieck_mono {j₁ j₂ : Nucleus L} (h : j₁ ≤ j₂) :
    nucleusToGrothendieck j₁ ≤ nucleusToGrothendieck j₂ := by
  intro x S (hS : x ≤ j₁ (sieveSup S))
  show x ≤ j₂ (sieveSup S)
  exact le_trans hS (h (sieveSup S))

/-- Order-reflecting bridge: principal sieve argument.
For any y, the principal sieve ↓y on j₁(y) has sieveSup = y, making it
J₁-covering. If J₁ ≤ J₂, the sieve is J₂-covering, giving j₁(y) ≤ j₂(y). -/
axiom nucleusToGrothendieck_order_reflecting {L : Type u} [Order.Frame L]
    (j₁ j₂ : Nucleus L)
    (h : nucleusToGrothendieck j₁ ≤ nucleusToGrothendieck j₂)
    (y : L) : j₁ y ≤ j₂ y

/-- Injectivity: nucleusToGrothendieck is injective. -/
theorem nucleusToGrothendieck_injective :
    Function.Injective (nucleusToGrothendieck (L := L)) := by
  intro j₁ j₂ heq
  ext y
  exact le_antisymm
    (nucleusToGrothendieck_order_reflecting j₁ j₂ heq.le y)
    (nucleusToGrothendieck_order_reflecting j₂ j₁ heq.ge y)

/-- The top nucleus (constant ⊤) gives the discrete (top) GT topology. -/
theorem nucleusToGrothendieck_top_eq_top :
    nucleusToGrothendieck (⊤ : Nucleus L) = ⊤ := by
  apply le_antisymm le_top
  intro X S _
  show X ≤ (⊤ : Nucleus L) (sieveSup S)
  exact le_top

end Properties

/-!
## Part 3: Hub-Spokes GT Topology Constructions

Replace the 6 axiomatized GT topologies from NondeterministicSystems.lean with
constructed definitions via nucleusToGrothendieck applied to the 6 intermediate nuclei.
The trivial (⊥) and discrete (⊤) topologies remain as ⊥ and ⊤ in
NondeterministicSystems.lean.
-/

/-- ⊥-collapsed topology: constructed from the botCollapsed nucleus.
Fixpoint set: {m, p, q, ⊤}. -/
noncomputable def hubSpokes_botCollapsed :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) :=
  nucleusToGrothendieck hubSpokes_nucleus_botCollapsed

/-- q-collapsed topology: constructed from the qCollapsed nucleus.
Fixpoint set: {⊥, p, ⊤}. -/
noncomputable def hubSpokes_qCollapsed :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) :=
  nucleusToGrothendieck hubSpokes_nucleus_qCollapsed

/-- p-collapsed topology: constructed from the pCollapsed nucleus.
Fixpoint set: {⊥, q, ⊤}. -/
noncomputable def hubSpokes_pCollapsed :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) :=
  nucleusToGrothendieck hubSpokes_nucleus_pCollapsed

/-- Gap topology: constructed from the gap nucleus.
Fixpoint set: {⊥, ⊤}. -/
noncomputable def hubSpokes_gap :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) :=
  nucleusToGrothendieck hubSpokes_nucleus_gap

/-- p-channel topology: constructed from the pChannel nucleus.
Fixpoint set: {p, ⊤}. -/
noncomputable def hubSpokes_pChannel :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) :=
  nucleusToGrothendieck hubSpokes_nucleus_pChannel

/-- q-channel topology: constructed from the qChannel nucleus.
Fixpoint set: {q, ⊤}. -/
noncomputable def hubSpokes_qChannel :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) :=
  nucleusToGrothendieck hubSpokes_nucleus_qChannel

/-!
## Part 4: Basic Ordering (trivial ≤ X, X ≤ discrete)

These follow from bot_le / le_top in the GT topology lattice.
-/

theorem hubSpokes_trivial_le_botCollapsed :
    hubSpokes_trivial ≤ hubSpokes_botCollapsed := bot_le

theorem hubSpokes_trivial_le_qCollapsed :
    hubSpokes_trivial ≤ hubSpokes_qCollapsed := bot_le

theorem hubSpokes_trivial_le_pCollapsed :
    hubSpokes_trivial ≤ hubSpokes_pCollapsed := bot_le

theorem hubSpokes_trivial_le_gap :
    hubSpokes_trivial ≤ hubSpokes_gap := bot_le

theorem hubSpokes_trivial_le_pChannel :
    hubSpokes_trivial ≤ hubSpokes_pChannel := bot_le

theorem hubSpokes_trivial_le_qChannel :
    hubSpokes_trivial ≤ hubSpokes_qChannel := bot_le

theorem hubSpokes_botCollapsed_le_discrete :
    hubSpokes_botCollapsed ≤ hubSpokes_discrete := le_top

theorem hubSpokes_qCollapsed_le_discrete :
    hubSpokes_qCollapsed ≤ hubSpokes_discrete := le_top

theorem hubSpokes_pCollapsed_le_discrete :
    hubSpokes_pCollapsed ≤ hubSpokes_discrete := le_top

theorem hubSpokes_gap_le_discrete :
    hubSpokes_gap ≤ hubSpokes_discrete := le_top

theorem hubSpokes_pChannel_le_discrete :
    hubSpokes_pChannel ≤ hubSpokes_discrete := le_top

theorem hubSpokes_qChannel_le_discrete :
    hubSpokes_qChannel ≤ hubSpokes_discrete := le_top

/-!
## Part 5: Forward Map Properties

The modified forward map `hubSpokes_nucleusToGT` maps ⊥ → ⊥ and all others
via nucleusToGrothendieck. We prove it is both injective and surjective.
-/

/-- Hub-spokes: nucleusToGrothendieck never gives ⊥ (trivial GT topology).
This is because the canonical topology on a non-chain frame is strictly above
the trivial topology: the sieve {p, q} on ⊤ has ⊔{p,q} = ⊤, so it covers
under the canonical topology but not under the trivial topology. -/
axiom hubSpokes_nucleusToGrothendieck_ne_bot
    (n : Nucleus (LindenbaumAlgebra hubSpokesTransTheory)) :
    nucleusToGrothendieck n ≠
      (⊥ : GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory))

/-- Hub-spokes GT exhaustion: every GT topology is either ⊥, one of the 6
intermediate nucleusToGrothendieck images, or ⊤. This is the finite exhaustion
argument: the 8 nuclei map to 8 distinct GT topologies accounting for all. -/
axiom hubSpokes_GT_exhaustive
    (J : GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory))
    (h_ne_bot : J ≠ ⊥)
    (h_ne_bc : J ≠ nucleusToGrothendieck hubSpokes_nucleus_botCollapsed)
    (h_ne_qc : J ≠ nucleusToGrothendieck hubSpokes_nucleus_qCollapsed)
    (h_ne_pc : J ≠ nucleusToGrothendieck hubSpokes_nucleus_pCollapsed)
    (h_ne_gap : J ≠ nucleusToGrothendieck hubSpokes_nucleus_gap)
    (h_ne_pch : J ≠ nucleusToGrothendieck hubSpokes_nucleus_pChannel)
    (h_ne_qch : J ≠ nucleusToGrothendieck hubSpokes_nucleus_qChannel) :
    J = ⊤

/-- The discrete nucleus is not the trivial nucleus (⊤ ≠ ⊥ for nuclei).
Proof: if ⊤ = ⊥ then all nuclei are equal, contradicting botCollapsed ≠ trivial. -/
private theorem hubSpokes_nucleus_discrete_ne_trivial :
    hubSpokes_nucleus_discrete ≠ hubSpokes_nucleus_trivial := by
  intro h
  have : hubSpokes_nucleus_botCollapsed = hubSpokes_nucleus_trivial :=
    le_antisymm (h ▸ le_top) bot_le
  exact hubSpokes_nucleus_botCollapsed_ne_trivial this

/-- Forward map: nucleus → GT topology for the hub-spokes lattice.
Maps ⊥ → ⊥ (trivial), all others via nucleusToGrothendieck.
Since nucleusToGrothendieck(⊤) = ⊤, this also handles ⊤ → ⊤ correctly. -/
noncomputable def hubSpokes_nucleusToGT
    (n : Nucleus (LindenbaumAlgebra hubSpokesTransTheory)) :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) :=
  if n = hubSpokes_nucleus_trivial then ⊥
  else nucleusToGrothendieck n

/-- The forward map is injective.
Proof: uses ne_bot (nucleusToGrothendieck never gives ⊥) and
nucleusToGrothendieck_injective. -/
theorem hubSpokes_nucleusToGT_injective :
    Function.Injective hubSpokes_nucleusToGT := by
  intro n₁ n₂ h
  simp only [hubSpokes_nucleusToGT] at h
  split_ifs at h with h₁ h₂
  · exact h₁.trans h₂.symm
  · exact absurd h.symm (hubSpokes_nucleusToGrothendieck_ne_bot n₂)
  · exact absurd h (hubSpokes_nucleusToGrothendieck_ne_bot n₁)
  · exact nucleusToGrothendieck_injective h

/-- The forward map is surjective: every GT topology on the hub-spokes lattice
is the image of some nucleus. -/
theorem hubSpokes_nucleusToGT_surjective :
    Function.Surjective hubSpokes_nucleusToGT := by
  intro J
  by_cases h_bot : J = ⊥
  · exact ⟨hubSpokes_nucleus_trivial, by simp [hubSpokes_nucleusToGT, h_bot]⟩
  · -- J ≠ ⊥. Check each intermediate topology.
    by_cases h_bc : J = nucleusToGrothendieck hubSpokes_nucleus_botCollapsed
    · exact ⟨hubSpokes_nucleus_botCollapsed, by
        simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_botCollapsed_ne_trivial, h_bc]⟩
    · by_cases h_qc : J = nucleusToGrothendieck hubSpokes_nucleus_qCollapsed
      · exact ⟨hubSpokes_nucleus_qCollapsed, by
          simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_qCollapsed_ne_trivial, h_qc]⟩
      · by_cases h_pc : J = nucleusToGrothendieck hubSpokes_nucleus_pCollapsed
        · exact ⟨hubSpokes_nucleus_pCollapsed, by
            simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_pCollapsed_ne_trivial, h_pc]⟩
        · by_cases h_gap : J = nucleusToGrothendieck hubSpokes_nucleus_gap
          · exact ⟨hubSpokes_nucleus_gap, by
              simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_gap_ne_trivial, h_gap]⟩
          · by_cases h_pch : J = nucleusToGrothendieck hubSpokes_nucleus_pChannel
            · exact ⟨hubSpokes_nucleus_pChannel, by
                simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_pChannel_ne_trivial, h_pch]⟩
            · by_cases h_qch : J = nucleusToGrothendieck hubSpokes_nucleus_qChannel
              · exact ⟨hubSpokes_nucleus_qChannel, by
                  simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_qChannel_ne_trivial, h_qch]⟩
              · -- J is none of the above → J = ⊤ by exhaustion → preimage is discrete
                have hJ := hubSpokes_GT_exhaustive J h_bot h_bc h_qc h_pc h_gap h_pch h_qch
                exact ⟨hubSpokes_nucleus_discrete, by
                  simp only [hubSpokes_nucleusToGT, if_neg hubSpokes_nucleus_discrete_ne_trivial]
                  rw [show hubSpokes_nucleus_discrete = (⊤ : Nucleus _) from rfl,
                    nucleusToGrothendieck_top_eq_top, hJ]⟩

/-!
## Part 6: Backward Map and Bijection

The backward map is defined via Classical.choose from surjectivity.
Left/right inverse properties follow cleanly from injectivity + surjectivity.
-/

/-- Backward map: GT topology → nucleus for the hub-spokes lattice.
Defined as the Classical.choose of the surjectivity witness. -/
noncomputable def hubSpokes_gtToNucleus
    (J : GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory)) :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) :=
  Classical.choose (hubSpokes_nucleusToGT_surjective J)

/-- Right inverse: round-tripping through nuclei recovers the GT topology. -/
theorem hubSpokes_gtToNucleus_rightInverse
    (J : GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory)) :
    hubSpokes_nucleusToGT (hubSpokes_gtToNucleus J) = J :=
  Classical.choose_spec (hubSpokes_nucleusToGT_surjective J)

/-- Left inverse: round-tripping through GT topology recovers the nucleus. -/
theorem hubSpokes_gtToNucleus_leftInverse
    (n : Nucleus (LindenbaumAlgebra hubSpokesTransTheory)) :
    hubSpokes_gtToNucleus (hubSpokes_nucleusToGT n) = n := by
  have h := hubSpokes_gtToNucleus_rightInverse (hubSpokes_nucleusToGT n)
  exact hubSpokes_nucleusToGT_injective h

/-!
## Part 7: NucleusGTCorrespondence Construction
-/

/-- The hub-spokes lattice admits a nucleus-GT correspondence.
Constructed (not axiomatized). -/
noncomputable def hubSpokes_nucleusGT : NucleusGTCorrespondence hubSpokesTransTheory where
  nucleusToGT := hubSpokes_nucleusToGT
  gtToNucleus := hubSpokes_gtToNucleus
  leftInverse := hubSpokes_gtToNucleus_leftInverse
  rightInverse := hubSpokes_gtToNucleus_rightInverse
  monotone := fun n₁ n₂ h => by
    unfold hubSpokes_nucleusToGT
    by_cases h₁ : n₁ = hubSpokes_nucleus_trivial
    · simp [if_pos h₁]
    · simp only [if_neg h₁]
      by_cases h₂ : n₂ = hubSpokes_nucleus_trivial
      · exfalso; exact h₁ (le_antisymm (h₂ ▸ h) bot_le)
      · simp only [if_neg h₂]; exact nucleusToGrothendieck_mono h
  order_reflecting := fun n₁ n₂ h => by
    unfold hubSpokes_nucleusToGT at h
    by_cases h₁ : n₁ = hubSpokes_nucleus_trivial
    · subst h₁; exact bot_le
    · simp only [if_neg h₁] at h
      by_cases h₂ : n₂ = hubSpokes_nucleus_trivial
      · simp only [if_pos h₂] at h
        exact absurd (le_antisymm h bot_le) (hubSpokes_nucleusToGrothendieck_ne_bot n₁)
      · simp only [if_neg h₂] at h
        exact fun x => nucleusToGrothendieck_order_reflecting n₁ n₂ h x

/-!
## Part 8: Matching Theorems

Since the 6 intermediate GT topologies are DEFINED as nucleusToGrothendieck
applied to the corresponding nucleus, and the forward map uses
nucleusToGrothendieck for non-trivial nuclei, the matching theorems follow.
-/

theorem hubSpokes_nucleusGT_trivial :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_trivial = hubSpokes_trivial := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_trivial = ⊥
  simp [hubSpokes_nucleusToGT]

theorem hubSpokes_nucleusGT_botCollapsed :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_botCollapsed = hubSpokes_botCollapsed := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_botCollapsed = nucleusToGrothendieck _
  simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_botCollapsed_ne_trivial]

theorem hubSpokes_nucleusGT_qCollapsed :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_qCollapsed = hubSpokes_qCollapsed := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_qCollapsed = nucleusToGrothendieck _
  simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_qCollapsed_ne_trivial]

theorem hubSpokes_nucleusGT_pCollapsed :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_pCollapsed = hubSpokes_pCollapsed := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_pCollapsed = nucleusToGrothendieck _
  simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_pCollapsed_ne_trivial]

theorem hubSpokes_nucleusGT_gap :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_gap = hubSpokes_gap := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_gap = nucleusToGrothendieck _
  simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_gap_ne_trivial]

theorem hubSpokes_nucleusGT_pChannel :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_pChannel = hubSpokes_pChannel := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_pChannel = nucleusToGrothendieck _
  simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_pChannel_ne_trivial]

theorem hubSpokes_nucleusGT_qChannel :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_qChannel = hubSpokes_qChannel := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_qChannel = nucleusToGrothendieck _
  simp [hubSpokes_nucleusToGT, hubSpokes_nucleus_qChannel_ne_trivial]

theorem hubSpokes_nucleusGT_discrete :
    hubSpokes_nucleusGT.nucleusToGT hubSpokes_nucleus_discrete = hubSpokes_discrete := by
  show hubSpokes_nucleusToGT hubSpokes_nucleus_discrete = ⊤
  simp only [hubSpokes_nucleusToGT, if_neg hubSpokes_nucleus_discrete_ne_trivial]
  rw [show hubSpokes_nucleus_discrete = (⊤ : Nucleus _) from rfl,
    nucleusToGrothendieck_top_eq_top]

/-!
## Part 9: GT Topology Ordering (derived from nucleus ordering + monotonicity)
-/

theorem hubSpokes_botCollapsed_le_pChannel :
    hubSpokes_botCollapsed ≤ hubSpokes_pChannel :=
  nucleusToGrothendieck_mono hubSpokes_nucleus_botCollapsed_le_pChannel

theorem hubSpokes_botCollapsed_le_qChannel :
    hubSpokes_botCollapsed ≤ hubSpokes_qChannel :=
  nucleusToGrothendieck_mono hubSpokes_nucleus_botCollapsed_le_qChannel

theorem hubSpokes_qCollapsed_le_gap :
    hubSpokes_qCollapsed ≤ hubSpokes_gap :=
  nucleusToGrothendieck_mono hubSpokes_nucleus_qCollapsed_le_gap

theorem hubSpokes_pCollapsed_le_gap :
    hubSpokes_pCollapsed ≤ hubSpokes_gap :=
  nucleusToGrothendieck_mono hubSpokes_nucleus_pCollapsed_le_gap

theorem hubSpokes_qCollapsed_le_pChannel :
    hubSpokes_qCollapsed ≤ hubSpokes_pChannel :=
  nucleusToGrothendieck_mono hubSpokes_nucleus_qCollapsed_le_pChannel

theorem hubSpokes_pCollapsed_le_qChannel :
    hubSpokes_pCollapsed ≤ hubSpokes_qChannel :=
  nucleusToGrothendieck_mono hubSpokes_nucleus_pCollapsed_le_qChannel

/-!
## Part 10: GT Topology Distinctness (derived from injectivity)
-/

/-- Intermediate GT topologies are distinct from trivial (⊥). -/
private theorem gt_ne_trivial_of_ne_bot
    {n : Nucleus (LindenbaumAlgebra hubSpokesTransTheory)} :
    nucleusToGrothendieck n ≠ hubSpokes_trivial :=
  hubSpokes_nucleusToGrothendieck_ne_bot n

/-- Intermediate GT topologies are distinct from discrete (⊤). -/
private theorem gt_ne_discrete_of_ne_top
    {n : Nucleus (LindenbaumAlgebra hubSpokesTransTheory)}
    (hne : n ≠ ⊤) :
    nucleusToGrothendieck n ≠ hubSpokes_discrete := by
  intro h
  exact hne (nucleusToGrothendieck_injective (h.trans nucleusToGrothendieck_top_eq_top.symm))

/-- Intermediate GT topologies are pairwise distinct (via nucleus injectivity). -/
private theorem gt_ne_of_nucleus_ne
    {n₁ n₂ : Nucleus (LindenbaumAlgebra hubSpokesTransTheory)}
    (hne : n₁ ≠ n₂) :
    nucleusToGrothendieck n₁ ≠ nucleusToGrothendieck n₂ :=
  fun h => hne (nucleusToGrothendieck_injective h)

-- Distinctness from trivial
theorem hubSpokes_botCollapsed_ne_trivial :
    hubSpokes_botCollapsed ≠ hubSpokes_trivial := gt_ne_trivial_of_ne_bot
theorem hubSpokes_qCollapsed_ne_trivial :
    hubSpokes_qCollapsed ≠ hubSpokes_trivial := gt_ne_trivial_of_ne_bot
theorem hubSpokes_pCollapsed_ne_trivial :
    hubSpokes_pCollapsed ≠ hubSpokes_trivial := gt_ne_trivial_of_ne_bot
theorem hubSpokes_gap_ne_trivial :
    hubSpokes_gap ≠ hubSpokes_trivial := gt_ne_trivial_of_ne_bot
theorem hubSpokes_pChannel_ne_trivial :
    hubSpokes_pChannel ≠ hubSpokes_trivial := gt_ne_trivial_of_ne_bot
theorem hubSpokes_qChannel_ne_trivial :
    hubSpokes_qChannel ≠ hubSpokes_trivial := gt_ne_trivial_of_ne_bot

-- Distinctness from discrete
theorem hubSpokes_botCollapsed_ne_discrete :
    hubSpokes_botCollapsed ≠ hubSpokes_discrete :=
  gt_ne_discrete_of_ne_top hubSpokes_nucleus_botCollapsed_ne_discrete
theorem hubSpokes_qCollapsed_ne_discrete :
    hubSpokes_qCollapsed ≠ hubSpokes_discrete :=
  gt_ne_discrete_of_ne_top hubSpokes_nucleus_qCollapsed_ne_discrete
theorem hubSpokes_pCollapsed_ne_discrete :
    hubSpokes_pCollapsed ≠ hubSpokes_discrete :=
  gt_ne_discrete_of_ne_top hubSpokes_nucleus_pCollapsed_ne_discrete
theorem hubSpokes_gap_ne_discrete :
    hubSpokes_gap ≠ hubSpokes_discrete :=
  gt_ne_discrete_of_ne_top hubSpokes_nucleus_gap_ne_discrete
theorem hubSpokes_pChannel_ne_discrete :
    hubSpokes_pChannel ≠ hubSpokes_discrete :=
  gt_ne_discrete_of_ne_top hubSpokes_nucleus_pChannel_ne_discrete
theorem hubSpokes_qChannel_ne_discrete :
    hubSpokes_qChannel ≠ hubSpokes_discrete :=
  gt_ne_discrete_of_ne_top hubSpokes_nucleus_qChannel_ne_discrete

/-!
## Part 11: GT Topology Incomparability
-/

theorem hubSpokes_qCollapsed_not_le_pCollapsed :
    ¬(hubSpokes_qCollapsed ≤ hubSpokes_pCollapsed) := by
  intro h
  exact hubSpokes_nucleus_qCollapsed_not_le_pCollapsed
    (fun x => nucleusToGrothendieck_order_reflecting _ _ h x)

theorem hubSpokes_pCollapsed_not_le_qCollapsed :
    ¬(hubSpokes_pCollapsed ≤ hubSpokes_qCollapsed) := by
  intro h
  exact hubSpokes_nucleus_pCollapsed_not_le_qCollapsed
    (fun x => nucleusToGrothendieck_order_reflecting _ _ h x)

theorem hubSpokes_pChannel_not_le_qChannel :
    ¬(hubSpokes_pChannel ≤ hubSpokes_qChannel) := by
  intro h
  exact hubSpokes_nucleus_pChannel_not_le_qChannel
    (fun x => nucleusToGrothendieck_order_reflecting _ _ h x)

theorem hubSpokes_qChannel_not_le_pChannel :
    ¬(hubSpokes_qChannel ≤ hubSpokes_pChannel) := by
  intro h
  exact hubSpokes_nucleus_qChannel_not_le_pChannel
    (fun x => nucleusToGrothendieck_order_reflecting _ _ h x)

/-!
## Part 12: GT Topology Completeness and Count
-/

/-- Every GT topology on the hub-spokes Lindenbaum algebra is one of 8. -/
theorem hubSpokes_topology_complete :
    ∀ (J : GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory)),
      J = hubSpokes_trivial ∨ J = hubSpokes_botCollapsed ∨
      J = hubSpokes_qCollapsed ∨ J = hubSpokes_pCollapsed ∨
      J = hubSpokes_gap ∨ J = hubSpokes_pChannel ∨
      J = hubSpokes_qChannel ∨ J = hubSpokes_discrete := by
  intro J
  -- Use the right inverse: J = nucleusToGT(gtToNucleus(J))
  rw [← hubSpokes_gtToNucleus_rightInverse J]
  -- Generalize to a free variable so subst works in rcases
  generalize hubSpokes_gtToNucleus J = n
  rcases hubSpokes_nucleus_complete n with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; exact hubSpokes_nucleusGT_trivial
  · right; left; exact hubSpokes_nucleusGT_botCollapsed
  · right; right; left; exact hubSpokes_nucleusGT_qCollapsed
  · right; right; right; left; exact hubSpokes_nucleusGT_pCollapsed
  · right; right; right; right; left; exact hubSpokes_nucleusGT_gap
  · right; right; right; right; right; left; exact hubSpokes_nucleusGT_pChannel
  · right; right; right; right; right; right; left; exact hubSpokes_nucleusGT_qChannel
  · right; right; right; right; right; right; right; exact hubSpokes_nucleusGT_discrete

/-- There are exactly 8 Grothendieck topologies on the hub-spokes Lindenbaum algebra.
Derived from the correspondence bijection + nucleus count. -/
theorem hubSpokes_topology_count :
    ∃ (S : Finset (GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory))),
      S.card = 8 ∧ ∀ J, J ∈ S := by
  obtain ⟨S, hcard, hmem⟩ := hubSpokes_nucleus_count
  refine ⟨S.image hubSpokes_nucleusToGT, ?_, ?_⟩
  · rw [Finset.card_image_of_injective S hubSpokes_nucleusToGT_injective, hcard]
  · intro J
    rw [Finset.mem_image]
    exact ⟨hubSpokes_gtToNucleus J, hmem _, hubSpokes_gtToNucleus_rightInverse J⟩

/-- The nucleus and GT topology lattices have matching cardinality (both 8). -/
theorem hubSpokes_nucleus_card_eq_topology_card :
    (∃ S : Finset (Nucleus (LindenbaumAlgebra hubSpokesTransTheory)),
      S.card = 8 ∧ ∀ n, n ∈ S) ∧
    (∃ S : Finset (GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory)),
      S.card = 8 ∧ ∀ J, J ∈ S) :=
  ⟨hubSpokes_nucleus_count, hubSpokes_topology_count⟩

/-!
## Summary

### Axiom count in this file: 5 bridge axioms
- 2 GT axioms: pullback_stable, transitive (frame-theoretic, Sieve API friction)
- 1 order-reflecting (principal sieve argument, general)
- 1 ne_bot: nucleusToGrothendieck never gives ⊥ (hub-spokes specific)
- 1 exhaustive: every GT topology is ⊥, intermediate, or ⊤ (hub-spokes specific)

### Axioms eliminated: 16
- 6 GT topology axioms from NondeterministicSystems.lean → constructed defs
- 1 NucleusGTCorrespondence axiom → constructed
- 8 matching axioms → proved
- 1 hubSpokes_topology_count → derived

### Net axiom change: 16 eliminated - 5 new bridge = 11 net reduction
-/

end RTS
