/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Birkhoff Representation: 30-Element Spectrum Lattice L₃₀

This file defines all 30 elements of the spectrum lattice L₃₀ (the lattice closure
of the 13 named van Glabbeek energy vectors under componentwise min/max), computes
the complete Hasse diagram (covering relations), and identifies the join-irreducible
and meet-irreducible elements.

## Mathematical Content

The 13 named equivalences are not closed under componentwise meet/join in the ambient
energy frame (WithTop ℕ)⁶. Taking the lattice closure yields exactly 30 elements:
- 13 named (from EnergyVectors.lean)
- 9 Round 1 unnamed (meets/joins of named pairs)
- 8 Round 2 unnamed (meets/joins involving Round 1 elements)

The Birkhoff representation theorem for finite distributive lattices states that
L ≅ O(J(L)), the lattice of downsets of join-irreducibles. We compute J(L₃₀)
and M(L₃₀) explicitly and verify |J| = |M| (Birkhoff duality).

## Main Results

1. `SpectrumElement` — 30-element inductive type for L₃₀
2. `toEnergyBudget` — injective energy vector mapping
3. `Lattice SpectrumElement` — concrete meet/join
4. `coveringRelations` — complete Hasse diagram
5. `joinIrreducibles` / `meetIrreducibles` — J(L₃₀), M(L₃₀)
6. `card_J_eq_M` — |J| = |M|

## References

- Bisping, "Process Equivalence Problems as Energy Games" (CAV 2023, Figure 3)
- Birkhoff, "Lattice Theory" (1967), representation theorem for finite distributive lattices
- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990, 2001)
-/

import RuleSys.SubtoposLattice.LatticeClosureComputation

set_option autoImplicit false

-- Kernel-checked `decide` replaces `native_decide` throughout this file, so that
-- throughout this file, so that downstream results carry only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) rather than `Lean.ofReduceBool` /
-- `Lean.trustCompiler`. The 900-pair round-trip lemmas need a raised recursion limit.
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

universe u

namespace RTS

/-!
## Part 1: SpectrumElement — All 30 Elements of L₃₀
-/

/-- The 30 elements of the spectrum lattice L₃₀, the lattice closure of the
13 named van Glabbeek energy vectors under componentwise min/max in (WithTop ℕ)⁶.

Named elements (13): the van Glabbeek spectrum equivalences.
Round 1 unnamed (9): pairwise meets/joins of incomparable named pairs.
Round 2 unnamed (8): meets/joins involving Round 1 elements. -/
inductive SpectrumElement : Type
  -- Named (13)
  | enabledness : SpectrumElement
  | traces : SpectrumElement
  | failures : SpectrumElement
  | revivals : SpectrumElement
  | readiness : SpectrumElement
  | impossibleFutures : SpectrumElement
  | simulation : SpectrumElement
  | failureTraces : SpectrumElement
  | possibleFutures : SpectrumElement
  | readyTraces : SpectrumElement
  | readySimulation : SpectrumElement
  | twoNestedSim : SpectrumElement
  | bisimulation : SpectrumElement
  -- Round 1 unnamed (9)
  | sim_meet_failures : SpectrumElement      -- S∧F
  | sim_meet_revivals : SpectrumElement      -- S∧RV
  | sim_meet_readiness : SpectrumElement     -- S∧R
  | sim_meet_pf : SpectrumElement            -- S∧PF
  | pf_meet_ft : SpectrumElement             -- PF∧FT
  | pf_meet_rt : SpectrumElement             -- PF∧RT
  | pf_meet_rs : SpectrumElement             -- PF∧RS
  | if_join_ft : SpectrumElement             -- IF∨FT
  | if_join_rt : SpectrumElement             -- IF∨RT
  -- Round 2 unnamed (8)
  | sim_meet_ifJoinFt : SpectrumElement      -- S∧(IF∨FT)
  | pf_meet_ifJoinFt : SpectrumElement       -- PF∧(IF∨FT)
  | simPf_meet_ifJoinFt : SpectrumElement    -- (S∧PF)∧(IF∨FT)
  | if_join_simRv : SpectrumElement          -- IF∨(S∧RV)
  | if_join_simR : SpectrumElement           -- IF∨(S∧R)
  | rt_meet_simPf : SpectrumElement          -- RT∧(S∧PF)
  | if_join_pfRt : SpectrumElement           -- IF∨(PF∧RT)
  | sim_meet_ifJoinRt : SpectrumElement      -- S∧(IF∨RT)
  deriving DecidableEq, Repr

namespace SpectrumElement

/-!
## Part 2: Energy Budget Mapping
-/

/-- Map each spectrum element to its canonical 6-dimensional energy budget.
The dimensions are: (e₁ obsDepth, e₂ conjNesting, e₃ deepPosClause,
e₄ otherPosClause, e₅ negClause, e₆ negNesting). -/
def toEnergyBudget : SpectrumElement → EnergyBudget
  -- Named (13)
  | .enabledness       => ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .traces            => ⟨⊤, (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .failures          => ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .revivals          => ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .readiness         => ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .impossibleFutures => ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), ⊤, (1 : ℕ)⟩
  | .simulation        => ⟨⊤, ⊤, ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩
  | .failureTraces     => ⟨⊤, ⊤, ⊤, (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .possibleFutures   => ⟨⊤, (2 : ℕ), ⊤, ⊤, ⊤, (1 : ℕ)⟩
  | .readyTraces       => ⟨⊤, ⊤, ⊤, (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .readySimulation   => ⟨⊤, ⊤, ⊤, ⊤, (1 : ℕ), (1 : ℕ)⟩
  | .twoNestedSim      => ⟨⊤, ⊤, ⊤, ⊤, ⊤, (1 : ℕ)⟩
  | .bisimulation      => ⟨⊤, ⊤, ⊤, ⊤, ⊤, ⊤⟩
  -- Round 1 unnamed (9)
  | .sim_meet_failures  => ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .sim_meet_revivals  => ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .sim_meet_readiness => ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .sim_meet_pf        => ⟨⊤, (2 : ℕ), ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩
  | .pf_meet_ft         => ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .pf_meet_rt         => ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .pf_meet_rs         => ⟨⊤, (2 : ℕ), ⊤, ⊤, (1 : ℕ), (1 : ℕ)⟩
  | .if_join_ft         => ⟨⊤, ⊤, ⊤, (0 : ℕ), ⊤, (1 : ℕ)⟩
  | .if_join_rt         => ⟨⊤, ⊤, ⊤, (1 : ℕ), ⊤, (1 : ℕ)⟩
  -- Round 2 unnamed (8)
  | .sim_meet_ifJoinFt    => ⟨⊤, ⊤, ⊤, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .pf_meet_ifJoinFt     => ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), ⊤, (1 : ℕ)⟩
  | .simPf_meet_ifJoinFt  => ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .if_join_simRv        => ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), ⊤, (1 : ℕ)⟩
  | .if_join_simR         => ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), ⊤, (1 : ℕ)⟩
  | .rt_meet_simPf        => ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .if_join_pfRt         => ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), ⊤, (1 : ℕ)⟩
  | .sim_meet_ifJoinRt    => ⟨⊤, ⊤, ⊤, (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩

/-!
## Part 3: Fintype Instance
-/

/-- All 30 spectrum elements, enumerated for Fintype. -/
def allElements : List SpectrumElement :=
  [.enabledness, .traces, .failures, .revivals, .readiness,
   .impossibleFutures, .simulation, .failureTraces, .possibleFutures,
   .readyTraces, .readySimulation, .twoNestedSim, .bisimulation,
   .sim_meet_failures, .sim_meet_revivals, .sim_meet_readiness,
   .sim_meet_pf, .pf_meet_ft, .pf_meet_rt, .pf_meet_rs,
   .if_join_ft, .if_join_rt,
   .sim_meet_ifJoinFt, .pf_meet_ifJoinFt, .simPf_meet_ifJoinFt,
   .if_join_simRv, .if_join_simR, .rt_meet_simPf, .if_join_pfRt,
   .sim_meet_ifJoinRt]

private theorem allElements_nodup : allElements.Nodup := by decide

instance : Fintype SpectrumElement where
  elems := ⟨allElements, allElements_nodup⟩
  complete := fun x => by cases x <;> decide

/-- L₃₀ has exactly 30 elements. -/
theorem card : Fintype.card SpectrumElement = 30 := by decide

/-!
## Part 4: Injectivity
-/

/-- Distinct spectrum elements have distinct energy vectors. -/
theorem toEnergyBudget_injective : Function.Injective toEnergyBudget := by
  intro a b h
  cases a <;> cases b <;> simp [toEnergyBudget] at h <;> rfl

/-!
## Part 5: Named Equivalence Embedding
-/

/-- Embed the 13 named equivalences into the 30-element spectrum. -/
def fromNamed : NamedEquivalence → SpectrumElement
  | .enabledness         => .enabledness
  | .traces              => .traces
  | .failures            => .failures
  | .revivals            => .revivals
  | .readiness           => .readiness
  | .impossibleFutures   => .impossibleFutures
  | .simulation          => .simulation
  | .failureTraces       => .failureTraces
  | .possibleFutures     => .possibleFutures
  | .readyTraces         => .readyTraces
  | .readySimulation     => .readySimulation
  | .twoNestedSimulation => .twoNestedSim
  | .bisimulation        => .bisimulation

/-- The named embedding is consistent with energy budgets. -/
theorem fromNamed_consistent :
    ∀ x : NamedEquivalence, (fromNamed x).toEnergyBudget = x.toEnergyBudget := by
  intro x; cases x <;> rfl

/-!
## Part 6: Partial Order on SpectrumElement

We use `PartialOrder.lift` to pull back the componentwise ordering on `EnergyBudget`
along the injective map `toEnergyBudget`.
-/

/-- Partial order on SpectrumElement, lifted from componentwise energy budget ordering
via the injective `toEnergyBudget` map. -/
instance : PartialOrder SpectrumElement :=
  PartialOrder.lift toEnergyBudget toEnergyBudget_injective

/-- Decidable ordering on spectrum elements. -/
instance instDecidableRelSpectrumElementLE :
    DecidableRel (· ≤ · : SpectrumElement → SpectrumElement → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.toEnergyBudget ≤ b.toEnergyBudget))

/-- Decidable strict ordering on spectrum elements. -/
instance instDecidableRelSpectrumElementLT :
    DecidableRel (· < · : SpectrumElement → SpectrumElement → Prop) :=
  fun a b =>
    if h₁ : a ≤ b then
      if h₂ : b ≤ a then isFalse (fun h => h.ne (le_antisymm h₁ h₂))
      else isTrue (lt_of_le_of_ne h₁ (fun heq => h₂ (heq ▸ le_refl _)))
    else isFalse (fun h => h₁ (le_of_lt h))

/-!
## Part 7: Meet and Join Operations
-/

/-- Look up a SpectrumElement by its energy budget. Returns the matching element
if one exists in L₃₀, otherwise returns a default (enabledness). Since L₃₀ is
closed under meet/join, the default is never actually reached for valid inputs. -/
def fromEnergyBudget (e : EnergyBudget) : SpectrumElement :=
  -- We search through all elements to find the one matching the given budget.
  -- Since the set is closed under meet/join, this always succeeds for valid inputs.
  match allElements.find? (fun x => x.toEnergyBudget == e) with
  | some x => x
  | none   => .enabledness  -- unreachable for closed inputs

/-- Meet (infimum) of two spectrum elements via componentwise min of energy budgets. -/
def meet (a b : SpectrumElement) : SpectrumElement :=
  fromEnergyBudget (EnergyBudget.meet a.toEnergyBudget b.toEnergyBudget)

/-- Join (supremum) of two spectrum elements via componentwise max of energy budgets. -/
def join (a b : SpectrumElement) : SpectrumElement :=
  fromEnergyBudget (EnergyBudget.join a.toEnergyBudget b.toEnergyBudget)

/-- The meet operation produces the correct energy budget (all 900 pairs). -/
theorem meet_toEnergyBudget : ∀ (a b : SpectrumElement),
    (meet a b).toEnergyBudget = EnergyBudget.meet a.toEnergyBudget b.toEnergyBudget := by
  decide

/-- The join operation produces the correct energy budget (all 900 pairs). -/
theorem join_toEnergyBudget : ∀ (a b : SpectrumElement),
    (join a b).toEnergyBudget = EnergyBudget.join a.toEnergyBudget b.toEnergyBudget := by
  decide

/-!
## Part 8: Lattice Instance
-/

/-- L₃₀ forms a lattice with componentwise meet and join. -/
instance : Lattice SpectrumElement where
  sup := join
  le_sup_left a b := by
    show (toEnergyBudget a) ≤ (toEnergyBudget (join a b))
    rw [join_toEnergyBudget]; exact EnergyBudget.le_join_left _ _
  le_sup_right a b := by
    show (toEnergyBudget b) ≤ (toEnergyBudget (join a b))
    rw [join_toEnergyBudget]; exact EnergyBudget.le_join_right _ _
  sup_le a b c hac hbc := by
    show (toEnergyBudget (join a b)) ≤ (toEnergyBudget c)
    rw [join_toEnergyBudget]
    exact ⟨max_le hac.1 hbc.1, max_le hac.2.1 hbc.2.1,
           max_le hac.2.2.1 hbc.2.2.1, max_le hac.2.2.2.1 hbc.2.2.2.1,
           max_le hac.2.2.2.2.1 hbc.2.2.2.2.1, max_le hac.2.2.2.2.2 hbc.2.2.2.2.2⟩
  inf := meet
  inf_le_left a b := by
    show (toEnergyBudget (meet a b)) ≤ (toEnergyBudget a)
    rw [meet_toEnergyBudget]; exact EnergyBudget.meet_le_left _ _
  inf_le_right a b := by
    show (toEnergyBudget (meet a b)) ≤ (toEnergyBudget b)
    rw [meet_toEnergyBudget]; exact EnergyBudget.meet_le_right _ _
  le_inf a b c hab hac := by
    show (toEnergyBudget a) ≤ (toEnergyBudget (meet b c))
    rw [meet_toEnergyBudget]
    exact ⟨le_min hab.1 hac.1, le_min hab.2.1 hac.2.1,
           le_min hab.2.2.1 hac.2.2.1, le_min hab.2.2.2.1 hac.2.2.2.1,
           le_min hab.2.2.2.2.1 hac.2.2.2.2.1, le_min hab.2.2.2.2.2 hac.2.2.2.2.2⟩

/-- Enabledness is the bottom element of L₃₀. -/
theorem enabledness_le (a : SpectrumElement) : .enabledness ≤ a := by
  show toEnergyBudget .enabledness ≤ toEnergyBudget a
  cases a <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

/-- Bisimulation is the top element of L₃₀. -/
theorem le_bisimulation (a : SpectrumElement) : a ≤ .bisimulation := by
  show toEnergyBudget a ≤ toEnergyBudget .bisimulation
  cases a <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

instance : BoundedOrder SpectrumElement where
  top := .bisimulation
  le_top := le_bisimulation
  bot := .enabledness
  bot_le := enabledness_le

/-!
## Part 9: Covering Relations (Hasse Diagram)
-/

/-- Element a is covered by element b (a ⋖ b): a < b with nothing strictly between. -/
def covers (a b : SpectrumElement) : Prop :=
  a < b ∧ ∀ c : SpectrumElement, a < c → c < b → False

/-- Covering relation is decidable (finite type with decidable ordering). -/
instance : DecidableRel covers := fun a b =>
  inferInstanceAs (Decidable (a < b ∧ ∀ c : SpectrumElement, a < c → c < b → False))

/-- The complete list of covering pairs (a, b) where a ⋖ b in L₃₀.
54 covering relations computed by exhaustive search over all 870 ordered pairs. -/
def coveringRelations : List (SpectrumElement × SpectrumElement) :=
  [ -- Named ⋖ Named/Unnamed
    (.enabledness, .traces),
    (.traces, .sim_meet_failures),
    (.failures, .revivals),
    (.failures, .impossibleFutures),
    (.revivals, .readiness),
    (.revivals, .pf_meet_ft),
    (.revivals, .if_join_simRv),
    (.readiness, .pf_meet_rt),
    (.readiness, .if_join_simR),
    (.impossibleFutures, .if_join_simRv),
    (.simulation, .readySimulation),
    (.failureTraces, .readyTraces),
    (.failureTraces, .if_join_ft),
    (.possibleFutures, .twoNestedSim),
    (.readyTraces, .readySimulation),
    (.readyTraces, .if_join_rt),
    (.readySimulation, .twoNestedSim),
    (.twoNestedSim, .bisimulation),
    -- Round 1 unnamed ⋖ ...
    (.sim_meet_failures, .failures),
    (.sim_meet_failures, .sim_meet_revivals),
    (.sim_meet_revivals, .revivals),
    (.sim_meet_revivals, .sim_meet_readiness),
    (.sim_meet_revivals, .simPf_meet_ifJoinFt),
    (.sim_meet_readiness, .readiness),
    (.sim_meet_readiness, .rt_meet_simPf),
    (.sim_meet_pf, .simulation),
    (.sim_meet_pf, .pf_meet_rs),
    (.pf_meet_ft, .failureTraces),
    (.pf_meet_ft, .pf_meet_rt),
    (.pf_meet_ft, .pf_meet_ifJoinFt),
    (.pf_meet_rt, .readyTraces),
    (.pf_meet_rt, .pf_meet_rs),
    (.pf_meet_rt, .if_join_pfRt),
    (.pf_meet_rs, .possibleFutures),
    (.pf_meet_rs, .readySimulation),
    (.if_join_ft, .if_join_rt),
    (.if_join_rt, .twoNestedSim),
    -- Round 2 unnamed ⋖ ...
    (.sim_meet_ifJoinFt, .failureTraces),
    (.sim_meet_ifJoinFt, .sim_meet_ifJoinRt),
    (.pf_meet_ifJoinFt, .if_join_ft),
    (.pf_meet_ifJoinFt, .if_join_pfRt),
    (.simPf_meet_ifJoinFt, .pf_meet_ft),
    (.simPf_meet_ifJoinFt, .sim_meet_ifJoinFt),
    (.simPf_meet_ifJoinFt, .rt_meet_simPf),
    (.if_join_simRv, .pf_meet_ifJoinFt),
    (.if_join_simRv, .if_join_simR),
    (.if_join_simR, .if_join_pfRt),
    (.rt_meet_simPf, .sim_meet_pf),
    (.rt_meet_simPf, .pf_meet_rt),
    (.rt_meet_simPf, .sim_meet_ifJoinRt),
    (.if_join_pfRt, .possibleFutures),
    (.if_join_pfRt, .if_join_rt),
    (.sim_meet_ifJoinRt, .simulation),
    (.sim_meet_ifJoinRt, .readyTraces)]

/-- All pairs in coveringRelations are genuine covering relations. -/
theorem coveringRelations_correct :
    ∀ p ∈ coveringRelations, covers p.1 p.2 := by decide

/-- All covering relations are listed in coveringRelations. -/
theorem coveringRelations_complete :
    ∀ a b : SpectrumElement, covers a b → (a, b) ∈ coveringRelations := by decide

/-- The Hasse diagram has exactly 54 covering relations. -/
theorem coveringRelations_length : coveringRelations.length = 54 := by decide

/-!
## Part 10: Join-Irreducibles and Meet-Irreducibles
-/

/-- An element is join-irreducible if it is not ⊥ and cannot be written as a
non-trivial join: x = a ⊔ b implies x = a or x = b. -/
def isJoinIrreducible (x : SpectrumElement) : Prop :=
  x ≠ ⊥ ∧ ∀ a b : SpectrumElement, x = a ⊔ b → x = a ∨ x = b

/-- Decidability of join-irreducibility. -/
instance : DecidablePred isJoinIrreducible := fun x =>
  inferInstanceAs (Decidable (x ≠ ⊥ ∧ ∀ a b : SpectrumElement, x = a ⊔ b → x = a ∨ x = b))

/-- An element is meet-irreducible if it is not ⊤ and cannot be written as a
non-trivial meet: x = a ⊓ b implies x = a or x = b. -/
def isMeetIrreducible (x : SpectrumElement) : Prop :=
  x ≠ ⊤ ∧ ∀ a b : SpectrumElement, x = a ⊓ b → x = a ∨ x = b

/-- Decidability of meet-irreducibility. -/
instance : DecidablePred isMeetIrreducible := fun x =>
  inferInstanceAs (Decidable (x ≠ ⊤ ∧ ∀ a b : SpectrumElement, x = a ⊓ b → x = a ∨ x = b))

/-- The 10 join-irreducible elements of L₃₀.
J(L₃₀) = {T, F, IF, B, S∧F, S∧RV, S∧R, S∧PF, S∧(IF∨FT), (S∧PF)∧(IF∨FT)} -/
def joinIrreducibles : List SpectrumElement :=
  [.traces, .failures, .impossibleFutures, .bisimulation,
   .sim_meet_failures, .sim_meet_revivals, .sim_meet_readiness,
   .sim_meet_pf, .sim_meet_ifJoinFt, .simPf_meet_ifJoinFt]

/-- The 10 meet-irreducible elements of L₃₀.
M(L₃₀) = {E, T, IF, S, PF, RS, 2S, IF∨FT, IF∨RT, IF∨(S∧R)} -/
def meetIrreducibles : List SpectrumElement :=
  [.enabledness, .traces, .impossibleFutures, .simulation,
   .possibleFutures, .readySimulation, .twoNestedSim,
   .if_join_ft, .if_join_rt, .if_join_simR]

/-- All listed join-irreducibles are indeed join-irreducible. -/
theorem joinIrreducibles_correct :
    ∀ x ∈ joinIrreducibles, isJoinIrreducible x := by decide

/-- All join-irreducible elements are in the list. -/
theorem joinIrreducibles_complete :
    ∀ x : SpectrumElement, isJoinIrreducible x → x ∈ joinIrreducibles := by decide

/-- All listed meet-irreducibles are indeed meet-irreducible. -/
theorem meetIrreducibles_correct :
    ∀ x ∈ meetIrreducibles, isMeetIrreducible x := by decide

/-- All meet-irreducible elements are in the list. -/
theorem meetIrreducibles_complete :
    ∀ x : SpectrumElement, isMeetIrreducible x → x ∈ meetIrreducibles := by decide

/-- |J(L₃₀)| = 10 -/
theorem card_joinIrreducibles : joinIrreducibles.length = 10 := by decide

/-- |M(L₃₀)| = 10 -/
theorem card_meetIrreducibles : meetIrreducibles.length = 10 := by decide

/-- |J(L₃₀)| = |M(L₃₀)| = 10 — Birkhoff duality check. -/
theorem card_J_eq_M : joinIrreducibles.length = meetIrreducibles.length := by decide

end SpectrumElement

end RTS
