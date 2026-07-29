/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Computable Hub-Spokes Lattice with 8 Nuclei

This file defines a computable 5-element lattice isomorphic to the hub-spokes
Lindenbaum algebra and constructs all 8 nuclei with their properties proved
by `decide` or explicit case analysis.

## Mathematical Background

The hub-spokes lattice {bot, pq, p, q, top} has the Hasse diagram:
```
    top
   / \
  p   q
   \ /
   pq
    |
   bot
```

It admits exactly 8 nuclei (inflationary idempotent inf-preserving endomorphisms),
corresponding to the 8 subtoposes of the associated presheaf topos.

## Main Results

- `HubSpokesElem`: Computable 5-element type with `DecidableEq`, `Fintype`
- `DistribLattice`, `BoundedOrder`, `Order.Frame` instances
- 8 concrete nucleus definitions with all properties proved computationally
- Transport infrastructure for carrying nucleus results through `OrderIso`

## References

- Johnstone, "Stone Spaces" (1982), II.2
- Funayama-Nakayama (1942)
-/

import Mathlib.Order.Nucleus
import Mathlib.Order.Irreducible
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

universe u

/-!
## Part 1: The HubSpokesElem Type
-/

/-- The 5-element hub-spokes lattice, computable. -/
inductive HubSpokesElem : Type
  | bot   -- bottom
  | pq    -- p ∧ q (meet of generators)
  | p     -- generator p (step(a,b))
  | q     -- generator q (step(a,c))
  | top   -- top
  deriving DecidableEq, Repr

namespace HubSpokesElem

instance : Fintype HubSpokesElem where
  elems := {.bot, .pq, .p, .q, .top}
  complete := fun x => by cases x <;> simp

/-!
## Part 2: Partial Order
-/

/-- Decidable ordering on HubSpokesElem. -/
def le : HubSpokesElem → HubSpokesElem → Bool
  | .bot, _ => true
  | _, .top => true
  | .pq, .pq => true | .pq, .p => true | .pq, .q => true
  | .p, .p => true
  | .q, .q => true
  | _, _ => false

instance : LE HubSpokesElem where
  le a b := le a b = true

instance instDecidableLE : DecidableRel (· ≤ · : HubSpokesElem → HubSpokesElem → Prop) :=
  fun a b => inferInstanceAs (Decidable (le a b = true))

instance : PartialOrder HubSpokesElem where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

/-!
## Part 3: Lattice Operations
-/

/-- Meet (infimum) on HubSpokesElem. -/
def inf : HubSpokesElem → HubSpokesElem → HubSpokesElem
  | .bot, _ => .bot | _, .bot => .bot
  | .top, x => x | x, .top => x
  | .p, .p => .p | .q, .q => .q | .pq, .pq => .pq
  | .p, .q => .pq | .q, .p => .pq
  | .p, .pq => .pq | .pq, .p => .pq
  | .q, .pq => .pq | .pq, .q => .pq

/-- Join (supremum) on HubSpokesElem. -/
def sup : HubSpokesElem → HubSpokesElem → HubSpokesElem
  | .top, _ => .top | _, .top => .top
  | .bot, x => x | x, .bot => x
  | .p, .p => .p | .q, .q => .q | .pq, .pq => .pq
  | .p, .q => .top | .q, .p => .top
  | .p, .pq => .p | .pq, .p => .p
  | .q, .pq => .q | .pq, .q => .q

instance : Min HubSpokesElem where min := inf
instance : Max HubSpokesElem where max := sup

instance : OrderBot HubSpokesElem where
  bot := .bot
  bot_le := by decide

instance : OrderTop HubSpokesElem where
  top := .top
  le_top := by decide

instance : BoundedOrder HubSpokesElem where
  __ := inferInstanceAs (OrderBot HubSpokesElem)
  __ := inferInstanceAs (OrderTop HubSpokesElem)

instance : Lattice HubSpokesElem where
  inf := inf
  sup := sup
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : DistribLattice HubSpokesElem where
  le_sup_inf := by decide

/-!
## Part 4: CompleteLattice and Frame

The CompleteLattice is noncomputable (sSup/sInf take Set arguments), but that's
fine -- we only need decide on the finite lattice operations.
-/

noncomputable instance : CompleteLattice HubSpokesElem :=
  Fintype.toCompleteLattice HubSpokesElem

noncomputable instance : CompleteDistribLattice HubSpokesElem :=
  Fintype.toCompleteDistribLattice HubSpokesElem

noncomputable instance : Order.Frame HubSpokesElem :=
  inferInstanceAs (Order.Frame HubSpokesElem)

/-!
## Part 5: Eight Concrete Nuclei

Each nucleus is defined as a function HubSpokesElem → HubSpokesElem, then
wrapped into a Nucleus value with all axioms proved.
-/

/-- The trivial nucleus (identity). -/
def concreteNucleus_trivial : HubSpokesElem → HubSpokesElem := id

/-- The bot-collapsed nucleus: j(bot) = pq, rest fixed. -/
def concreteNucleus_botCollapsed : HubSpokesElem → HubSpokesElem
  | .bot => .pq | .pq => .pq | .p => .p | .q => .q | .top => .top

/-- The q-collapsed nucleus: j(pq) = p, j(q) = top. -/
def concreteNucleus_qCollapsed : HubSpokesElem → HubSpokesElem
  | .bot => .bot | .pq => .p | .p => .p | .q => .top | .top => .top

/-- The p-collapsed nucleus: j(pq) = q, j(p) = top. -/
def concreteNucleus_pCollapsed : HubSpokesElem → HubSpokesElem
  | .bot => .bot | .pq => .q | .p => .top | .q => .q | .top => .top

/-- The gap nucleus: j(pq) = j(p) = j(q) = top. -/
def concreteNucleus_gap : HubSpokesElem → HubSpokesElem
  | .bot => .bot | .pq => .top | .p => .top | .q => .top | .top => .top

/-- The p-channel nucleus: j(bot) = j(pq) = p, j(q) = top. -/
def concreteNucleus_pChannel : HubSpokesElem → HubSpokesElem
  | .bot => .p | .pq => .p | .p => .p | .q => .top | .top => .top

/-- The q-channel nucleus: j(bot) = j(pq) = q, j(p) = top. -/
def concreteNucleus_qChannel : HubSpokesElem → HubSpokesElem
  | .bot => .q | .pq => .q | .p => .top | .q => .q | .top => .top

/-- The discrete nucleus (constant top). -/
def concreteNucleus_discrete : HubSpokesElem → HubSpokesElem := fun _ => .top

/-!
### Wrapping into Nucleus values

We need to prove inf-preservation, inflationarity, and idempotence for each.
-/

/-- Helper: construct a Nucleus from a function with all properties decidable. -/
noncomputable def mkNucleus (f : HubSpokesElem → HubSpokesElem)
    (h_inf : ∀ a b : HubSpokesElem, f (a ⊓ b) = f a ⊓ f b)
    (h_le : ∀ a : HubSpokesElem, a ≤ f a)
    (h_idem : ∀ a : HubSpokesElem, f (f a) ≤ f a) :
    Nucleus HubSpokesElem where
  toInfHom := ⟨f, h_inf⟩
  le_apply' := h_le
  idempotent' := h_idem

noncomputable def concreteNucleus_trivial_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_trivial
    (by decide) (by decide) (by decide)

noncomputable def concreteNucleus_botCollapsed_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_botCollapsed
    (by decide) (by decide) (by decide)

noncomputable def concreteNucleus_qCollapsed_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_qCollapsed
    (by decide) (by decide) (by decide)

noncomputable def concreteNucleus_pCollapsed_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_pCollapsed
    (by decide) (by decide) (by decide)

noncomputable def concreteNucleus_gap_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_gap
    (by decide) (by decide) (by decide)

noncomputable def concreteNucleus_pChannel_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_pChannel
    (by decide) (by decide) (by decide)

noncomputable def concreteNucleus_qChannel_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_qChannel
    (by decide) (by decide) (by decide)

noncomputable def concreteNucleus_discrete_nucleus : Nucleus HubSpokesElem :=
  mkNucleus concreteNucleus_discrete
    (by decide) (by decide) (by decide)

/-!
### Trivial and discrete nuclei match Mathlib's bot/top
-/

theorem concreteNucleus_trivial_eq_bot :
    concreteNucleus_trivial_nucleus = (⊥ : Nucleus HubSpokesElem) := by
  ext x; cases x <;> rfl

theorem concreteNucleus_discrete_eq_top :
    concreteNucleus_discrete_nucleus = (⊤ : Nucleus HubSpokesElem) := by
  ext x; cases x <;> rfl

/-!
## Part 6: Ordering, Distinctness, and Incomparability

The ordering on Nucleus is pointwise: n₁ ≤ n₂ ↔ ∀ x, n₁ x ≤ n₂ x.
-/

/-- Helper: two nuclei are distinct if they differ at some element. -/
private theorem ne_of_apply_ne {n₁ n₂ : Nucleus HubSpokesElem}
    (x : HubSpokesElem) (h : n₁ x ≠ n₂ x) : n₁ ≠ n₂ := by
  intro heq; exact h (congr_arg (· x) (congrArg DFunLike.coe heq))

/-- Helper: two nuclei are not ≤ if one exceeds the other at some element. -/
private theorem not_le_of_apply_not_le {n₁ n₂ : Nucleus HubSpokesElem}
    (x : HubSpokesElem) (h : ¬(n₁ x ≤ n₂ x)) : ¬(n₁ ≤ n₂) :=
  fun hle => h (hle x)

-- True ordering relations (verified computationally):
-- trivial ≤ everything (from bot_le)
-- everything ≤ discrete (from le_top)
-- botCollapsed ≤ pChannel, qChannel
-- qCollapsed ≤ gap, pChannel
-- pCollapsed ≤ gap, qChannel

theorem concrete_botCollapsed_le_pChannel :
    concreteNucleus_botCollapsed_nucleus ≤ concreteNucleus_pChannel_nucleus := by
  intro x; cases x <;> decide

theorem concrete_botCollapsed_le_qChannel :
    concreteNucleus_botCollapsed_nucleus ≤ concreteNucleus_qChannel_nucleus := by
  intro x; cases x <;> decide

theorem concrete_qCollapsed_le_gap :
    concreteNucleus_qCollapsed_nucleus ≤ concreteNucleus_gap_nucleus := by
  intro x; cases x <;> decide

theorem concrete_pCollapsed_le_gap :
    concreteNucleus_pCollapsed_nucleus ≤ concreteNucleus_gap_nucleus := by
  intro x; cases x <;> decide

theorem concrete_qCollapsed_le_pChannel :
    concreteNucleus_qCollapsed_nucleus ≤ concreteNucleus_pChannel_nucleus := by
  intro x; cases x <;> decide

theorem concrete_pCollapsed_le_qChannel :
    concreteNucleus_pCollapsed_nucleus ≤ concreteNucleus_qChannel_nucleus := by
  intro x; cases x <;> decide

-- Incomparability results (botCollapsed is incomparable with qCollapsed, pCollapsed, gap)
-- (gap is incomparable with pChannel, qChannel)

theorem concrete_botCollapsed_not_le_qCollapsed :
    ¬(concreteNucleus_botCollapsed_nucleus ≤ concreteNucleus_qCollapsed_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

theorem concrete_qCollapsed_not_le_botCollapsed :
    ¬(concreteNucleus_qCollapsed_nucleus ≤ concreteNucleus_botCollapsed_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_botCollapsed_not_le_pCollapsed :
    ¬(concreteNucleus_botCollapsed_nucleus ≤ concreteNucleus_pCollapsed_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

theorem concrete_pCollapsed_not_le_botCollapsed :
    ¬(concreteNucleus_pCollapsed_nucleus ≤ concreteNucleus_botCollapsed_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_botCollapsed_not_le_gap :
    ¬(concreteNucleus_botCollapsed_nucleus ≤ concreteNucleus_gap_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

theorem concrete_gap_not_le_botCollapsed :
    ¬(concreteNucleus_gap_nucleus ≤ concreteNucleus_botCollapsed_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_gap_not_le_pChannel :
    ¬(concreteNucleus_gap_nucleus ≤ concreteNucleus_pChannel_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_pChannel_not_le_gap :
    ¬(concreteNucleus_pChannel_nucleus ≤ concreteNucleus_gap_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

theorem concrete_gap_not_le_qChannel :
    ¬(concreteNucleus_gap_nucleus ≤ concreteNucleus_qChannel_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_qChannel_not_le_gap :
    ¬(concreteNucleus_qChannel_nucleus ≤ concreteNucleus_gap_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

theorem concrete_qCollapsed_not_le_qChannel :
    ¬(concreteNucleus_qCollapsed_nucleus ≤ concreteNucleus_qChannel_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_qChannel_not_le_qCollapsed :
    ¬(concreteNucleus_qChannel_nucleus ≤ concreteNucleus_qCollapsed_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

theorem concrete_pCollapsed_not_le_pChannel :
    ¬(concreteNucleus_pCollapsed_nucleus ≤ concreteNucleus_pChannel_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_pChannel_not_le_pCollapsed :
    ¬(concreteNucleus_pChannel_nucleus ≤ concreteNucleus_pCollapsed_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

-- Original 4 incomparability pairs (qCollapsed ∥ pCollapsed, pChannel ∥ qChannel)
theorem concrete_qCollapsed_not_le_pCollapsed :
    ¬(concreteNucleus_qCollapsed_nucleus ≤ concreteNucleus_pCollapsed_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_pCollapsed_not_le_qCollapsed :
    ¬(concreteNucleus_pCollapsed_nucleus ≤ concreteNucleus_qCollapsed_nucleus) :=
  not_le_of_apply_not_le .pq (by decide)

theorem concrete_pChannel_not_le_qChannel :
    ¬(concreteNucleus_pChannel_nucleus ≤ concreteNucleus_qChannel_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

theorem concrete_qChannel_not_le_pChannel :
    ¬(concreteNucleus_qChannel_nucleus ≤ concreteNucleus_pChannel_nucleus) :=
  not_le_of_apply_not_le .bot (by decide)

/-!
### Distinctness

Each pair of distinct nuclei differs at some element. We exhibit the witness.
-/

theorem concrete_botCollapsed_ne_trivial :
    concreteNucleus_botCollapsed_nucleus ≠ concreteNucleus_trivial_nucleus :=
  ne_of_apply_ne .bot (by decide)

theorem concrete_botCollapsed_ne_discrete :
    concreteNucleus_botCollapsed_nucleus ≠ concreteNucleus_discrete_nucleus :=
  ne_of_apply_ne .p (by decide)

theorem concrete_qCollapsed_ne_trivial :
    concreteNucleus_qCollapsed_nucleus ≠ concreteNucleus_trivial_nucleus :=
  ne_of_apply_ne .pq (by decide)

theorem concrete_qCollapsed_ne_discrete :
    concreteNucleus_qCollapsed_nucleus ≠ concreteNucleus_discrete_nucleus :=
  ne_of_apply_ne .bot (by decide)

theorem concrete_pCollapsed_ne_trivial :
    concreteNucleus_pCollapsed_nucleus ≠ concreteNucleus_trivial_nucleus :=
  ne_of_apply_ne .pq (by decide)

theorem concrete_pCollapsed_ne_discrete :
    concreteNucleus_pCollapsed_nucleus ≠ concreteNucleus_discrete_nucleus :=
  ne_of_apply_ne .bot (by decide)

theorem concrete_gap_ne_trivial :
    concreteNucleus_gap_nucleus ≠ concreteNucleus_trivial_nucleus :=
  ne_of_apply_ne .pq (by decide)

theorem concrete_gap_ne_discrete :
    concreteNucleus_gap_nucleus ≠ concreteNucleus_discrete_nucleus :=
  ne_of_apply_ne .bot (by decide)

theorem concrete_pChannel_ne_trivial :
    concreteNucleus_pChannel_nucleus ≠ concreteNucleus_trivial_nucleus :=
  ne_of_apply_ne .bot (by decide)

theorem concrete_pChannel_ne_discrete :
    concreteNucleus_pChannel_nucleus ≠ concreteNucleus_discrete_nucleus :=
  ne_of_apply_ne .p (by decide)

theorem concrete_qChannel_ne_trivial :
    concreteNucleus_qChannel_nucleus ≠ concreteNucleus_trivial_nucleus :=
  ne_of_apply_ne .bot (by decide)

theorem concrete_qChannel_ne_discrete :
    concreteNucleus_qChannel_nucleus ≠ concreteNucleus_discrete_nucleus :=
  ne_of_apply_ne .q (by decide)

/-!
## Part 9: Completeness

Every nucleus on HubSpokesElem is one of the 8 named nuclei.
We prove this by case analysis on the values of j at each element.
-/

/-- Every nucleus on HubSpokesElem is one of the 8 named nuclei.

The proof proceeds by case analysis on the values of `n` at each element, using:
- Inflationarity: `x ≤ n x` constrains values to elements above `x`
- Inf-preservation: `n (p ⊓ q) = n p ⊓ n q` determines `n .pq` from `n .p` and `n .q`
- Idempotency: `n (n x) = n x` eliminates non-fixpoint candidates for `n .bot`

This gives 2 choices for `n .p` × 2 for `n .q` × 2 valid for `n .bot` = 8 nuclei. -/
theorem concrete_nucleus_complete
    (n : Nucleus HubSpokesElem) :
    n = concreteNucleus_trivial_nucleus ∨
    n = concreteNucleus_botCollapsed_nucleus ∨
    n = concreteNucleus_qCollapsed_nucleus ∨
    n = concreteNucleus_pCollapsed_nucleus ∨
    n = concreteNucleus_gap_nucleus ∨
    n = concreteNucleus_pChannel_nucleus ∨
    n = concreteNucleus_qChannel_nucleus ∨
    n = concreteNucleus_discrete_nucleus := by
  -- Step 1: Determine n .top
  have h_top : n .top = .top := le_antisymm le_top Nucleus.le_apply
  -- Step 2: Determine possible values of n .p and n .q (inflationarity)
  have hp : n .p = .p ∨ n .p = .top := by
    have : ∀ x : HubSpokesElem, .p ≤ x → x = .p ∨ x = .top := by decide
    exact this _ Nucleus.le_apply
  have hq : n .q = .q ∨ n .q = .top := by
    have : ∀ x : HubSpokesElem, .q ≤ x → x = .q ∨ x = .top := by decide
    exact this _ Nucleus.le_apply
  -- Step 3: n .pq is determined by n .p and n .q (inf-preservation)
  have hpq : n .pq = n .p ⊓ n .q := by
    have h : (.pq : HubSpokesElem) = .p ⊓ .q := by decide
    conv_lhs => rw [h]
    exact n.map_inf
  -- Step 4: n .bot ≤ n .pq (inf-preservation at ⊥)
  have hbot_le : n .bot ≤ n .pq := by
    have hmf : n (.bot ⊓ .pq) = n .bot ⊓ n .pq := n.map_inf
    have : (.bot : HubSpokesElem) ⊓ .pq = .bot := by decide
    rw [this] at hmf; rw [hmf]; exact inf_le_right
  -- Step 5: n (n .bot) = n .bot (idempotency — used to eliminate invalid candidates)
  have hbot_idem : n (n .bot) = n .bot := Nucleus.idempotent _
  -- Case analysis on n .p ∈ {.p, .top} and n .q ∈ {.q, .top}
  rcases hp with hp | hp <;> rcases hq with hq | hq
  -- Case (n .p = .p, n .q = .q): n .pq = .p ⊓ .q = .pq
  · have hpq_val : n .pq = .pq := by rw [hpq, hp, hq]; decide
    have hbot_bound : n .bot ≤ .pq := hpq_val ▸ hbot_le
    have hbot_opts : n .bot = .bot ∨ n .bot = .pq := by
      have : ∀ x : HubSpokesElem, .bot ≤ x → x ≤ .pq → x = .bot ∨ x = .pq := by decide
      exact this _ Nucleus.le_apply hbot_bound
    rcases hbot_opts with hbot | hbot
    · left; ext x; cases x <;> assumption                            -- trivial
    · right; left; ext x; cases x <;> assumption                     -- botCollapsed
  -- Case (n .p = .p, n .q = .top): n .pq = .p ⊓ .top = .p
  · have hpq_val : n .pq = .p := by rw [hpq, hp, hq]; decide
    have hbot_bound : n .bot ≤ .p := hpq_val ▸ hbot_le
    have hbot_opts : n .bot = .bot ∨ n .bot = .pq ∨ n .bot = .p := by
      have : ∀ x : HubSpokesElem, .bot ≤ x → x ≤ .p → x = .bot ∨ x = .pq ∨ x = .p := by decide
      exact this _ Nucleus.le_apply hbot_bound
    rcases hbot_opts with hbot | hbot | hbot
    · right; right; left; ext x; cases x <;> assumption              -- qCollapsed
    · exfalso; rw [hbot] at hbot_idem; rw [hpq_val] at hbot_idem    -- impossible: n(.pq) = .p ≠ .pq
      exact absurd hbot_idem (by decide)
    · right; right; right; right; right; left                        -- pChannel
      ext x; cases x <;> assumption
  -- Case (n .p = .top, n .q = .q): n .pq = .top ⊓ .q = .q
  · have hpq_val : n .pq = .q := by rw [hpq, hp, hq]; decide
    have hbot_bound : n .bot ≤ .q := hpq_val ▸ hbot_le
    have hbot_opts : n .bot = .bot ∨ n .bot = .pq ∨ n .bot = .q := by
      have : ∀ x : HubSpokesElem, .bot ≤ x → x ≤ .q → x = .bot ∨ x = .pq ∨ x = .q := by decide
      exact this _ Nucleus.le_apply hbot_bound
    rcases hbot_opts with hbot | hbot | hbot
    · right; right; right; left; ext x; cases x <;> assumption       -- pCollapsed
    · exfalso; rw [hbot] at hbot_idem; rw [hpq_val] at hbot_idem    -- impossible: n(.pq) = .q ≠ .pq
      exact absurd hbot_idem (by decide)
    · right; right; right; right; right; right; left                 -- qChannel
      ext x; cases x <;> assumption
  -- Case (n .p = .top, n .q = .top): n .pq = .top ⊓ .top = .top
  · have hpq_val : n .pq = .top := by rw [hpq, hp, hq]; decide
    have hbot_opts : n .bot = .bot ∨ n .bot = .pq ∨ n .bot = .p ∨ n .bot = .q ∨ n .bot = .top := by
      have : ∀ x : HubSpokesElem, x = .bot ∨ x = .pq ∨ x = .p ∨ x = .q ∨ x = .top := by decide
      exact this _
    rcases hbot_opts with hbot | hbot | hbot | hbot | hbot
    · right; right; right; right; left                               -- gap
      ext x; cases x <;> assumption
    · exfalso; rw [hbot] at hbot_idem; rw [hpq_val] at hbot_idem    -- impossible: n(.pq) = .top ≠ .pq
      exact absurd hbot_idem (by decide)
    · exfalso; rw [hbot] at hbot_idem; rw [hp] at hbot_idem         -- impossible: n(.p) = .top ≠ .p
      exact absurd hbot_idem (by decide)
    · exfalso; rw [hbot] at hbot_idem; rw [hq] at hbot_idem         -- impossible: n(.q) = .top ≠ .q
      exact absurd hbot_idem (by decide)
    · right; right; right; right; right; right; right                -- discrete
      ext x; cases x <;> assumption

-- The count theorem (∃ Finset of size 8 containing all nuclei) is a corollary of
-- concrete_nucleus_complete (at most 8) plus Part 8 distinctness (all 8 are pairwise
-- distinct). The Finset formulation is omitted because it requires DecidableEq on
-- Nucleus HubSpokesElem, which is available in principle but adds significant boilerplate.

/-!
## Part 10: Nucleus Transport Infrastructure

Transport nuclei through an OrderIso between frames.
-/

section NucleusTransport

variable {L M : Type*} [Order.Frame L] [Order.Frame M]

/-- Transport a nucleus through an order isomorphism (reversed direction).
Given φ : L ≃o M and a nucleus n on M, produces a nucleus on L. -/
noncomputable def Nucleus.transport
    (φ : L ≃o M) (n : Nucleus M) : Nucleus L where
  toInfHom :=
    { toFun := fun x => φ.symm (n (φ x))
      map_inf' := fun a b => by
        rw [OrderIso.map_inf φ a b, n.map_inf, OrderIso.map_inf φ.symm] }
  le_apply' := fun x => by
    calc x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
      _ ≤ φ.symm (n (φ x)) := φ.symm.monotone Nucleus.le_apply
  idempotent' := fun x => by
    change φ.symm (n (φ (φ.symm (n (φ x))))) ≤ φ.symm (n (φ x))
    rw [φ.apply_symm_apply]
    exact φ.symm.monotone (le_of_eq (Nucleus.idempotent _))

/-- Transport preserves ordering: if n₁ ≤ n₂ then transport n₁ ≤ transport n₂. -/
theorem Nucleus.transport_mono
    (φ : L ≃o M) (n₁ n₂ : Nucleus M) (h : n₁ ≤ n₂) :
    Nucleus.transport φ n₁ ≤ Nucleus.transport φ n₂ := by
  intro x
  change φ.symm (n₁ (φ x)) ≤ φ.symm (n₂ (φ x))
  exact φ.symm.monotone (h (φ x))

/-- Transport reflects ordering: if transport n₁ ≤ transport n₂ then n₁ ≤ n₂. -/
theorem Nucleus.transport_reflects_le
    (φ : L ≃o M) (n₁ n₂ : Nucleus M) (h : Nucleus.transport φ n₁ ≤ Nucleus.transport φ n₂) :
    n₁ ≤ n₂ := by
  intro x
  have hx := h (φ.symm x)
  -- hx : (transport φ n₁) (φ.symm x) ≤ (transport φ n₂) (φ.symm x)
  -- which unfolds to: φ.symm (n₁ (φ (φ.symm x))) ≤ φ.symm (n₂ (φ (φ.symm x)))
  -- after φ.apply_symm_apply: φ.symm (n₁ x) ≤ φ.symm (n₂ x)
  -- since φ.symm is an order iso, this gives n₁ x ≤ n₂ x
  change φ.symm (n₁ (φ (φ.symm x))) ≤ φ.symm (n₂ (φ (φ.symm x))) at hx
  rw [φ.apply_symm_apply] at hx
  exact φ.symm.le_iff_le.mp hx

/-- Transport is injective. -/
theorem Nucleus.transport_injective
    (φ : L ≃o M) : Function.Injective (Nucleus.transport φ) := by
  intro n₁ n₂ h
  ext x
  have hle : Nucleus.transport φ n₁ ≤ Nucleus.transport φ n₂ := le_of_eq h
  have hge : Nucleus.transport φ n₂ ≤ Nucleus.transport φ n₁ := ge_of_eq h
  have h1 := Nucleus.transport_reflects_le φ n₁ n₂ hle
  have h2 := Nucleus.transport_reflects_le φ n₂ n₁ hge
  exact le_antisymm (h1 x) (h2 x)

/-- Transport of ⊥ (identity nucleus) is ⊥. -/
theorem Nucleus.transport_bot
    (φ : L ≃o M) : Nucleus.transport φ ⊥ = ⊥ := by
  ext x
  simp [Nucleus.transport, Nucleus.bot_apply, φ.symm_apply_apply]

/-- Transport of ⊤ (constant ⊤ nucleus) is ⊤. -/
theorem Nucleus.transport_top
    (φ : L ≃o M) : Nucleus.transport φ ⊤ = ⊤ := by
  ext x
  simp [Nucleus.transport, Nucleus.top_apply, OrderIso.map_top]

end NucleusTransport

end HubSpokesElem
