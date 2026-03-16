/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Negation Collapse for Geometric Subfunctors

This file proves the Negation Collapse Theorem for geometric subfunctors of the
generic model U_T in the presheaf topos Set[T_LTS] = [f.p.LTS_L^op, Set].

## Mathematical Content

A subfunctor S of the generic model U_T assigns to each finite LTS G a subset
S(G) of its vertices, with the naturality condition that LTS homomorphisms
preserve membership (forward direction). The presheaf-theoretic Heyting negation
of S is:
  (not S)(G) = { v in G | forall (H : FinLTS L) (h : LTSHom G H), v' = h(v) -> v' notin S(H) }

For geometric subfunctors -- those arising from positive existential HML formulas
(HMLPos) via the Phase 162 correspondence -- the Free Extension Lemma (Phase 184)
guarantees that every pointed LTS (G, v) can be extended to satisfy any HMLPos formula.
This immediately implies:

**Negation Collapse**: For any HMLPos formula phi, not S_phi = bot (the empty subfunctor).
**Double Negation Density**: For any HMLPos formula phi, not not S_phi = top (the full subfunctor).

These are the subfunctor-level counterparts of the sieve-level negation collapse
proved in Phase 161 (SubobjectClassifier.lean), and connect to the De Morgan
property of the Ore condition via model extensibility.

## Key Definitions

- `LTSSubfunctor L`: Subfunctor of U_T (predicate on vertices, natural in LTSHom)
- `HMLPos.toSubfunctor`: Geometric subfunctor from an HMLPos formula
- `LTSSubfunctor.negation`: Presheaf Heyting negation of a subfunctor
- `geometric_negation_collapse`: not S_phi = bot for any HMLPos phi
- `geometric_double_negation_dense`: not not S_phi = top for any HMLPos phi

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992) -- Heyting negation in presheaf toposes
- Caramello, "Theories, Sites, Toposes" (2018) -- geometric logic and classifying toposes
-/

import RuleSys.PresheafTopos.FreeExtension

set_option autoImplicit false

universe u

namespace RTS.PresheafTopos

/-!
## Part 1: Subfunctor Infrastructure
-/

/-- A subfunctor of the generic model U_T in Set[T_LTS].
    Assigns to each finite LTS G a subset of its vertices (via a predicate),
    with the naturality condition that LTS homomorphisms preserve membership
    in the forward direction. -/
structure LTSSubfunctor (L : Type) [Fintype L] [DecidableEq L] where
  /-- The predicate assigning to each LTS a subset of vertices -/
  pred : (G : FinLTS L) -> G.Vertex -> Prop
  /-- Forward preservation by homomorphisms (naturality condition) -/
  natural : forall {G H : FinLTS L} (f : LTSHom G H) (v : G.Vertex),
    pred G v -> pred H (f.toFun v)

/-!
## Part 2: Geometric Subfunctors from HMLPos
-/

/-- Construct a subfunctor of U_T from a positive existential HML formula.
    The predicate is satisfaction of the formula, and naturality follows from
    `HMLPos.preserved_by_hom` (forward preservation by homomorphisms). -/
def HMLPos.toSubfunctor {L : Type} [Fintype L] [DecidableEq L]
    (phi : HMLPos L) : LTSSubfunctor L where
  pred := fun G v => phi.satisfies G v
  natural := fun f v h => HMLPos.preserved_by_hom f v phi h

/-!
## Part 3: Distinguished Subfunctors (Bot and Top)
-/

/-- The empty (bottom) subfunctor: no vertex satisfies the predicate. -/
def LTSSubfunctor.bot (L : Type) [Fintype L] [DecidableEq L] : LTSSubfunctor L where
  pred := fun _ _ => False
  natural := fun _ _ h => h

/-- The full (top) subfunctor: every vertex satisfies the predicate. -/
def LTSSubfunctor.top (L : Type) [Fintype L] [DecidableEq L] : LTSSubfunctor L where
  pred := fun _ _ => True
  natural := fun _ _ _ => trivial

/-!
## Part 4: Presheaf Heyting Negation
-/

/-- The presheaf Heyting negation of a subfunctor S.
    (not S)(G, v) holds iff for every extension h : G -> H, h(v) is not in S(H).
    This is the standard formula for negation in [C^op, Set]:
      (not S)(G) = { v | forall H, forall h : G -> H, h(v) notin S(H) }

    Naturality proof: if v in (not S)(G) and f : G -> K, then for any h : K -> H,
    (h . f) : G -> H is a morphism, so not S(H, (h.f)(v)) = not S(H, h(f(v))),
    proving f(v) in (not S)(K). -/
def LTSSubfunctor.negation {L : Type} [Fintype L] [DecidableEq L]
    (S : LTSSubfunctor L) : LTSSubfunctor L where
  pred := fun G v => forall (H : FinLTS L) (h : LTSHom G H), ¬ S.pred H (h.toFun v)
  natural := fun {G K} f v hv H h => by
    have := hv H (LTSHom.comp f h)
    simp [LTSHom.comp] at this
    exact this

/-!
## Part 5: Negation of Bot and Top
-/

/-- Negation of the empty subfunctor is the full subfunctor (pointwise).
    not bot = top: for any G and v, (not bot)(G, v) holds because
    forall H h, not False is trivially true. -/
theorem LTSSubfunctor.negation_bot_is_top {L : Type} [Fintype L] [DecidableEq L] :
    forall (G : FinLTS L) (v : G.Vertex),
      (LTSSubfunctor.bot L).negation.pred G v := by
  intro G v H h
  exact id

/-- Negation of the full subfunctor is the empty subfunctor (pointwise).
    not top = bot: for any G and v, (not top)(G, v) is False because
    taking H = G and h = id gives not True, which is absurd. -/
theorem LTSSubfunctor.negation_top_is_bot {L : Type} [Fintype L] [DecidableEq L] :
    forall (G : FinLTS L) (v : G.Vertex),
      ¬ (LTSSubfunctor.top L).negation.pred G v := by
  intro G v h
  exact h G (LTSHom.id G) trivial

/-!
## Part 6: Geometric Negation Collapse
-/

/-- **Geometric Negation Collapse Theorem**: The presheaf negation of any geometric
    subfunctor is empty.

    For any HMLPos formula phi, (not S_phi)(G, v) is False for all G and v.
    Proof: Suppose v in (not S_phi)(G). Then for all H, h : G -> H, phi does not
    hold at h(v) in H. But by the Free Extension Lemma, there exist H and h such
    that phi.satisfies H (h(v)). Contradiction.

    This is the subfunctor-level counterpart of the sieve-level result:
    not S = empty for non-empty sieves in Omega(G) (Phase 161). -/
theorem geometric_negation_collapse {L : Type} [Fintype L] [DecidableEq L]
    (phi : HMLPos L) :
    forall (G : FinLTS L) (v : G.Vertex),
      ¬ (phi.toSubfunctor.negation.pred G v) := by
  intro G v h_neg
  -- h_neg : forall H h, not (phi.satisfies H (h.toFun v))
  -- By the Free Extension Lemma, obtain H and h with phi.satisfies H (h.toFun v)
  obtain ⟨H, h, h_sat⟩ := freeExtensionLemma G v phi
  -- This contradicts h_neg
  exact h_neg H h h_sat

/-- **Geometric Double Negation Density**: Every geometric subfunctor is
    double-negation dense (not not S_phi = top).

    For any HMLPos formula phi, (not not S_phi)(G, v) holds for all G and v.
    Proof: (not not S_phi)(G, v) = forall H h, not ((not S_phi)(H, h(v))).
    By geometric_negation_collapse, (not S_phi)(H, h(v)) is False for all H, h.
    So not False is trivially true. -/
theorem geometric_double_negation_dense {L : Type} [Fintype L] [DecidableEq L]
    (phi : HMLPos L) :
    forall (G : FinLTS L) (v : G.Vertex),
      phi.toSubfunctor.negation.negation.pred G v := by
  intro G v H h
  exact geometric_negation_collapse phi H (h.toFun v)

/-!
## Part 7: Negation Collapse Connection

The negation collapse operates at two levels in the topos Set[T_LTS]:

1. **Sieve level** (Phase 161, SubobjectClassifier.lean): For non-empty sieves
   S in Omega(G), the Heyting negation not S = empty. This follows from the
   right Ore condition (every span can be completed).

2. **Subfunctor level** (this file): For geometric subfunctors S_phi of the
   generic model U_T, the Heyting negation not S_phi = bot. This follows from
   the Free Extension Lemma (every pointed LTS can be extended to satisfy phi).

Both are instances of the same De Morgan phenomenon: model extensibility prevents
complementation. The right Ore condition (sieve level) and the Free Extension
Lemma (subfunctor level) are both manifestations of the fact that in the category
of finite LTS, objects can always be extended.
-/

/-- Summary conjunction combining the four main results about negation of subfunctors.
    - Part 1: Geometric negation collapse (not S_phi = bot)
    - Part 2: Geometric double negation density (not not S_phi = top)
    - Part 3: not bot = top
    - Part 4: not top = bot -/
theorem negation_collapse_connection {L : Type} [Fintype L] [DecidableEq L] :
    -- Part 1: Geometric negation collapse
    (forall (phi : HMLPos L) (G : FinLTS L) (v : G.Vertex),
      ¬ (phi.toSubfunctor.negation.pred G v)) ∧
    -- Part 2: Geometric double negation density
    (forall (phi : HMLPos L) (G : FinLTS L) (v : G.Vertex),
      phi.toSubfunctor.negation.negation.pred G v) ∧
    -- Part 3: not bot = top
    (forall (G : FinLTS L) (v : G.Vertex),
      (LTSSubfunctor.bot L).negation.pred G v) ∧
    -- Part 4: not top = bot
    (forall (G : FinLTS L) (v : G.Vertex),
      ¬ (LTSSubfunctor.top L).negation.pred G v) :=
  ⟨geometric_negation_collapse,
   geometric_double_negation_dense,
   LTSSubfunctor.negation_bot_is_top,
   LTSSubfunctor.negation_top_is_bot⟩

end RTS.PresheafTopos
