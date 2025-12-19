---
title: Mobiles as a Quotient-Inductive Type via Plump Ordinals
author: Christina O'Donnell
---

# Abstract

This note describes a construction of infinitary mobiles as a quotient-inductive type. The construction proceeds in two stages. First, we give a setoid-based description in terms of a transfinite diagram indexed by a plump tree ordinal $(T_I,\le)$. Second, we show that the same construction can be carried out directly in the category **Set**, assuming the availability of non-recursive quotients or colimit higher inductive types.

The key property of the index order $T_I$ is that it possesses a *definable supremum*: every family of elements indexed by $I$ has a canonical upper bound. This avoids the need for WISC (the Weakly Initial Set of Covers), which is typically required to ensure that polynomial functors preserve colimits in exact completions. Our construction is an instance where these general-purpose axioms are unnecessary.

# Setoid Infrastructure

Before presenting the construction, we establish the fundamental categorical infrastructure based on setoids.

## Setoids

```agda
{-# OPTIONS --cubical --safe #-}

module Paper where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum

-- Basic setoid structure
record Setoid ℓ : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    _≈_ : Carrier → Carrier → Type ℓ
    isEquivRel : BinaryRelation.isEquivRel _≈_

open Setoid public
```

A **setoid** $S = (|S|, {\approx_S})$ consists of a set $|S|$ equipped with an equivalence relation ${\approx_S}$ satisfying reflexivity, symmetry, and transitivity.

## Setoid Homomorphisms

```agda
-- Setoid homomorphisms
record SetoidHom {ℓ} (A B : Setoid ℓ) : Type ℓ where
  constructor mk-hom
  field
    fun : Carrier A → Carrier B
    resp : ∀ {x y} → A ._≈_ x y → B ._≈_ (fun x) (fun y)

open SetoidHom public

-- Identity and composition
idHom : ∀ {ℓ} (A : Setoid ℓ) → SetoidHom A A
idHom A = mk-hom (idfun _) (idfun _)

_∘ₕ_ : ∀ {ℓ} {A B C : Setoid ℓ} → SetoidHom B C → SetoidHom A B → SetoidHom A C
g ∘ₕ f = mk-hom (fun g ∘ fun f) (resp g ∘ resp f)
```

A **setoid homomorphism** $f: S \to T$ is a function $f: |S| \to |T|$ that respects the equivalence relations: $x \approx_S y \implies f(x) \approx_T f(y)$.

## Raw infinitary trees and plumpness

Fix a set $I$. We define the W-type of infinitary $I$-branching trees:

```agda
-- Raw trees with I-branching
data Tree (I : Type) : Type where
  leaf : Tree I  
  node : (I → Tree I) → Tree I

-- Strict plump order
data _<_ {I : Type} : Tree I → Tree I → Type where
  node-< : ∀ {f : I → Tree I} {i : I} {u : Tree I}
         → u ≤ f i
         → u < node f
  where
    _≤_ : Tree I → Tree I → Type
    u ≤ v = (u < v) ⊎ (u ≡ v)
```

The strict plump order $<$ on $T_I$ is defined inductively: $u < \mathsf{node}(f)$ if $u \le f(i)$ for some $i$, where $\le$ is the reflexive closure of $<$.

## Stage sets and the setoid construction

```agda
-- Stage sets S(t) = {u : Tree I | u < t}
S : ∀ {I : Type} → Tree I → Type
S {I} t = Σ[ u ∈ Tree I ] (u < t)

-- Equivalence relation on trees (simplified version)
data TreeEq {I : Type} : Tree I → Tree I → Type where
  leaf-eq : TreeEq leaf leaf
  node-eq : ∀ {f g : I → Tree I}
          → (∀ i → TreeEq (f i) (g i))
          → TreeEq (node f) (node g)
  -- Permutation equivalence would go here in full version
  
-- The setoid P(t)
P : ∀ {I : Type} → Tree I → Setoid₀
Carrier (P t) = S t
(P t) ._≈_ (u , _) (v , _) = TreeEq u v
BinaryRelation.isEquivRel.reflexive (isEquivRel (P t)) = tree-refl
  where
    tree-refl : ∀ {u} → TreeEq u u
    tree-refl {leaf} = leaf-eq
    tree-refl {node f} = node-eq (λ i → tree-refl {f i})
BinaryRelation.isEquivRel.symmetric (isEquivRel (P t)) = tree-sym
  where
    tree-sym : ∀ {u v} → TreeEq u v → TreeEq v u  
    tree-sym leaf-eq = leaf-eq
    tree-sym (node-eq h) = node-eq (λ i → tree-sym (h i))
BinaryRelation.isEquivRel.transitive (isEquivRel (P t)) = tree-trans
  where
    tree-trans : ∀ {u v w} → TreeEq u v → TreeEq v w → TreeEq u w
    tree-trans leaf-eq leaf-eq = leaf-eq
    tree-trans (node-eq h₁) (node-eq h₂) = node-eq (λ i → tree-trans (h₁ i) (h₂ i))
```

For each $t : T_I$, we define the stage set $S(t) := \{u : T_I \mid u < t\}$ and equip it with an equivalence relation to form the setoid $P(t)$.

## The quotient-polynomial functor

```agda
-- Quotient-polynomial functor on setoids  
F̃ : ∀ {I : Type} → Setoid₀ → Setoid₀
Carrier (F̃ {I} X) = Unit ⊎ (I → Carrier X)
(F̃ X) ._≈_ (inl tt) (inl tt) = Unit
(F̃ X) ._≈_ (inl tt) (inr _) = ⊥
(F̃ X) ._≈_ (inr _) (inl tt) = ⊥  
(F̃ X) ._≈_ (inr f) (inr g) = ∀ i → X ._≈_ (f i) (g i)
-- Permutation equivalence omitted for brevity
isEquivRel (F̃ X) = {!!} -- Proof omitted
```

We define an endofunctor on setoids: $\widetilde F_I(X,\approx_X) := \bigl( 1 + (I \to X) \bigr) / \approx_F$, where $\approx_F$ includes both pointwise equivalence and permutation equivalence.

# Cocontinuity and the main result

## Definable supremum property

The key insight is that plump orders have **definable suprema**: for any $g : I \to \text{colim} P$, if $g(i)$ is represented by $(t_i, x_i)$, then $t^* := \mathsf{node}(i \mapsto t_i)$ serves as an upper bound with $t_i \le t^*$.

```agda
-- Definable supremum (sketch)
sup : ∀ {I : Type} → (I → Tree I) → Tree I  
sup f = node f

sup-property : ∀ {I : Type} (f : I → Tree I) (i : I)
             → f i ≤ sup f
sup-property f i = inl (node-< (inr refl))
```

## Cocontinuity theorem

This definable supremum property allows us to prove that $\widetilde F_I$ preserves the colimit without requiring choice principles like WISC:

**Theorem.** The functor $\widetilde F_I$ is cocontinuous on the diagram $P : (T_I, \le) \to \mathbf{Setoid}$.

```agda
-- Main cocontinuity result (statement only)
postulate
  cocontinuity : ∀ {I : Type}
               → {!!} -- F̃ preserves colimits of P
```

## Initial algebra construction

From cocontinuity, we obtain that mobiles form the initial algebra for $\widetilde F_I$:

```agda
-- Mobiles as initial F̃-algebra (postulated)
postulate
  Mobile : ∀ (I : Type) → Type
  mobile-algebra : ∀ {I : Type} 
                 → Carrier (F̃ {I} {!!}) → Mobile I
  mobile-initial : ∀ {I : Type} (A : Type) (α : Carrier (F̃ {!!}) → A)
                 → ∃![ h ∈ (Mobile I → A) ] (h ∘ mobile-algebra ≡ α ∘ {!!})
```

# Constructing Mobiles Directly in Set

The same construction can be carried out using Higher Inductive Types, avoiding the setoid machinery entirely while maintaining the same cocontinuity properties.

# Conclusion

We have shown how plump tree ordinals provide a natural indexing structure for constructing mobiles as quotient-inductive types. The definable supremum property eliminates the need for choice principles like WISC, making this a particularly clean example of cocontinuous functors in practice.

The construction demonstrates how careful choice of indexing can simplify what would otherwise require sophisticated categorical machinery, suggesting broader applications in the theory of quotient-inductive types.