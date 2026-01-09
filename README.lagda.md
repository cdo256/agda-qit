```agda
module README where
```

# Agda QIT Development: Constructive Quotient Inductive Types

This repository develops mathematical foundations for Quotient Inductive
Types (QITs) using setoid-based category theory, building toward proving
cocontinuity for specific classes of QITs without choice principles.

## Key Innovation: Choice-Free Construction

This work aims to establish that certain QW-types can achieve cocontinuity
without any choice principles—not WISC (Weak Infinite Set of Choices), not
AC (Axiom of Choice), not even unique choice. While Blass (1983) proved
that cocontinuity for arbitrary QW-types requires choice axioms, and Fiore
et al. (2022) represents the current state of the art using WISC, this work
investigates whether mobile categories can sidestep these fundamental
barriers.

If successful, this would be the first construction showing that specific
QW-types can sidestep the fundamental choice-theoretic barriers identified
by Blass (1983), advancing substantially beyond the current state of the
art which still requires WISC, and establishing that choice-theoretic
obstacles in QIT theory are not universal.

## The Foundation: Type Theory and Relations

We start with the essential
type-theoretic infrastructure that provides universe levels, the Box
type for proposition lifting, and crucially, postulates for function
extensionality and propositional extensionality:

```agda
open import QIT.Prelude
```

The `QIT.Prelude` provides the basic machinery that makes everything
else possible. Most critically, it postulates the extensionality
principles that are essential for reasoning about equality in a
constructive setting but cannot be proven from Agda's basic type
theory.

Next, we need a solid foundation for working with relations. These
modules establish the relational foundations that underpin the entire
setoid-based approach, providing basic relation definitions and the
key equivalence relation properties of reflexivity, symmetry, and
transitivity:

```agda
open import QIT.Relation.Base
open import QIT.Relation.Binary
```

Rather than relying solely on Agda's built-in propositional equality,
we work with user-defined equivalence relations that give us explicit
control over what "equality" means in different contexts.

## Size Control: Plump Ordinals

One of the key insights from Fiore et al. (2022) is that QIT
constructions require careful size management to ensure
termination. We follow their approach using plump
ordinals, which are well-founded ordinals with join operations that
provide size bounds for controlling the depth infinite QIT
constructions:
One of the key insights from Fiore et al. (2022) is that QIT constructions
require careful size management to ensure initiality. We follow their
approach using plump ordinals—well-founded ordinals with join operations
that provide size bounds for controlling infinite QIT constructions:

```agda
open import QIT.Relation.Plump
```

Plump ordinals are a weaker form of classical ordinals, which are only
'quasi-extensional'. They're specifically designed ordinals with join
operations that provide the size bounds needed to build QITs in
stages. Think of them as "depth complexity measures" that ensure our
constructions don't run away to infinity.

## Setoid-Based Category Theory

Instead of working with strict equality, we embrace the world of setoids—sets
equipped with equivalence relations. Why setoids? Because QITs are
fundamentally about quotients—identifying elements that should be considered
"the same" even if they're not strictly equal. Setoids make this explicit and
workable.

We start with core setoid definitions that provide carriers with
arbitrary equivalence relations, then build homomorphisms that
preserve equivalence relations between setoids:

```agda
open import QIT.Setoid.Base
open import QIT.Setoid.Hom
```

Building the categorical infrastructure over setoids, we need
isomorphisms with explicit inverses and bidirectional equivalence
preservation, structure-preserving functors between setoid categories,
and algebras satisfying equational laws over setoid functors:

```agda
open import QIT.Setoid.Iso
open import QIT.Setoid.Functor
open import QIT.Setoid.Algebra
```

These provide the categorical machinery we need: ways to relate
setoids (homomorphisms), identify equivalent setoids (isomorphisms),
transform entire setoid categories (functors), and work with algebraic
structures that respect setoid equivalences.

## Diagrams: The Staging Infrastructure

Diagrams are functors from a preorders to Setoid, they provide the basic
categorical structure that will be used to construct the colimit. We
use will use these to build QW types, taking the preorder to be the
plump order, and the diagram to be the category over stage sets.

```agda
open import QIT.Setoid.Diagram
```

Diagrams let us organize families of setoids with transition maps
between them, exactly what we need for building QITs at ordinal-bounded depth.

## Container Theory: Capturing Constructors

Containers provide a systematic way to represent the "constructor"
part of inductive type signatures. A container signature separates
shapes (constructors) from positions (argument arities), while setoid
functors induced by containers lift container operations to preserve
setoid equivalences:

```agda
open import QIT.Container.Base
open import QIT.Container.Functor
```

A container `(S ◁ P)` separates the "shapes" (what constructors you
have) from the "positions" (how many arguments each constructor
takes). This systematic approach makes it possible to work with
arbitrary inductive signatures uniformly.

## The Main Event: Quotient W-Types

Now we reach the core contribution: the construction of quotient
inductive types through staged approximations, following Fiore et
al. 2022.

We first define a QW signature, then define the semantic properties we
desire of a QW type, namely initiality over a QW algebra.

### Syntax of QW types

We need a way to state what equations should hold in our quotient. The
equation module provides an expression language built from variables
and constructors that lets us write down arbitrary equational
constraints:

```agda
open import QIT.QW.W
```

Equations might require arbitrarily deep unfolding of constructors to
check, so we can't build the quotient all at once. Instead, we build
it in stages indexed by plump ordinals, enforcing equations at each
stage while controlling the complexity of terms we need to consider:

```agda
open import QIT.QW.Equation
```

A QIT signature packages together the container (which constructors
you have) with the equations (which elements should be
identified). This cleanly separates the "syntax" from the "semantics"
of a quotient inductive type:

```agda
open import QIT.QW.Signature
```

### Semantics of QW types


Every QIT starts with an ordinary W-type—the free algebra generated by
the constructors without any equations imposed. This is our starting
point before we quotient out the unwanted distinctions:

```agda
open import QIT.QW.Stage
```

What are we building toward? Algebras that satisfy all the equations
in our signature. The initial such algebra (if it exists) gives us the
QIT we want:

```agda
open import QIT.QW.Colimit
```

The final piece: we need to prove that our QIT constructors have the
right universal properties. This requires proving that the relevant
functors preserve colimits—they're "cocontinuous":

```agda
open import QIT.QW.Algebra
```

How do we get from the stages to the final result? By taking the
colimit—the categorical construction that glues together all the
finite stages into the final infinite object:


The final piece: we need to prove that our QIT constructors have the right
universal properties. This requires proving that the container functor over the
signature preserves colimits on a Diagram.

```agda
open import QIT.QW.Cocontinuity
```

## The Test Case: Mobile Categories

All of this theory is developed in service of a specific goal: proving
that certain QITs can be constructed without choice principles. Mobile
categories provide our test case.

The mobile signature captures a beautifully simple idea: tree
structures where the ordering of branches doesn't matter. Given any
set I (finite or infinite), we get trees with I-branching nodes, but
we quotient by all possible permutations of the branches. The result
is "mobiles"—tree-like structures that can be freely rotated:

```agda
open import QIT.Mobile.Base
```

Mobile categories provide the mathematical foundation that makes choice-free
cocontinuity possible. They capture essential symmetries through:

- **Permutation symmetry**: QIT equivalences respect reordering of
  branching structures
- **Structural irrelevance**: Leaf nodes are equivalent regardless of
  content  
- **Binding-aware equivalences**: Proper handling of variable binding and
  renaming
- **Constructive equivalences**: All equivalence relations are decidable
  and constructively defined

This is where the rubber meets the road. The cocontinuity proof for mobile
categories represents the current frontier of the research program. Success
here would demonstrate that at least some QITs can be constructed without
any choice principles—not WISC (Weak Infinite Set of Choices), not AC
(Axiom of Choice), not even unique choice:

```agda
open import QIT.Mobile.Cocontinuity
```

The module `QIT.Mobile.Cocontinuity` attempts to constructively establish
the crucial isomorphism F(Colim D) ≅ Colim(F ∘ D) for mobile functors F
and diagrams D.

## Technical Foundation

The choice-free approach relies on several key technical innovations:

- **Setoid-based categorical semantics**: Working in setoid categories
  provides better extensionality without requiring choice
- **Size-based termination**: Following Fiore et al. (2022), uses plump
  ordinals for well-founded recursion without choice axioms
- **Constructive mobile equivalences**: All equivalence relations are
  decidably constructible
- **Explicit isomorphism construction**: Direct construction of cocontinuity
  isomorphisms without existential quantification

## Relationship to Existing Work

This formalization directly addresses fundamental limitations in QW-type
theory:

- **Blass (1983) limitation**: Proved impossibility of cocontinuity for
  arbitrary QW-types without choice
- **Fiore et al. (2022) approach**: Current state of the art using WISC for
  general QW-type cocontinuity
- **This work's contribution**: Investigates whether mobile categories
  represent a specific class of QW-types achieving choice-free cocontinuity
- **Theoretical significance**: Would demonstrate that choice-theoretic
  barriers are not universal—specific QIT signatures might avoid them
  entirely

## Current Status and Research Challenges

### What Works
- ✅ Complete setoid-based categorical foundation
- ✅ Container theory with functorial properties  
- ✅ Plump ordinal framework for size bounds
- ✅ Staged QW construction with colimits
- ✅ Mobile signature and forward cocontinuity direction

### Major Open Problems
- ⚠️ **Mobile cocontinuity reverse direction**: Construction of the backward
  isomorphism encounters substantial technical obstacles
- ⚠️ **Ordinal bound management**: Complex interactions between stage
  ordinals and permutation equations
- ❓ **Choice-freedom question**: Even if completed, whether this truly
  avoids all choice principles remains unclear

## Research Significance

Why does this matter? Blass (1983) proved that cocontinuity for arbitrary
QW-types requires choice axioms, and Fiore et al. (2022) represents the
current state of the art using WISC. If we can prove mobile categories are
cocontinuous without any choice principles, we'd show that the
choice-theoretic barriers aren't universal—that there exist meaningful
classes of QIT signatures that sidestep these fundamental obstacles
entirely.

**Current Status**: The forward direction of the cocontinuity isomorphism
F(Colim D) → Colim(F ∘ D) is successfully implemented. However, the reverse
direction encounters substantial technical challenges involving ordinal
bound management and permutation equivalence construction across different
stages. Whether these obstacles can be overcome, or whether they indicate
that choice principles are unavoidable even for mobile categories, remains
an open question at the heart of this research program.

If successful, this would demonstrate that specific QW-types achieve
cocontinuity without choice principles, potentially opening new directions
in constructive type theory. However, the technical challenges encountered
suggest that choice-theoretic obstacles may be more fundamental than
initially hoped. The mobile example serves as a crucial test case for
understanding the true boundaries of choice-free QIT theory.

This literate Agda development provides both the mathematical foundations
and the concrete test case needed to explore the boundaries of choice-free
QIT theory.
