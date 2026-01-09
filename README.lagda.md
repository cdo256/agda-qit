```agda
module README where
```

# Agda QIT Development: Constructive Quotient Inductive Types

## Abstract

This repository develops mathematical foundations for Quotient Inductive Types (QITs) using setoid-based category theory, building toward proving cocontinuity for specific classes of QITs without choice principles.

## Key Innovation: Choice-Free Construction

This work aims to identify a class of QW-type signatures where cocontinuity can be proved without WISC (Weak Infinite Set of Choices). While Blass (1983) shows that, in general, cocontinuity-type statements for polynomial-like functors can require choice principles, and Fiore et al. (2022) use WISC to obtain cocontinuity for general QW-type signatures, we investigate whether mobiles might satisfy a locality/compactness property that sidesteps these barriers.

Our hypothesis is that mobiles exhibit sufficient structural constraints to avoid the choice-theoretic obstacles. We aim to work without WISC or global choice principles, avoiding assumptions beyond what is derivable from the ambient type theory.

If successful, this would demonstrate that choice-theoretic obstacles in QIT theory are not universal—specific QIT signatures might avoid them entirely.

## The Foundation: Type Theory and Relations

Every development needs its foundations. We start with the essential type-theoretic infrastructure that provides universe levels, the Box type for proposition lifting, and postulates for function extensionality and propositional extensionality:

```agda
open import QIT.Prelude
```

The `QIT.Prelude` provides the basic machinery that makes everything else possible. Most critically, it postulates the extensionality principles that are essential for reasoning about equality in a constructive setting.

Next, we need a solid foundation for working with relations. These modules establish the relational foundations that underpin the entire setoid-based approach:

```agda
open import QIT.Relation.Base
open import QIT.Relation.Binary
```

Rather than relying solely on Agda's built-in propositional equality, we work with user-defined equivalence relations that give us explicit control over what equality means in different contexts.

## Size Control: Plump Ordinals

One of the key insights from Fiore et al. (2022) is that QIT constructions require careful size management to ensure termination. We follow their approach using plump ordinals: well-founded ordinals with join operations that provide size bounds for controlling the depth of potentially infinite constructions:

```agda
open import QIT.Relation.Plump
```

Plump ordinals are not just any ordinals: they're specifically designed ordinals with join operations that provide the size bounds needed to build QITs in stages.

## Setoid-Based Category Theory

Instead of working with strict equality, we embrace the world of setoids: sets equipped with equivalence relations. Why setoids? Because QITs are fundamentally about quotients, identifying elements that should be considered the same even if they're not strictly equal.

We start with core setoid definitions that provide carriers with user-defined equivalence relations, then build homomorphisms that preserve equivalence relations between setoids:

```agda
open import QIT.Setoid.Base
open import QIT.Setoid.Hom
```

Building the categorical infrastructure over setoids:

```agda
open import QIT.Setoid.Iso
open import QIT.Setoid.Functor
open import QIT.Setoid.Algebra
```

These provide the categorical machinery we need: ways to relate setoids (homomorphisms), identify equivalent setoids (isomorphisms), transform entire setoid categories (functors), and work with algebraic structures that respect setoid equivalences.

## Diagrams: The Staging Infrastructure

Diagrams are crucial for organizing our staged constructions. They provide diagrams as functors from a preorder (viewed as a thin category) to setoids:

```agda
open import QIT.Setoid.Diagram
```

Diagrams let us organize families of setoids with transition maps between them, exactly what we need for building QITs stage by stage.

## Container Theory: Capturing Constructors

Containers provide a systematic way to represent the constructor part of inductive type signatures. A container signature separates shapes (constructors) from positions (argument arities):

```agda
open import QIT.Container.Base
open import QIT.Container.Functor
```

A container `(S ◁ P)` separates the shapes (what constructors you have) from the positions (how many arguments each constructor takes). From `(S,P)` we define the polynomial (container) functor `F`.

## The Main Event: Quotient W-Types

We need a way to state what equations should hold in our quotient. The equation module provides an expression language built from variables and constructors that lets us write down arbitrary equational constraints:

```agda
open import QIT.QW.Equation
```

A QIT signature packages together the container (which constructors you have) with the equations (which elements should be identified):

```agda
open import QIT.QW.Signature
```

The underlying syntax is generated by the W-type for the container before quotienting:

```agda
open import QIT.QW.W
```

Equations might require arbitrarily deep unfolding of constructors to check, so we can't build the quotient all at once. Instead, we build it in stages indexed by plump ordinals:

```agda
open import QIT.QW.Stage
```

What are we building toward? Algebras that satisfy all the equations in our signature:

```agda
open import QIT.QW.Algebra
```

How do we get from the stages to the final result? By taking the colimit: the categorical construction that glues together all the finite stages into the final infinite object:

```agda
open import QIT.QW.Colimit
```

We need to prove that our QIT constructors have the right universal properties. This requires proving that the relevant functors preserve colimits (they're *cocontinuous*):

```agda
open import QIT.QW.Cocontinuity
```

## The Test Case: Mobiles

The mobile signature captures a simple idea: tree structures where the ordering of branches doesn't matter. Given any set I, we get trees with I-branching nodes, but we quotient by all possible permutations of the branches:

```agda
open import QIT.Mobile.Base
```

Mobiles provide the mathematical foundation that makes choice-free cocontinuity possible. They capture essential symmetries through:

- Permutation symmetry: QIT equivalences respect reordering of branching structures
- Structural irrelevance: Leaf nodes are equivalent regardless of content
- Binding-aware equivalences: Proper handling of variable binding and renaming
- Constructive equivalences: All equivalence relations are defined constructively

The mobile cocontinuity proof represents the current frontier of the research program:

```agda
open import QIT.Mobile.Cocontinuity
```

The module `QIT.Mobile.Cocontinuity` attempts to constructively establish the crucial isomorphism $F(\text{Colim } D) \cong \text{Colim}(F \circ D)$ for the mobile functor $F$ and diagrams $D$.

## Technical Foundation

The choice-free approach relies on several key technical innovations:

- Setoid-based categorical semantics: Working in setoid categories provides better extensionality without requiring choice
- Size-based termination: Following Fiore et al. (2022), uses plump ordinals for well-founded recursion without choice axioms
- Constructive mobile equivalences: All equivalence relations are defined constructively
- Explicit isomorphism construction: Direct construction of cocontinuity isomorphisms without existential quantification

## Relationship to Existing Work

This formalization directly addresses fundamental limitations in QW-type theory:

- **Blass (1983) limitation**: Shows that, in general, cocontinuity-type statements for polynomial-like functors can require choice principles
- **Fiore et al. (2022) approach**: "Quotient inductive-inductive types" uses WISC for general QW-type cocontinuity
- **This work's contribution**: Investigates whether the mobile signature represents a specific class achieving choice-free cocontinuity
- **Theoretical significance**: Would demonstrate that choice-theoretic barriers are not universal

## Current Status and Research Challenges

### What Works
- Complete setoid-based categorical foundation
- Container theory with functorial properties
- Plump ordinal framework for size bounds
- Staged QW construction with colimits
- Mobile signature and forward cocontinuity direction

### Major Open Problems
- **Mobile cocontinuity reverse direction**: Construction of the backward isomorphism encounters substantial technical obstacles
- **Ordinal bound management**: Complex interactions between stage ordinals and permutation equations
- **Choice-freedom question**: Even if completed, whether this truly avoids all choice principles remains unclear

## Research Significance

Blass (1983) shows that, in general, cocontinuity for polynomial-like functors can require choice principles, and Fiore et al. (2022) use WISC for general QW-type signatures. If we can prove the mobile signature is cocontinuous without these assumptions, we'd show that the choice-theoretic barriers aren't universal: that there exist meaningful classes of QIT signatures that sidestep these fundamental obstacles entirely.

The forward direction of the cocontinuity isomorphism $F(\text{Colim } D) \to \text{Colim}(F \circ D)$ is successfully implemented. However, the reverse direction encounters substantial technical challenges involving ordinal bound management and permutation equivalence construction across different stages.

If successful, this would demonstrate that specific QW-types achieve cocontinuity without choice principles, potentially opening new directions in constructive type theory. The mobile example serves as a crucial test case for understanding the true boundaries of choice-free QIT theory.
