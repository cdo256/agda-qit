```agda
module README where
```

# Agda QIT Development: Constructive Quotient Inductive Types

## Abstract

This repository develops mathematical foundations for Quotient Inductive
Types (QITs) using setoid-based category theory, including a concrete proof
of cocontinuity for mobile QITs without WISC.

## The Ambient Type Theory

We work in Agda with `--with-k` (K/UIP axiom) and `--prop` (proof-irrelevant
propositions). We postulate function extensionality for Set-valued functions
and propositional extensionality as needed.

Note that we develop QIT semantics externally via setoids; no quotient HITs
are assumed. To internalise as a Set-level quotient type, one would need
quotient/HIT postulates, but we do not pursue that here.

## Development Roadmap

The construction proceeds through several layers:

- Foundations: Essential infrastructure (Prelude, Relations)
- Setoid category theory: Explicit equivalence relations and categorical structures
- Size control: Plump ordinals for termination
- Diagrams and colimits: Staged construction framework  
- QW machinery: General quotient W-type construction
- Mobile test case: Cocontinuity proof for permutation-invariant trees

## The Foundation: Type Theory and Relations

Every development needs its foundations. We start with the essential
type-theoretic infrastructure that provides universe levels, the Box type
for proposition lifting, and the extensionality postulates:

```agda
open import QIT.Prelude
```

The `QIT.Prelude` provides the basic machinery that makes everything else
possible. Most critically, it postulates extensionality principles used
throughout the development, which are not derivable from Agda's core
intensional theory.

Next, we need a solid foundation for working with relations. These modules
establish the relational foundations that underpin the entire setoid-based
approach, providing basic relation definitions and the key equivalence
relation properties of reflexivity, symmetry, and transitivity:

```agda
open import QIT.Relation.Base
open import QIT.Relation.Binary
```

Rather than relying solely on Agda's built-in propositional equality, we
work with user-defined equivalence relations that give us explicit control
over what equality means in different contexts.

## Size Control: Plump Ordinals

One of the key insights from Fiore et al. (2022) is that QIT constructions
require careful size management to ensure termination. We follow their
approach using plump ordinals: W-types with a well-founded order that 
provide size bounds for controlling the depth of potentially infinite
constructions:

```agda
open import QIT.Relation.Plump
```

Plump ordinals are specifically designed ordinals with join operations that
provide the size bounds needed to build QITs in stages. Think of them as
complexity measures that ensure our constructions don't run away to
infinity.

## Setoid-Based Category Theory

This is where the mathematical heart of the development lives. Instead of
working with strict equality, we embrace the world of setoids: sets equipped
with equivalence relations. Why setoids? Because QITs are fundamentally
about quotients, identifying elements that should be considered the same
even if they're not strictly equal. Setoids make this explicit and
workable.

We start with core setoid definitions that provide carriers with
user-defined equivalence relations, then build homomorphisms that preserve
equivalence relations between setoids:

```agda
open import QIT.Setoid.Base
open import QIT.Setoid.Hom
```

Building the categorical infrastructure over setoids, we need isomorphisms
with explicit inverses and bidirectional equivalence preservation,
structure-preserving functors between setoid categories, and algebras
satisfying equational laws over setoid functors:

```agda
open import QIT.Setoid.Iso
open import QIT.Setoid.Functor
open import QIT.Setoid.Algebra
```

These provide the categorical machinery we need: ways to relate setoids
(homomorphisms), identify equivalent setoids (isomorphisms), transform
entire setoid categories (functors), and work with algebraic structures
that respect setoid equivalences.

## Diagrams: The Staging Infrastructure

Diagrams are crucial for organizing our staged constructions. They provide
diagrams as functors from a preorder (viewed as a thin category) to setoids:

```agda
open import QIT.Setoid.Diagram
```

Diagrams let us organize families of setoids with transition maps between
them: exactly what we need for building QITs stage by stage.

## Container Theory: Capturing Constructors

Containers provide a systematic way to represent the constructor part of
inductive type signatures. A container signature separates shapes
(constructors) from positions (argument arities):

```agda
open import QIT.Container.Base
open import QIT.Container.Functor
```

A container `(S ◁ P)` separates the shapes (what constructors you have)
from the positions (how many arguments each constructor takes). From
`(S,P)` we define the polynomial (container) functor `F`. Quotienting is
handled externally via stagewise setoids and colimits; the functor itself
is unchanged. This systematic approach makes it possible to work with
arbitrary inductive signatures uniformly.

## The Main Event: Quotient W-Types

Now we reach the core contribution: the construction of quotient inductive
types through staged approximations.

We need a way to state what equations should hold in our quotient. The
equation module provides an expression language built from variables and
constructors that lets us write down arbitrary equational constraints:

```agda
open import QIT.QW.Equation
```

A QIT signature packages together the container (which constructors you
have) with the equations (which elements should be identified). This
cleanly separates the syntax from the semantics of a quotient inductive
type:

```agda
open import QIT.QW.Signature
```

The underlying syntax is generated by the W-type for the container before
quotienting. This gives us the raw terms without any equations imposed:

```agda
open import QIT.QW.W
```

Here's the key insight: equations might require arbitrarily deep unfolding
of constructors to check, so we can't build the quotient all at once.
Instead, we build it in stages indexed by plump ordinals, enforcing
equations at each stage while controlling the complexity of terms we need
to consider:

```agda
open import QIT.QW.Stage
```

What are we building toward? Algebras that satisfy all the equations in our
signature. The initial such algebra (if it exists) gives us the QIT we
want:

```agda
open import QIT.QW.Algebra
```

How do we get from the stages to the final result? By taking the
colimit: the categorical construction that glues together all the finite
stages into the final infinite object:

```agda
open import QIT.QW.Colimit
```

We need to prove that our QIT constructors have the right universal
properties. This requires proving that the relevant functors preserve
colimits (they're *cocontinuous*):

```agda
open import QIT.QW.Cocontinuity
```

## The Test Case: Mobiles

We demonstrate the theory with a concrete example: the mobile QIT.

The mobile signature captures a simple idea: tree structures where the
ordering of branches doesn't matter. Given any set I (finite or infinite),
we get trees with I-branching nodes, but we quotient by reindexing under
all bijections I ↔ I. The result is mobiles: tree-like structures
that can be freely rotated:

```agda
open import QIT.Mobile.Base
```

The mobile cocontinuity proof provides a concrete test case where we avoid
WISC entirely:

```agda
open import QIT.Mobile.Cocontinuity
```

## Main Results

The module `QIT.Mobile.Cocontinuity` establishes:

*Definition*: The mobile functor `F` is *cocontinuous* for
plump-ordinal indexed diagrams `D` (i.e. functors from the plump preorder
to setoids), meaning there is a setoid isomorphism
`F (Colim D) ≅ Colim (F ∘ D)` with both inverses
(`linv`, `rinv`) proved.

This provides a concrete formalised example where cocontinuity is proved
without WISC (and no additional choice axioms).

## Technical Foundation

The construction relies on several key innovations:

- Size-based termination: Following Fiore et al. (2022), uses plump ordinals 
  for well-founded recursion without choice axioms
- Constructive mobile equivalences: All equivalence relations are defined 
  constructively
- Explicit isomorphism construction: Direct construction of cocontinuity 
  isomorphisms without existential quantification  
- Permutation locality: Mobile permutations have sufficient structural 
  constraints to avoid choice-theoretic obstacles

## Relationship to Existing Work

This formalization addresses fundamental limitations in QW-type theory:

- *Blass (1983)*: Shows that certain preservation principles entail 
  choice-like principles in broad settings. Our mobile case shows the
  obstruction is not universal.
- *Fiore et al. (2022)*: Quotient inductive-inductive types uses WISC for 
  general QW-type cocontinuity. We eliminate this requirement for the mobile
  case.
- *This work's contribution*: Shows the choice-theoretic obstruction is not
  universal by providing a concrete mobile case.

## Current Status

### What Has Been Achieved
- Complete setoid-based categorical foundation
- Container theory with functorial properties  
- Plump ordinal framework for size bounds
- Staged QW construction with colimits
- Mobile signature specification
- Forward cocontinuity direction: `F (Colim D) → Colim (F ∘ D)`
- Reverse cocontinuity direction: `Colim (F ∘ D) → F (Colim D)`
- Complete inverse proofs: Both `linv` and `rinv` verified

### Technical Details

The major technical hurdle was constructing the reverse direction
`ψ₀ : F (Colim D) → Colim (F ∘ D)` and proving it respects all equivalences.
Key insights that enabled the proof:

- Depth preservation: Equivalences in stages preserve ordinal depths
- Constructive bounds: Explicit ordinal bound construction for node cases
- Permutation coherence: Systematic handling of permutation equivalences
  across stages
- Stage embedding: Proper embedding of elements into appropriate stages
  with correct bound witnesses

## Research Significance

The success demonstrates that choice-theoretic obstacles in QIT theory are
not universal. There exist meaningful classes of QIT signatures that can be
handled in purely constructive mathematics without choice principles beyond
those derivable from type theory itself.

This opens several research directions: classification of other QIT
signatures that might achieve choice-free cocontinuity, extension to more
complex permutation-invariant structures, applications to practical proof
assistant implementation, and connections to homotopy type theory and
univalent foundations.

The techniques developed here provide a pathway for implementing mobile QITs
in constructive proof assistants without requiring choice axiom extensions
to the type theory.

## Technical Requirements and Usage

Dependencies:

- Agda 2.8.0.
- Agda standard library 2.3.

Dependencies are pinned by the Nix flake. A development environment is 
available via `flake.nix`.

To typecheck, run:

```bash
agda Everything.agda
```

Main theorem: `QIT.Mobile.Cocontinuity.cocontinuous`

This literate Agda development provides both the mathematical foundations
and the concrete proof that choice-free QIT theory is possible for
meaningful classes of quotient inductive types.
