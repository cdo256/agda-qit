module README where
{-
  Agda code to accompany the paper:

  Marcelo P. Fiore, Andrew M. Pitts and S. C. Steenkamp,
  "Quotients, Inductive Types and Quotient Inductive Types"
  https://arxiv.org/abs/2101.02994

  Agda code at https://doi.org/10.17863/CAM.77483

  The code has been checked with Agda version 2.6.2

  The files use a common set of options given in the file flags.agda-lib:

  --with-K
    (we make use of Streicher's Axiom K, or equivalently the
    Uniqueness of Identity Proofs (UIP), via the more liberal, dafault
    version of Agda's dependent patern matching)

  --prop
    (we make use of Agda’s built-in predicative universes of
    definitionally proof-irrelevant propositions)

  --rewriting
    (we use Agda's facility for user-defined extensions of its
    evaluation relation with new computation rules, in order to make
    the computation rules for postulated quotient types be
    definitional equalities)

  We begin with a small library of common definitions:
-}
open import Prelude
{-
  Next we give some postulates for propositional extensionaliy,
  Hofmann-style quotient types and the axiom of unique choice, as
  described in section 2 (Type Theory) of the paper:
-}
open import TypeTheory
{-
  We also rely on some standard facts about well-founded induction and
  recursion (deriving the latter from the former via a use of Unique
  Choice -- see Proposition 5.3 in the paper):
-}
open import WellFoundedRelations
{-
  We make use of (an indexed version of) the Weakly Initial Set of
  Covers (WISC) Axiom, as discussed in section 4 of the paper:
-}
open import WeaklyInitialSetsOfCovers
{-
  Now there are two branches: QW and QWI

    The QW branch treats the construction of QW-types, as described in
    the paper.
-}
open import QW
{-
    The QWI branch generalises the construction to the case of the
    indexed version of QW-types, the QWI-types described in section 3.3
    of the paper.
-}
open import QWI
