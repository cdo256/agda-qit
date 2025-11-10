{-# OPTIONS --prop --rewriting --show-irrelevant #-}
module README where

{- Agda code to accompany the paper:

Marcelo P. Fiore, Andrew M. Pitts and S. C. Steenkamp, "Quotients,
Inductive Types and Quotient Inductive Types", 2021.

Here we give the indexed version of quotient inductive types
(section 3.3 in the paper) straight away, rather than treating the
un-indexed version first (section 3.2)

-}

open import Prelude

-- Section 2. Type Theory
open import TypeTheory

-- Section 3. Indexed Containers and Equational Systems
open import IndexedContainersAndEquationalSystems

-- Section 4. Weakly Initial Sets of Covers
open import WeaklyInitialSetsOfCovers

-- Section 5. Size
open import WellFoundedRelations
open import Size
open import ColimitsOfSizedIndexedDiagrams

-- Section 6. Construction of QWI-Types
open import SizeIndexedStructure
open import FixedPointsAreQWITypes
open import ConstructionOfQWITypes

-- Section 7. Encoding QITs as QWI-Types
open import EncodingQITsAsQWITypes
