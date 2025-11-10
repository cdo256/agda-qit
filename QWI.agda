module QWI where

{-
Here we give the indexed version of quotient inductive types,
QWI-types (section 3.3 in the paper) and their construction from
quotient and inductive types using the WISC axiom
-}

-- Section 3. Indexed Polynomial Functors and Equational Systems
open import QWI.IndexedPolynomialFunctorsAndEquationalSystems

-- Section 5. Size
open import QWI.Size
open import QWI.ColimitsOfSizedIndexedDiagrams

-- Section 6. Construction of QWI-Types
open import QWI.SizeIndexedStructure
open import QWI.FixedPointsAreQWITypes
open import QWI.ConstructionOfQWITypes

-- Section 7. Encoding QITs as QWI-Types
open import QWI.EncodingQITsAsQWITypes
