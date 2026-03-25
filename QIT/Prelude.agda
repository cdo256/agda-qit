module QIT.Prelude where

-- Foundational definitions and type theory concepts for the QIT development.
-- Provides constructive foundations without choice principles, careful universe
-- level management, and propositional truncation for proof-irrelevant statements.

-- Universe level management - crucial for building large type constructions.
open import Level public using (Level; _⊔_; Lift; lift; lower)
  renaming (suc to lsuc; zero to ℓ0)

-- Propositional equality - the basic definitional equality in Agda.
-- import Relation.Binary.PropositionalEquality
-- module ≡ = Relation.Binary.PropositionalEquality
-- open ≡ public using (_≡_; _≢_; subst) public

-- import Relation.Binary.HeterogeneousEquality 
-- module ≣ = Relation.Binary.HeterogeneousEquality 
-- open ≣ public using () renaming (_≅_ to _≣_)

-- Empty type - represents logical falsehood and impossible cases.
import Data.Empty
module ⊥ = Data.Empty
open ⊥ using (⊥) public

-- Product types - both dependent (Σ) and non-dependent (_×_).
import Data.Product
module × = Data.Product
open × using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂) public

import Agda.Builtin.Sigma
{-# DISPLAY Agda.Builtin.Sigma.Σ.fst = proj₁ #-}
{-# DISPLAY Agda.Builtin.Sigma.Σ.snd = proj₂ #-}

-- Sum types - represents disjoint union and logical disjunction.
import Data.Sum
module ⊎ = Data.Sum
open ⊎ using (_⊎_; inj₁; inj₂) public

open import Data.Unit hiding (_≟_) public

-- Unit type at arbitrary universe levels.
⊤* : ∀ {ℓ} → Set ℓ
⊤* {ℓ} = Lift ℓ ⊤

-- Empty type at arbitrary universe levels.
⊥* : ∀ {ℓ} → Set ℓ
⊥* {ℓ} = Lift ℓ ⊥ 

