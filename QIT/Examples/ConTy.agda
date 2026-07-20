{-# OPTIONS --allow-unsolved-metas #-}
open import QIT.Prelude

module QIT.Examples.ConTy where

-- Algebras Categories
import QIT.Examples.ConTy.Direct
import QIT.Examples.ConTy.Tagged
import QIT.Examples.ConTy.WeaklyTagged

-- Conversion functors
import QIT.Examples.ConTy.DirectToWeaklyTaggedLarge
import QIT.Examples.ConTy.WeaklyTaggedToDirect

-- Equivalence (WIP)
-- import QIT.Examples.ConTy.DirectWeaklyTaggedEquiv
