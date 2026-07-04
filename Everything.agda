module Everything where

-- Changes:
--  - QIT.Prelude.Universe: Export universe variables.
--  - QIT.Prelude.Logic: Rename intro and elim rules.

-- Base
import QIT.Prelude.Universe
import QIT.Prelude.Truncation
import QIT.Prelude.Types
import QIT.Prelude.Logic
import QIT.Prelude.Identity
import QIT.Prelude.HLevel
import QIT.Prelude.Axiom
import QIT.Prelude.Decidability
import QIT.Prelude

import QIT.Types
import QIT.HLevel
import QIT.Logic
import QIT.Prop

-- Relations
import QIT.Relation.Base
import QIT.Relation.Binary
import QIT.Relation.IndexedBinary
import QIT.Relation.Subset
import QIT.Relation.Plump
import QIT.Relation.Nullary
import QIT.Relation.Finite
import QIT.Relation.WellFounded
import QIT.Relation.BarInduction
import QIT.Relation.SetQuotient
import QIT.Relation.Ordinal
import QIT.Relation.Properties
import QIT.Relation.WISC
import QIT.Relation

import QIT.Bool
import QIT.List
import QIT.Maybe
import QIT.Nat
import QIT.Fin.Base
import QIT.Fin.Properties

-- Set
import QIT.Function.Base
import QIT.Identity
import QIT.Logic
import QIT.Set.Base
import QIT.Set.Bijection
-- import QIT.Set.Cantor

-- Algebra
import QIT.Algebra.Base
import QIT.Algebra.Lift
import QIT.Algebra.Properties
import QIT.Algebra

-- Category
import QIT.Category.Base
import QIT.Category.Strict
import QIT.Category.SetoidEnriched
import QIT.Category.Morphism
import QIT.Category.Equivalence
import QIT.Category.Slice
import QIT.Category.Initial
import QIT.Category.Terminal

-- Category of Setoids
import QIT.Setoid.Base
import QIT.Setoid.Indexed
import QIT.Setoid.Hom
import QIT.Setoid.Iso
import QIT.Setoid.Sigma
import QIT.Setoid.Properties
import QIT.Setoid.IndexedQuotient
import QIT.Setoid.Algebra.Base
import QIT.Setoid.Algebra.Lift
import QIT.Setoid.Quotient
import QIT.Setoid

-- Specific Categories
import QIT.Category.Discrete
import QIT.Category.Preorder
import QIT.Category.Set
import QIT.Category.Setoid
import QIT.Category.FamilyOfSetoids

-- Container
import QIT.Container.Base
import QIT.Container.Functor
import QIT.Container.Indexed
import QIT.Container.StrictFunctor
import QIT.Container.Properties

-- Functor
import QIT.Functor.Base
import QIT.Functor.Properties
import QIT.Functor.NatTrans
import QIT.Functor.Diagram
import QIT.Functor.Quotient

-- Colimits
import QIT.Colimit.Base
import QIT.Colimit.Properties
import QIT.Colimit

-- QW type definition
import QIT.QW.W
import QIT.QW.Equation
import QIT.QW.Signature
import QIT.QW.Plump
import QIT.QW.Subclasses
import QIT.QW.Algebra
import QIT.QW.Stage
import QIT.QW.Diagram
import QIT.QW.Locality
import QIT.QW.Cocontinuity
import QIT.QW.Cocontinuity.FromDepthPreservation
import QIT.QW

-- Plump ordinals
import QIT.Plump.Algebra
import QIT.Plump.W
import QIT.Plump.Size
import QIT.Plump.Properties
import QIT.Plump

-- Topology
-- import QIT.Topology.Base
-- import QIT.Topology.Subset
-- import QIT.Topology.Constructions
-- import QIT.Topology.Category
-- import QIT.Topology.BishopReals
-- import QIT.Topology.Examples

-- -- Extended Type Theories
-- import QIT.IIT.Base
-- import QIT.IIT.Cont1
-- -- import QIT.IIT.Codes -- incomplete
-- -- import QIT.QIIT -- very incomplete
-- import QIT.KKA2019.Syntax
-- import QIT.KK2020.Level
-- import QIT.KK2020.Syntax

-- -- -- Examples
-- import QIT.Examples.Mobile.Base
-- -- import QIT.Examples.Mobile.Cocontinuity
-- -- import QIT.Examples.CauchyReals
-- import QIT.Examples.ConTy.Direct
-- import QIT.Examples.ConTy.DirectWeaklyTaggedEquiv
-- import QIT.Examples.ConTy.DisplayedReduction
-- import QIT.Examples.ConTy.Erased
-- import QIT.Examples.ConTy.ErasedElim
-- import QIT.Examples.ConTy.ErasedRec
-- import QIT.Examples.ConTy.Iterated
-- import QIT.Examples.ConTy.MutualProjection
-- import QIT.Examples.ConTy.QW
-- import QIT.Examples.ConTy.Tagged
-- import QIT.Examples.ConTy.TaggedWeaklyTaggedEquiv
-- import QIT.Examples.ConTy.WeaklyTagged
-- import QIT.Examples.ConTy
-- import QIT.Examples.CyclicList
-- import QIT.Examples.DoublyLinkedList
-- import QIT.Examples.HoleList
-- import QIT.Examples.Int
-- import QIT.Examples.ListBag
-- import QIT.Examples.Nat
-- import QIT.Examples.PartialityMonad.Combined
-- import QIT.Examples.PartialityMonad.Direct
-- import QIT.Examples.PartialityMonad.DirectAlgebra
-- import QIT.Examples.PartialityMonad.Erased
-- import QIT.Examples.PartialityMonad.ErasedW
-- import QIT.Examples.PartialityMonad.Flat
-- import QIT.Examples.PartialityMonad.MutualAlgebra
-- import QIT.Examples.PartialityMonad.MutualDirectEquiv
-- import QIT.Examples.PartialityMonad
-- import QIT.Examples.PartialityMonad.QW
-- import QIT.Examples.PartialityMonad.W1EquivDirect
-- import QIT.Examples.PartialityMonad.WellFormed
-- import QIT.Examples.PartialityMonad.WellFormedW
-- import QIT.Examples.Plump.Properties
-- import QIT.Examples.Queue
-- -- import QIT.Examples.RotTree
-- -- import QIT.Examples.SGL
-- import QIT.Examples.T
-- import QIT.Examples.Trunc
-- -- import QIT.Examples.WFTree
-- -- import QIT.Examples.Lambda
-- -- import QIT.Examples.Surreal
