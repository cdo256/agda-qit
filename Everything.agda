module Everything where

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

-- Propositions
import QIT.Logic
import QIT.Prop.Base
import QIT.Prop.Data
import QIT.Prop.Properties
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
import QIT.Relation.WISC
import QIT.Relation

import QIT.Nat
import QIT.Fin.Base
import QIT.Fin.Properties

import QIT.Function.Base
import QIT.Identity
import QIT.Prop.Base
import QIT.Logic
import QIT.Prop.Data
import QIT.Prop.Properties
import QIT.Prop
import QIT.Set.Base
import QIT.Set.Bijection

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

-- Functor
import QIT.Functor.Base
import QIT.Functor.Properties
import QIT.Functor.NatTrans

-- Algebra
import QIT.Algebra.Base
import QIT.Algebra.Properties
import QIT.Algebra.Lift
import QIT.Algebra

-- Containers
import QIT.Container.Base
import QIT.Container.Functor
import QIT.Container.StrictFunctor
import QIT.Container.Indexed
import QIT.Container.Properties

-- Plump ordinals
import QIT.Plump

-- QW type definition
import QIT.QW.W
import QIT.QW.Equation
import QIT.QW.Signature
import QIT.QW.Algebra
import QIT.QW.Stage
import QIT.QW.StageColimit
import QIT.QW.Colimit
import QIT.QW.Locality
import QIT.QW.Cocontinuity
import QIT.QW

-- -- Extended Type Theories
-- import QIT.IIT.Cont1
-- -- import QIT.IIT.Codes -- incomplete
-- -- import QIT.QIIT -- very incomplete

-- -- Kaposi-Kovacs-Altenkirch Syntax
-- import QIT.KKA2019.Syntax
-- -- import QIT.KK2020.Level
-- -- -- import QIT.KK2020.Syntax -- incomplete

-- -- -- Examples
-- import QIT.Examples.Mobile.Base
-- -- import QIT.Examples.Mobile.Cocontinuity
-- -- import QIT.Examples.CauchyReals
-- import QIT.Examples.ConTy
-- import QIT.Examples.HoleList
-- import QIT.Examples.ListBag
-- import QIT.Examples.PartialityMonad
-- -- import QIT.Examples.RotTree
-- -- import QIT.Examples.SGL
-- import QIT.Examples.T
-- import QIT.Examples.Trunc
-- -- import QIT.Examples.WFTree
-- -- import QIT.Examples.Lambda
-- -- import QIT.Examples.Surreal
