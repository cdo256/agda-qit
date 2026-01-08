{-# OPTIONS --allow-unsolved-metas #-}
module Everything where

-- Base
import QIT.Prelude

-- Relations
import QIT.Relation.Base
import QIT.Relation.Binary
import QIT.Relation.IndexedBinary
import QIT.Relation.Subset
import QIT.Relation.Plump
import QIT.Relation.Tests
import QIT.Relation

-- Category of Setoids
import QIT.Setoid.Base
import QIT.Setoid.Indexed
import QIT.Setoid.Hom
import QIT.Setoid.Iso
import QIT.Setoid.Sigma
import QIT.Setoid.Functor
import QIT.Setoid.Algebra
import QIT.Setoid

-- Containers
import QIT.Container.Base
import QIT.Container.Functor

-- QW type definition
import QIT.QW.Equation
import QIT.QW.Diagram
import QIT.QW.Colimit
import QIT.QW.Cocontinuity

-- Stage Sets
import QIT.Stage.Base
import QIT.Stage.Homo
-- import QIT.Stage.Hetero

-- Mobile construction 
import QIT.Mobile.Base
-- import QIT.Mobile.Stage.Hetero
import QIT.Mobile.Stage.Homo
import QIT.Mobile.Diagram
import QIT.Mobile.Functor
-- import QIT.Mobile.Cocontinuity
