{-# OPTIONS --allow-unsolved-metas #-}
module Everything where

-- Base
import QIT.Prelude

-- Relations
import QIT.Relation
import QIT.Relation.Base
import QIT.Relation.Binary
import QIT.Relation.IndexedBinary
import QIT.Relation.Subset
import QIT.Relation.Plump
import QIT.Relation.Tests

-- Setoids
import QIT.Setoid
import QIT.Setoid.Base
import QIT.Setoid.Functor
import QIT.Setoid.Hom
import QIT.Setoid.Indexed
import QIT.Setoid.Iso
import QIT.Setoid.Sigma

-- Containers & QIT Core
import QIT.Container
import QIT.ContainerFunctor
import QIT.SystemOfEquations
import QIT.QW

-- Category Theory
import QIT.Diagram
import QIT.Colimit
import QIT.Cocontinuity

-- Stages
import QIT.Stage.Base
import QIT.Stage.Homo
import QIT.Stage.Hetero

-- Mobile Logic
-- import QIT.Mobile.Base
-- import QIT.Mobile.Cocontinuity
-- import QIT.Mobile.Diagram
-- import QIT.Mobile.Functor
-- import QIT.Mobile.HeterogeneousDiagram
-- import QIT.Mobile.Stage.Hetero
-- import QIT.Mobile.Stage.Homo

-- -- Examples
-- import QIT.Examples.BoundedRational
-- import QIT.Examples.HoleList
