open import QIT.Prelude

module QIT.Relation where

open import QIT.Relation.Base public

import QIT.Relation.Binary
module Binary = QIT.Relation.Binary

import QIT.Relation.IndexedBinary
module IndexedBinary = QIT.Relation.IndexedBinary

-- FIXME: Cyclic dependency.
-- import QIT.Relation.Plump
-- module Plump = QIT.Relation.Plump

import QIT.Relation.Subset
module Subset = QIT.Relation.Subset
