module QIT.Plump where

module Algebra where
  open import QIT.Plump.Algebra public

module Size where
  open import QIT.Plump.Size public

module W where
  open import QIT.Plump.W.Base public

module Generic where
  open import QIT.Plump.Properties public

module Extensional where
  module Base where
    open import QIT.Plump.Extensional.Base public

  module Properties where
    open import QIT.Plump.Extensional.Properties public
