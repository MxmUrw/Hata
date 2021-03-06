{-# OPTIONS --cubical #-}

--------------------------------------------------------------------------------
--= Categories
--------------------------------------------------------------------------------

module Verification.Old.Core.Category where

-- | In this chapter we define categories and related structures, since we are
-- going to use them as a language in the main part.
open import Verification.Old.Core.Category.Definition public

open import Verification.Old.Core.Category.EpiMono public
open import Verification.Old.Core.Category.Instance.Type public
open import Verification.Old.Core.Category.Instance.Cat public
open import Verification.Old.Core.Category.Instance.Set.Definition public
open import Verification.Old.Core.Category.Instance.Set.Equalizers public
open import Verification.Old.Core.Category.Instance.Set.Products public
open import Verification.Old.Core.Category.Quiver public
open import Verification.Old.Core.Category.FreeCategory public


