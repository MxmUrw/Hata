

module Verification.Conventions where

open import Verification.Conventions.Prelude hiding (𝑖 ; 𝑗 ; 𝑘 ; 𝑙 ; ′_′) public
open import Verification.Conventions.Postprelude public
open import Verification.Conventions.Meta public
open import Verification.Conventions.Meta2.Macros public
open import Verification.Conventions.Meta2.Structure public

variable
  n-𝑖𝑖 n-𝑗𝑗 n-𝑘𝑘 n-𝑙𝑙 : ℕ
  n-𝑖𝑖₂ n-𝑗𝑗₂ n-𝑘𝑘₂ n-𝑙𝑙₂ : ℕ
  n-𝑖𝑖₁ n-𝑗𝑗₁ n-𝑘𝑘₁ n-𝑙𝑙₁ : ℕ
  𝑖 : 𝔏 ^-𝒰 n-𝑖𝑖
  𝑗 : 𝔏 ^-𝒰 (n-𝑗𝑗)
  𝑘 : 𝔏 ^-𝒰 (n-𝑘𝑘)
  𝑙 : 𝔏 ^-𝒰 (n-𝑙𝑙)
  𝑖₂ : 𝔏 ^-𝒰 n-𝑖𝑖₂
  𝑗₂ : 𝔏 ^-𝒰 n-𝑗𝑗₂
  𝑘₂ : 𝔏 ^-𝒰 n-𝑘𝑘₂
  𝑙₂ : 𝔏 ^-𝒰 n-𝑙𝑙₂
  𝑖₁ : 𝔏 ^-𝒰 n-𝑖𝑖₁
  𝑗₁ : 𝔏 ^-𝒰 n-𝑗𝑗₁
  𝑘₁ : 𝔏 ^-𝒰 n-𝑘𝑘₁
  𝑙₁ : 𝔏 ^-𝒰 n-𝑙𝑙₁
  -- 𝑚 : 𝔏 ^-𝒰 (n-𝑚)
  -- 𝑛 : 𝔏 ^-𝒰 (n-𝑛)
  -- 𝑜 : 𝔏 ^-𝒰 (n-𝑜)
