
open import Data.Product using (_,_; _×_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_; []; foldr)
open import Data.List.All using (All; _∷_; [])
open import Data.List.Any using (Any; here; there; module Membership)
open import Relation.Binary using (Setoid)
open import Algebra.FunctionProperties using (Op₂)


open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.Folds where

  
