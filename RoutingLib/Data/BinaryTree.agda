open import Data.List using (List; []; _∷_; _++_; [_])
open import Relation.Binary using (Rel; DecTotalOrder)
open import Relation.Nullary using (yes; no)
open import Function using (flip)

module RoutingLib.Data.BinaryTree where

  data BinaryTree {a} (A : Set a) : Set a where
    leaf : BinaryTree A
    branch : A → BinaryTree A → BinaryTree A → BinaryTree A

  preorder : ∀ {a} {A : Set a} → BinaryTree A → List A
  preorder leaf           = []
  preorder (branch x l r) = [ x ] ++ preorder l ++ preorder r

  inorder : ∀ {a} {A : Set a} → BinaryTree A → List A
  inorder leaf           = []
  inorder (branch x l r) = inorder l ++ [ x ] ++ inorder r

  postorder : ∀ {a} {A : Set a} → BinaryTree A → List A
  postorder leaf           = []
  postorder (branch x l r) = postorder l ++ postorder r ++ [ x ]




  data All {a p} {A : Set a} (P : A → Set p) : BinaryTree A → Set a where
    leaf   : All P leaf
    branch : ∀ l r x → All P l → All P r → All P (branch x l r)

  data Rec {a p₁ p₂} {A : Set a} (_~ˡ_ : A → A → Set p₁) (_~ʳ_ : A → A → Set p₂) : BinaryTree A → Set a where
    leaf : Rec _~ˡ_ _~ʳ_ leaf
    branch : ∀ l r x → All (x ~ˡ_) l → All (x ~ʳ_) r → Rec _~ˡ_ _~ʳ_ l → Rec _~ˡ_ _~ʳ_ r  → Rec _~ˡ_ _~ʳ_ (branch x l r)



  module BinarySearchTree {a ℓ₁ ℓ₂} (decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂) where

    open DecTotalOrder decTotalOrder renaming (Carrier to A)

    record BST : Set a where
      constructor _,_
      field
        tree : BinaryTree A
        sorted : Rec _≤_ (flip _≤_) tree

    insert : A → BinaryTree A → BinaryTree A
    insert x leaf = branch x leaf leaf
    insert x (branch y l r) with x ≤? y
    ... | yes x≤y = branch y (insert x l) r
    ... | no  x≰y = branch y l (insert x r)
