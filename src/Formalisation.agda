open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.List as List
open import Data.Fin
open import Relation.Binary.PropositionalEquality

module Formalisation where

module _
  (Fun Pred : Set) (arityF : Fun → ℕ) (arityP : Pred → ℕ)
  (rigid flexible : ℕ) where

  data Term : Set where
    rvar : Fin rigid                                 → Term
    fvar : Fin flexible                              → Term
    fun  : (fsym : Fun) → (Fin (arityF fsym) → Term) → Term

  data Atom : Set where
    rel : (psym : Pred) → (Fin (arityP psym) → Term) → Atom
    eqn : Term → Term                                → Atom

  data Conclusion : Set where
    definite : Atom → Conclusion
    goal     :        Conclusion

  Horn : Set
  Horn = List Atom × Conclusion

  variable
    a a'  : Atom
    c d   : Conclusion
    p q r : List Atom

  Sub : Set
  Sub = Fin flexible → Term

  subT : Sub → Term → Term
  subT σ (rvar x)      = rvar x
  subT σ (fvar x)      = σ x
  subT σ (fun fsym ts) = fun fsym (λ x → subT σ (ts x))

  subA : Sub → Atom → Atom
  subA = {!   !}

  subC : Sub → Conclusion → Conclusion
  subC = {!   !}

  data HVCC : Horn → Set where
    res : HVCC (p , definite a)
        → HVCC (a' ∷ q , c)
        → (σ : Sub) → subA σ a ≡ subA σ a'
        → r ≡ List.map (subA σ) p ++ List.map (subA σ) q
        → d ≡ subC σ c
        → HVCC (r , d)

  ⟦_⟧A : Atom → Set
  ⟦_⟧A = {!   !}

  ⟦_⟧LA : List Atom → Set → Set
  ⟦ []    ⟧LA X = X
  ⟦ a ∷ p ⟧LA X = ⟦ a ⟧A → ⟦ p ⟧LA X

  ⟦_⟧H : Horn → Set
  ⟦ p , definite a ⟧H = ⟦ p ⟧LA ⟦ a ⟧A
  ⟦ p , goal       ⟧H = ⟦ p ⟧LA ⊥

  toAgda : HVCC (p , c) → ⟦ p , c ⟧H
  toAgda = {!   !}
