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
    prd  : (psym : Pred) → (Fin (arityP psym) → Term) → Atom
    eqn  : Term → Term                                → Atom

  data Conclusion : Set where
    definite : Atom → Conclusion
    goal     :        Conclusion

  Horn : Set
  Horn = List Atom × Conclusion

  variable
    a a'      : Atom
    c d       : Conclusion
    p q r     : List Atom
    s t s'  : Term
    A         : Term → Atom   -- A[l] ≡ A l

  Sub : Set
  Sub = Fin flexible → Term

  subT : Sub → Term → Term
  subT σ (rvar x)      = rvar x
  subT σ (fvar x)      = σ x
  subT σ (fun fsym ts) = fun fsym (λ x → subT σ (ts x))

  subA : Sub → Atom → Atom
  subA σ (prd psym ts) = prd psym λ x → subT σ (ts x)
  subA σ (eqn x    y ) = eqn (subT σ x) (subT σ y)

  subC : Sub → Conclusion → Conclusion
  subC σ (definite x) = definite (subA σ x)
  subC σ goal         = goal
  
  data HVCC : Horn → Set where
    -- elim clause
    res    : HVCC (p , definite a)
           → HVCC (a' ∷ q , c)
           → (σ : Sub) → subA σ a ≡ subA σ a'
           → r ≡ List.map (subA σ) p ++ List.map (subA σ) q
           → d ≡ subC σ c
           → HVCC (r , d)
    sup·l  : HVCC (p , definite (eqn s t)) 
           → HVCC (A s' ∷ q , c)
           → (σ : Sub) → subT σ s ≡ subT σ s'
           → r ≡ A t ∷ List.map (subA σ) p ++ List.map (subA σ) q
           → d ≡ subC σ c
           → HVCC (r , d)
    sup·r  : HVCC (p , definite (eqn s t))
           → HVCC (q , definite (A s'))
           → (σ : Sub) → subT σ s ≡ subT σ s'
           → r ≡ List.map (subA σ) p ++ List.map (subA σ) q
           → d ≡ subC σ c
           → HVCC (r , d)
    
    -- elim atom
    fac    : HVCC (a ∷ a' ∷ p , c)
           → (σ : Sub) → subA σ a ≡ subA σ a'
           → r ≡ List.map (subA σ) (a ∷ p) 
           → d ≡ subC σ c
           → HVCC (r , d)
    eq·res : HVCC ((eqn s t) ∷ p , c)
           → (σ : Sub) → subT σ s ≡ subT σ t
           → r ≡ List.map (subA σ) p
           → d ≡ subC σ c
           → HVCC (r , d)

  record Structure : Set₁ where
    field
      D    : Set
      funI : (f : Fun)  → (Fin (arityF f) → D) → D
      prdI : (p : Pred) → (Fin (arityP p) → D) → Set

  module Semantics (M  : Structure)
                   (ρr : Fin rigid    → Structure.D M)
                   (ρf : Fin flexible → Structure.D M) where
    open Structure M

    ⟦_⟧T : Term → D
    ⟦ rvar x      ⟧T = ρr x
    ⟦ fvar x      ⟧T = ρf x
    ⟦ fun fsym ts ⟧T = funI fsym (λ i → ⟦ ts i ⟧T)

    ⟦_⟧A : Atom → Set
    ⟦ prd psym ts ⟧A = prdI psym (λ i → ⟦ ts i ⟧T)
    ⟦ eqn x    y  ⟧A = x ≡ y

    ⟦_⟧LA : List Atom → Set → Set
    ⟦ []    ⟧LA X = X
    ⟦ a ∷ p ⟧LA X = ⟦ a ⟧A → ⟦ p ⟧LA X

    ⟦_⟧H : Horn → Set
    ⟦ p , definite a ⟧H = ⟦ p ⟧LA ⟦ a ⟧A
    ⟦ p , goal       ⟧H = ⟦ p ⟧LA ⊥

    toAgda : HVCC (p , c) → ⟦ p , c ⟧H
    toAgda (res    p→a   a'∧q→c  σ σa≡σa' σp∧σq     σc)  = {!   !}
    toAgda (sup·l  p→s=t as'∧q→c σ σs≡σs' σat∧σp∧σq σc)  = {!   !}
    toAgda (sup·r  p→s=t q→as'   σ σs≡σs' σp∧σq     σat) = {!   !}
    toAgda (fac    a∧a'∧p→c      σ σa≡σa' σa∧σp     σc)  = {!   !}
    toAgda (eq·res s=t∧p→c       σ σs≡σt  σp        σc)  = {!   !}
