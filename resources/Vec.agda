{-# OPTIONS --without-K #-}
--
-- NOTE: no --safe here.  That flag rejects `postulate` outright (you can
-- postulate ⊥ with it, so it is exactly what --safe is meant to catch),
-- and this development is an abstract theory given by postulates.  For a
-- --safe-clean version of the same proof, see VecSafe.agda, which packs
-- the signature into a record parameter instead.
--

module Vec where

open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; cong; subst; module ≡-Reasoning)

infixl 6 _+_
infix  8 -_

------------------------------------------------------------------------
-- 1. The signature and the three axioms (paper, Section 3.1)
--
-- A rudimentary theory of vector spaces: a zero vector, addition, and
-- negation, with associativity, left neutrality of zero, and left
-- inverse.  These are `postulate`s rather than definitions because the
-- theory is abstract -- which is also why proof search has nothing to
-- unfold and must reason purely equationally.

postulate
  V   : Set
  ze  : V
  _+_ : V → V → V
  -_  : V → V

  neutl : ∀ u → ze + u ≡ u
  negl  : ∀ u → (- u) + u ≡ ze
  assoc : ∀ u v w → (u + v) + w ≡ u + (v + w)

------------------------------------------------------------------------
-- 2. The goal
--
--   ze-uniq : ∀ u v → (e : u + v ≡ v) → u ≡ ze
--
-- The paper notes this is "not discovered by Agda's built-in automatic
-- proof search", while "Vampire ... finds a correct proof instantly".
--
-- With the prototype, the SMT-LIB problem is emitted by naming the
-- definitions and letting reflection do the rest:
--
--   ze-uniq-v : String
--   ze-uniq-v = print-prog ( kty V :: kfun-ty _+_ :: kfun-ty -_
--                         :: kfun-ty ze :: kthm neutl :: kthm negl
--                         :: kthm assoc :: kgoal ze-uniq :: [] )
--
-- yielding (declare-sort vec.V 0), (declare-fun vec._+_ ...), the three
-- axioms as named `assert`s, `u` and `v` as fresh constants, `e` as an
-- assert, and the goal under `assert-not`.

------------------------------------------------------------------------
-- 3. Vampire's refutation, transformed and translated
--
-- Steps 1-3 of the refutation are just the axioms neutl, negl, assoc,
-- and step 4 is the hypothesis `e` (reoriented -- Vampire treats
-- equations as symmetric, hence the `sym`s below).
--
-- Step 5 is the negated goal `ze != u`.  Under the transform of
-- Section 3.3 every goal clause `C → ⊥` becomes `C → G`, so step 5
-- becomes the tautology `ze ≡ u → ze ≡ u` and step 15 (resolution
-- against ⊥) becomes an application of it.  Both therefore carry no
-- content and vanish from the term.  What remains is steps 6-14: pure
-- superposition, which Section 3.4 translates via
--
--   rw : l ≡ r → P[l] → P[r]        (here: `cong` and `trans`)
--
-- Steps 6 and 8-12 depend only on the axioms.

-- 6.  (- x) + (x + y) ≡ ze + y                       superposition 3,2
step-6 : ∀ x y → (- x) + (x + y) ≡ ze + y
-- step-6 x y = trans (sym (assoc (- x) x y)) (cong (_+ y) (negl x))
step-6 x y = sym (subst (λ z → z + y ≡ (- x) + (x + y)) (negl x) (assoc (- x) x y))

-- 8.  (- x) + (x + y) ≡ y                            superposition 6,1
step-8 : ∀ x y → (- x) + (x + y) ≡ y
-- step-8 x y = trans (step-6 x y) (neutl y)
step-8 x y = subst (λ z → (- x) + (x + y) ≡ z) (neutl y) (step-6 x y)

-- 9.  (- (- x)) + ze ≡ x                             superposition 8,2
step-9 : ∀ x → (- (- x)) + ze ≡ x
-- step-9 x = trans (cong ((- (- x)) +_) (sym (negl x))) (step-8 (- x) x)
step-9 x = subst (λ z → (- (- x)) + z ≡ x) (negl x) (step-8 (- x) x)

-- 10. y + x ≡ (- - y) + x                            superposition 8,8
step-10 : ∀ x y → y + x ≡ (- (- y)) + x
-- step-10 x y = trans (sym (step-8 (- y) (y + x))) 
--                   (cong ((- (- y)) +_) (step-8 y x))
step-10 x y = sym (subst (λ z → (- (- y)) + z ≡ y + x) (step-8 y x) (step-8 (- y) (y + x)))

-- 11. x + ze ≡ x                                     superposition 9,10
step-11 : ∀ x → x + ze ≡ x
-- step-11 x = trans (step-10 ze x) (step-9 x)
step-11 x = subst (λ z → z ≡ x) (sym (step-10 ze x)) (step-9 x)

-- 12. ze ≡ x + (- x)                                 superposition 2,10
step-12 : ∀ x → ze ≡ x + (- x)
-- step-12 x = sym (trans (step-10 (- x) x) (negl (- x)))
step-12 x = subst (λ z → ze ≡ z) (sym (step-10 (- x) x)) (sym (negl (- x)))

-- Steps 7, 13 and 14 additionally use the hypothesis (step 4).

module ZeUniq (u v : V) (e : u + v ≡ v) where

  -- 7.  v + x ≡ u + (v + x)                          superposition 3,4
  step-7 : ∀ x → v + x ≡ u + (v + x)
  -- step-7 x = trans (cong (_+ x) (sym e)) (assoc u v x)
  step-7 x = subst (λ z → z + x ≡ u + (v + x)) e (assoc u v x)

  -- 13. ze ≡ u + ze                                  superposition 7,12
  step-13 : ze ≡ u + ze
  -- step-13 = trans (trans (step-12 v) (step-7 (- v)))
  --                 (cong (u +_) (sym (step-12 v)))
  step-13 = subst (λ z → z ≡ u + z) (sym (step-12 v)) (step-7 (- v))

  -- 14. ze ≡ u                                       superposition 13,11
  step-14 : ze ≡ u
  -- step-14 = trans step-13 (step-11 u)
  step-14 = subst (λ z → ze ≡ z) (step-11 u) step-13

-- 15. ⊥, i.e. `ze ≡ u → ze ≡ u` applied to step 14.

ze-uniq : ∀ u v → u + v ≡ v → u ≡ ze
ze-uniq u v e = sym (ZeUniq.step-14 u v e)

------------------------------------------------------------------------
-- 4. Solved by handwrite style
--
-- The two proofs above both borrow step-11 and step-12, i.e. they still
-- lean on the refutation.  This section owes it nothing: it is the
-- textbook argument, found by the obvious heuristic rather than by
-- search, and it reaches right neutrality and right inverse by a
-- different route than Vampire did (no double negation `- (- x)`
-- anywhere).
--
-- The heuristic: the goal `u + v ≡ v` has `v` on the *right* of `u`, so
-- what it wants is a right cancellation law.  The three axioms are all
-- left-handed, so work towards `cancelʳ` and let it finish the job:
--
--   cancelˡ  -- free: `(- x) +_` undoes `x +_`, which is all the
--              axioms say
--   neutr    -- cancel `(- x) +_` off `x + ze ≟ x`
--   negr     -- cancel `(- x) +_` off `x + (- x) ≟ ze`
--   cancelʳ  -- neutr and negr are exactly the two facts needed to
--              conjugate a `_+ x` away
--
-- Each of the middle two is one appeal to the previous lemma, so the
-- whole development is four chains of rewrites with no invention in it.

open ≡-Reasoning

-- Left cancellation.  Sandwich the hypothesis between `(- x) +_` and
-- the two axioms that dismantle it again; assoc does the plumbing.
cancelˡ : ∀ x {y z} → x + y ≡ x + z → y ≡ z
cancelˡ x {y} {z} p = begin
  y                ≡⟨ sym (neutl y) ⟩
  ze + y           ≡⟨ cong (_+ y) (sym (negl x)) ⟩
  ((- x) + x) + y  ≡⟨ assoc (- x) x y ⟩
  (- x) + (x + y)  ≡⟨ cong ((- x) +_) p ⟩
  (- x) + (x + z)  ≡⟨ sym (assoc (- x) x z) ⟩
  ((- x) + x) + z  ≡⟨ cong (_+ z) (negl x) ⟩
  ze + z           ≡⟨ neutl z ⟩
  z                ∎

-- ze is a right unit too.  Prefixing `(- x) +_` turns the wanted
-- `x + ze ≡ x` into `ze + ze ≡ ze`, which is neutl at ze.
neutr : ∀ x → x + ze ≡ x
neutr x = cancelˡ (- x) (begin
  (- x) + (x + ze)  ≡⟨ sym (assoc (- x) x ze) ⟩
  ((- x) + x) + ze  ≡⟨ cong (_+ ze) (negl x) ⟩
  ze + ze           ≡⟨ neutl ze ⟩
  ze                ≡⟨ sym (negl x) ⟩
  (- x) + x         ∎)

-- The same move for the inverse: prefixing `(- x) +_` collapses the
-- left half to ze and leaves `(- x)` on both sides, modulo neutr.
negr : ∀ x → x + (- x) ≡ ze
negr x = cancelˡ (- x) (begin
  (- x) + (x + (- x))  ≡⟨ sym (assoc (- x) x (- x)) ⟩
  ((- x) + x) + (- x)  ≡⟨ cong (_+ (- x)) (negl x) ⟩
  ze + (- x)           ≡⟨ neutl (- x) ⟩
  (- x)                ≡⟨ sym (neutr (- x)) ⟩
  (- x) + ze           ∎)

-- Right cancellation: the mirror image of cancelˡ, now that ze and the
-- inverse are known to work on the right as well.
cancelʳ : ∀ x {y z} → y + x ≡ z + x → y ≡ z
cancelʳ x {y} {z} p = begin
  y                ≡⟨ sym (neutr y) ⟩
  y + ze           ≡⟨ cong (y +_) (sym (negr x)) ⟩
  y + (x + (- x))  ≡⟨ sym (assoc y x (- x)) ⟩
  (y + x) + (- x)  ≡⟨ cong (_+ (- x)) p ⟩
  (z + x) + (- x)  ≡⟨ assoc z x (- x) ⟩
  z + (x + (- x))  ≡⟨ cong (z +_) (negr x) ⟩
  z + ze           ≡⟨ neutr z ⟩
  z                ∎

-- And the theorem is one rewrite: `u + v ≡ v ≡ ze + v`, cancel the v.
ze-uniq' : ∀ u v → u + v ≡ v → u ≡ ze
ze-uniq' u v e = cancelʳ v (trans e (sym (neutl v)))