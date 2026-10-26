{-# OPTIONS --cubical --guardedness --safe #-}

{-
   M-types for the coinductive-repair development: the coinductive
   record `M A B` with `intro` and `corec`, and the 1-D coinduction
   principle `M-coind` via the bisimulation record `bisimMR`.
   Re-exports `coinductive-repair.cubical-common` publicly.
-}

module coinductive-repair.mtype where

open import Agda.Primitive
  using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import Agda.Primitive.Cubical
  using (I; i0; i1; primHComp)
  renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_;
            primTransp to transp)
open import coinductive-repair.cubical-common public

private variable
  ℓ ℓ' ℓ'' : Level

{- M-types. -}

record M (A : Type ℓ) (B : A → Type ℓ) : Type ℓ where
  coinductive
  field
    shape : A
    pos   : B shape → M A B
open M public

-- intro: build an M-element from a shape and a positions-function.
intro : {A : Type ℓ} {B : A → Type ℓ}
        (a : A) → (B a → M A B) → M A B
shape (intro a f)   = a
pos   (intro a f) b = f b

-- corec: corecurse into M from a carrier C with its own shape-function
-- (s : C → A) and positions-function (p : (c : C) → B (s c) → C).
corec : {A : Type ℓ} {B : A → Type ℓ} (C : Type ℓ)
        (s : C → A) (p : (c : C) → B (s c) → C)
        → C → M A B
shape (corec C s p c)   = s c
pos   (corec C s p c) b = corec C s p (p c b)

{-
   Bisimulation and the 1-D coinduction principle M-coind.

   `bisimMR` is the parametrised bisimulation record (data-style, to let
   the recursion in M-coind pass guardedness).  A coinductive alternative
   `bisimM` is given further down for convenience.
-}

record bisimMR {A : Type ℓ} {B : A → Type ℓ}
               (R : M A B → M A B → Type ℓ)
               (X Y : M A B) : Type ℓ where
  field
    shape-≡R : shape X ≡ shape Y
    pos-R    : (b₀ : B (shape X)) (b₁ : B (shape Y))
               (bp : PathP (λ i → B (shape-≡R i)) b₀ b₁)
             → R (pos X b₀) (pos Y b₁)
open bisimMR public

{- The B-position transports used inside M-coind's pos definition,
   lifted to top-level so they can be referenced externally. -}
module M-coind-internal
    {A : Type ℓ} {B : A → Type ℓ}
    (R : M A B → M A B → Type ℓ)
    (isBis : ∀ {m₀ m₁} → R m₀ m₁ → bisimMR R m₀ m₁) where
  QQ : ∀ {m₀ m₁} (r : R m₀ m₁) → I → Type _
  QQ {m₀ = m₀} {m₁ = m₁} r k = B (shape-≡R (isBis r) k)

  M-coind-b₀ : ∀ {m₀ m₁} (r : R m₀ m₁) (i : I)
             → QQ r i → QQ r i0
  M-coind-b₀ r i b = transp (λ j → QQ r (~ j ∧ i)) (~ i) b

  M-coind-b₁ : ∀ {m₀ m₁} (r : R m₀ m₁) (i : I)
             → QQ r i → QQ r i1
  M-coind-b₁ r i b = transp (λ j → QQ r (j ∨ i)) i b

  M-coind-bp : ∀ {m₀ m₁} (r : R m₀ m₁) (i : I) (b : QQ r i)
             → PathP (λ k → QQ r k) (M-coind-b₀ r i b) (M-coind-b₁ r i b)
  M-coind-bp r i b k =
    transp (λ j → QQ r ((~ k ∧ ~ j ∧ i) ∨ (k ∧ (j ∨ i)) ∨
                          ((~ j ∧ i) ∧ (j ∨ i))))
            ((~ k ∧ ~ i) ∨ (k ∧ i)) b

-- coind: any relation R that is a bisimulation up to itself entails
-- Path equality.
M-coind : {A : Type ℓ} {B : A → Type ℓ}
          (R : M A B → M A B → Type ℓ)
          (isBis : ∀ {m₀ m₁} → R m₀ m₁ → bisimMR R m₀ m₁)
        → ∀ {m₀ m₁} → R m₀ m₁ → m₀ ≡ m₁
shape (M-coind R isBis r i) = shape-≡R (isBis r) i
pos   (M-coind R isBis r i) b =
  M-coind R isBis
    (pos-R (isBis r)
           (M-coind-internal.M-coind-b₀ R isBis r i b)
           (M-coind-internal.M-coind-b₁ R isBis r i b)
           (M-coind-internal.M-coind-bp R isBis r i b))
    i

{- The 2-D bisimulation record for the native `M` — retained only
   as the shape of a 2-D bisimulation; the syntactic 2-D principle
   (`config.deriveCoind2D`) is derived from `corec-uniq-Σ` instead. -}

record bisim2DR
  {A : Type ℓ} {B : A → Type ℓ}
  (R₂ : {X₀ X₁ Y₀ Y₁ : M A B}
        (px : X₀ ≡ X₁) (py : Y₀ ≡ Y₁)
        (p : X₀ ≡ Y₀) (q : X₁ ≡ Y₁) → Type ℓ)
  {X₀ X₁ Y₀ Y₁ : M A B}
  (px : X₀ ≡ X₁) (py : Y₀ ≡ Y₁)
  (p : X₀ ≡ Y₀) (q : X₁ ≡ Y₁) : Type ℓ where
  field
    shape-2D-R : PathP (λ j → shape (px j) ≡ shape (py j))
                       (λ i → shape (p i)) (λ i → shape (q i))
    pos-2D-R   :
      (b₀₀ : B (shape X₀)) (b₀₁ : B (shape Y₀))
      (b₁₀ : B (shape X₁)) (b₁₁ : B (shape Y₁))
      (bp  : PathP (λ i → B (shape (p i))) b₀₀ b₀₁)
      (bq  : PathP (λ i → B (shape (q i))) b₁₀ b₁₁)
      (bpx : PathP (λ j → B (shape (px j))) b₀₀ b₁₀)
      (bpy : PathP (λ j → B (shape (py j))) b₀₁ b₁₁) →
      R₂ (λ j → pos (px j) (bpx j)) (λ j → pos (py j) (bpy j))
         (λ i → pos (p i)  (bp  i)) (λ i → pos (q i)  (bq  i))
open bisim2DR public

