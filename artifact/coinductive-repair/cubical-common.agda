{-# OPTIONS --cubical --guardedness --safe #-}

{-
   Shared cubical foundation for the coinductive-repair development.

   This is the dependency-free base that everything else sits on:
   Σ, the path vocabulary, the bi-invertible equivalence `_≃_` and
   logical biimplication `_↔_`, h-levels, a little path algebra, and the
   `≃`-combinators.  `coinductive-repair.mtype` re-exports this module
   publicly, so importing `mtype` (directly or via `coalg`) brings all of
   it into scope.

   Only Agda primitives are used here; there is no external library.
-}

module coinductive-repair.cubical-common where

open import Agda.Primitive
  using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import Agda.Primitive.Cubical
  using (I; i0; i1; primHComp; primComp)
  renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_;
            primTransp to transp)
open import Agda.Builtin.Cubical.Path public

private variable
  ℓ ℓ' ℓ'' : Level

{- Dependent pairs. -}

infixr 4 _,_
record Σ (X : Type ℓ) (P : X → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : X
    snd : P fst
open Σ public

{- Path vocabulary: reflexivity, inversion, congruence, transport, and
   `subst`-based path concatenation. -}

refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = λ _ → x

sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)

cong : {A : Type ℓ} {B : A → Type ℓ'} (f : (x : A) → B x)
       {x y : A} (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)

transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

subst : {A : Type ℓ} (B : A → Type ℓ')
        {x y : A} → x ≡ y → B x → B y
subst B p bx = transp (λ i → B (p i)) i0 bx

-- `subst` as a dependent path: `bx` and `subst B p bx` are connected by a
-- `PathP` over the family `B ∘ p`.
subst-filler : {A : Type ℓ} (B : A → Type ℓ')
               {x y : A} (p : x ≡ y) (bx : B x) →
               PathP (λ i → B (p i)) bx (subst B p bx)
subst-filler B p bx i = transp (λ j → B (p (i ∧ j))) (~ i) bx

-- `PathP A x y` is, as a *type*, the path `transport A x ≡ y`. Presenting
-- it as an actual path of types makes `fromPathP`/`toPathP` literal
-- transports, so their round-trip is `transport⁻Transport`.
PathP≡Path : (A : I → Type ℓ) (x : A i0) (y : A i1)
           → PathP A x y ≡ (transp (λ i → A i) i0 x ≡ y)
PathP≡Path A x y i =
  PathP (λ j → A (i ∨ j)) (transp (λ j → A (i ∧ j)) (~ i) x) y

-- Collapse a `PathP` to a plain path on the transported endpoint.
fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
          → PathP A x y → transp (λ i → A i) i0 x ≡ y
fromPathP {A = A} {x = x} {y = y} = transport (PathP≡Path A x y)

-- Build a `PathP` from such a plain path (inverse of `fromPathP`).
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
        → transp (λ i → A i) i0 x ≡ y → PathP A x y
toPathP {A = A} {x = x} {y = y} = transport (sym (PathP≡Path A x y))

-- `subst` along `refl` is the identity (up to a path).
substRefl : {A : Type ℓ} (B : A → Type ℓ') {x : A} (bx : B x)
          → subst B refl bx ≡ bx
substRefl B {x} bx i = transp (λ _ → B x) i bx

-- Extend a `PathP` by a plain path on its right (`i1`) endpoint.
_▷_ : {A : I → Type ℓ} {x : A i0} {y z : A i1}
    → PathP A x y → y ≡ z → PathP A x z
_▷_ {x = x} p q i =
  primHComp
    (λ j → λ where
      (i = i0) → x
      (i = i1) → q j)
    (p i)
infixl 30 _▷_

-- Composition of base paths (hcomp form) and its filler.
compBase : {A : Type ℓ} {a0 a1 a2 : A} → a0 ≡ a1 → a1 ≡ a2 → a0 ≡ a2
compBase {a0 = a0} bp bq i =
  primHComp (λ j → λ where (i = i0) → a0 ; (i = i1) → bq j) (bp i)

compBase-fill : {A : Type ℓ} {a0 a1 a2 : A}
                (bp : a0 ≡ a1) (bq : a1 ≡ a2) (i j : I) → A
compBase-fill {a0 = a0} bp bq i j =
  primHComp (λ l → λ where (i = i0) → a0
                           (i = i1) → bq (j ∧ l)
                           (j = i0) → bp i)
            (bp i)

-- Composition of dependent paths over a composite base, `compBase bp bq`.
compPathP : {A : Type ℓ} {B : A → Type ℓ'} {a0 a1 a2 : A}
            {bp : a0 ≡ a1} {bq : a1 ≡ a2}
            {b0 : B a0} {b1 : B a1} {b2 : B a2}
          → PathP (λ i → B (bp i)) b0 b1
          → PathP (λ i → B (bq i)) b1 b2
          → PathP (λ i → B (compBase bp bq i)) b0 b2
compPathP {B = B} {bp = bp} {bq = bq} {b0 = b0} P Q i =
  primComp (λ j → B (compBase-fill bp bq i j))
           (λ j → λ where (i = i0) → b0 ; (i = i1) → Q j)
           (P i)

-- Appending `refl` on the right of a `PathP` is the identity.
▷-refl : {A : I → Type ℓ} {a : A i0} {b : A i1} (P : PathP A a b)
       → (P ▷ (λ _ → b)) ≡ P
▷-refl {a = a} {b = b} P l i =
  primHComp (λ j → λ where (i = i0) → a ; (i = i1) → b ; (l = i1) → P i) (P i)

-- Appending `refl` on the left of a base composition collapses it.
compBase-refl : {A : Type ℓ} {a0 a1 : A} (bp : a0 ≡ a1)
              → compBase bp (λ _ → a1) ≡ bp
compBase-refl {a0 = a0} {a1 = a1} bp l i =
  primHComp (λ j → λ where (i = i0) → a0 ; (i = i1) → a1 ; (l = i1) → bp i)
            (bp i)

-- The 3-D filler linking `compBase-fill bp refl` (l=i0) to `bp` (l=i1),
-- with top face `compBase-refl bp` (j=i1).
compBase-refl-fill : {A : Type ℓ} {a0 a1 : A} (bp : a0 ≡ a1) (l i j : I) → A
compBase-refl-fill {a0 = a0} {a1 = a1} bp l i j =
  primHComp (λ m → λ where (i = i0) → a0
                           (i = i1) → a1
                           (j = i0) → bp i
                           (l = i1) → bp i)
            (bp i)

-- `compPathP P refl ≡ P`, as a dependent path over `compBase-refl bp`.
compPathP-refl : {A : Type ℓ} {B : A → Type ℓ'} {a0 a1 : A} {bp : a0 ≡ a1}
                 {b0 : B a0} {b1 : B a1}
                 (P : PathP (λ i → B (bp i)) b0 b1)
               → PathP (λ l → PathP (λ i → B (compBase-refl bp l i)) b0 b1)
                       (compPathP {A = A} {B = B} {bp = bp} {bq = λ _ → a1}
                                  P (λ _ → b1)) P
compPathP-refl {B = B} {bp = bp} {b0 = b0} {b1 = b1} P l i =
  primComp (λ j → B (compBase-refl-fill bp l i j))
           (λ j → λ where (i = i0) → b0 ; (i = i1) → b1 ; (l = i1) → P i)
           (P i)

funExt : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x}
       → (∀ x → f x ≡ g x) → f ≡ g
funExt h i x = h x i

_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q = subst (λ a → x ≡ a) q p
infixr 30 _∙_

{-
   Bi-invertible type equivalence: a forward map with separately stated
   left and right inverses.  (They coincide as functions in our uses, but
   keeping the two round-trip witnesses independent is convenient.)
-}

record _≃_ (X Y : Type ℓ) : Type ℓ where
  field
    fwd      : X → Y
    bwd-L    : Y → X
    leftInv  : (x : X) → bwd-L (fwd x) ≡ x
    bwd-R    : Y → X
    rightInv : (y : Y) → fwd (bwd-R y) ≡ y
open _≃_ public

-- Alias used by the carrier-iso corollary in `coalg`.
Iso : (X Y : Type ℓ) → Type ℓ
Iso = _≃_

{-
   Logical biimplication: forward and backward maps with no round-trip
   witnesses.  Weaker than `_≃_`, used when one side is not (or is not
   asserted to be) a proposition.
-}

record _↔_ (X Y : Type ℓ) : Type ℓ where
  field
    fwd : X → Y
    bwd : Y → X
open _↔_ public

{- Propositions, contractibility, and the basic h-level lemmas. -}

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

isContr : Type ℓ → Type ℓ
isContr A = Σ A (λ a → (x : A) → a ≡ x)

isPropΠ : {A : Type ℓ} {B : A → Type ℓ'}
        → ((x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h f g = funExt (λ x → h x (f x) (g x))

-- `isContr A` is itself a proposition (i = outer isProp index, j = the
-- inner snd-PathP index).
isPropIsContr : {A : Type ℓ} → isProp (isContr A)
isPropIsContr (c₀ , p₀) (c₁ , p₁) i =
  ( p₀ c₁ i
  , λ x j → primHComp
      (λ k → λ where
        (j = i0) → p₀ c₁ i
        (j = i1) → p₀ x (i ∨ k)
        (i = i0) → p₀ x (j ∧ k)
        (i = i1) → p₁ x j)
      (p₀ (p₁ x j) i))

{-
   Path induction, and path algebra for the `subst`-based `_∙_`.  The
   `J` base cases collapse because `transp A i1 a ≡ a` always holds
   definitionally (whereas `transp (λ _ → A) i0` does not reduce for
   abstract `A`, so `p ∙ refl ≡ p` is `∙-idr`, not `refl`).
-}

J : {A : Type ℓ} {x : A}
    (P : (y : A) → x ≡ y → Type ℓ')
  → P x refl → {y : A} (p : x ≡ y) → P y p
J {x = x} P d p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

-- `transport` along `refl` is the identity.
transportRefl : {A : Type ℓ} (a : A) → transport refl a ≡ a
transportRefl a = substRefl (λ X → X) a

-- Transporting backward then forward is the identity (the round-trip of a
-- type equivalence presented by a path).
transport⁻Transport : {A B : Type ℓ} (p : A ≡ B) (b : B)
                    → transport p (transport (sym p) b) ≡ b
transport⁻Transport {A = A} p b =
  J (λ B' p' → (b' : B') → transport p' (transport (sym p') b') ≡ b')
    (λ b' → transportRefl (transport refl b') ∙ transportRefl b')
    p b

-- The `fromPathP` / `toPathP` round-trip — now a literal `transport⁻Transport`.
fromPathP-toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
                    (p : transp (λ i → A i) i0 x ≡ y)
                  → fromPathP {A = A} (toPathP {A = A} p) ≡ p
fromPathP-toPathP {A = A} {x = x} {y = y} p =
  transport⁻Transport (PathP≡Path A x y) p

toPathP-fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
                    (P : PathP A x y)
                  → toPathP {A = A} (fromPathP {A = A} P) ≡ P
toPathP-fromPathP {A = A} {x = x} {y = y} P =
  transport⁻Transport (sym (PathP≡Path A x y)) P

-- `V ▷ sym (fromPathP V)` is the canonical `toPathP refl` (the transp-filler),
-- *independently of `V`*.  This is the key fact behind the p/q corner
-- coincidence in `deriveCoind2D`.
▷-sym-fromPathP :
    {A : I → Type ℓ} {x : A i0} {y : A i1} (V : PathP A x y)
  → (V ▷ (λ i → fromPathP V (~ i)))
      ≡ toPathP {A = A} (λ _ → transp (λ i → A i) i0 x)
▷-sym-fromPathP {A = A} {x = x} {y = y} V =
  subst (λ V' → (V' ▷ (λ i → fromPathP V (~ i)))
                  ≡ toPathP {A = A} (λ _ → tx))
        (toPathP-fromPathP V)
        (base (fromPathP V))
  where
    tx : A i1
    tx = transp (λ i → A i) i0 x
    base : (w : tx ≡ y)
         → (toPathP {A = A} w ▷ (λ i → w (~ i))) ≡ toPathP {A = A} (λ _ → tx)
    base w =
      J (λ y' w' → (toPathP {A = A} {x = x} {y = y'} w' ▷ (λ i → w' (~ i)))
                     ≡ toPathP {A = A} (λ _ → tx))
        (▷-refl (toPathP {A = A} (λ _ → tx)))
        w

∙-idr : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
∙-idr {x = x} {y = y} p i = transp (λ _ → x ≡ y) i p

∙assoc : {A : Type ℓ} {w x y z : A}
         (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q r =
  J (λ _ r' → (p ∙ q) ∙ r' ≡ p ∙ (q ∙ r'))
    (∙-idr (p ∙ q) ∙ sym (cong (p ∙_) (∙-idr q)))
    r

cong₂ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B → C)
        {x y : A} {u v : B} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f p q i = f (p i) (q i)

cong-∙ : {A : Type ℓ} {X : Type ℓ'}
         (F : A → X) {x y z : A} (p : x ≡ y) (q : y ≡ z)
       → cong F (p ∙ q) ≡ cong F p ∙ cong F q
cong-∙ F p q =
  J (λ _ q' → cong F (p ∙ q') ≡ cong F p ∙ cong F q')
    (cong (cong F) (∙-idr p) ∙ sym (∙-idr (cong F p)))
    q

∙-idl : {A : Type ℓ} {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
∙-idl p = J (λ _ p' → refl ∙ p' ≡ p') (∙-idr refl) p

{- Sliding the left endpoint of `q` along `p` (`subst (_≡ y) p`)
   is the same as prepending `sym p`. -}
subst-slide : {A : Type ℓ} {a b y : A} (p : a ≡ b) (q : a ≡ y)
            → subst (λ z → z ≡ y) p q ≡ sym p ∙ q
subst-slide {y = y} =
  J (λ _ p' → (q : _ ≡ y) → subst (λ z → z ≡ y) p' q ≡ sym p' ∙ q)
    (λ q → substRefl (λ z → z ≡ y) q ∙ sym (∙-idl q))

-- `subst` on the right endpoint of `q : x ≡ a` along `p : a ≡ b`
-- is the same as appending `p`.
subst-slide-right : {A : Type ℓ} {x a b : A} (p : a ≡ b) (q : x ≡ a)
                  → subst (λ z → x ≡ z) p q ≡ q ∙ p
subst-slide-right {x = x} =
  J (λ _ p' → (q : x ≡ _) → subst (λ z → x ≡ z) p' q ≡ q ∙ p')
    (λ q → substRefl (λ z → x ≡ z) q ∙ sym (∙-idr q))

-- Transporting a path along its endpoints (`sym a ∙ p ∙ b`).
transp-path : {A : Type ℓ} {a0 a1 b0 b1 : A}
              (a : a0 ≡ a1) (b : b0 ≡ b1) (p : a0 ≡ b0)
            → transp (λ j → a j ≡ b j) i0 p ≡ sym a ∙ (p ∙ b)
transp-path {a0 = a0} a b p =
  J (λ _ a' → {b0 b1 : _} (b' : b0 ≡ b1) (p' : a0 ≡ b0)
                → transp (λ j → a' j ≡ b' j) i0 p' ≡ sym a' ∙ (p' ∙ b'))
    (λ {b0} {b1} b' p' →
       J (λ _ b'' → (p'' : a0 ≡ b0)
                      → transp (λ j → a0 ≡ b'' j) i0 p'' ≡ sym refl ∙ (p'' ∙ b''))
         (λ p'' → transportRefl p'' ∙ sym (∙-idl (p'' ∙ refl) ∙ ∙-idr p''))
         b' p')
    a b p

-- The diagonal of a `transp`-over-constant square is its
-- `transportRefl` edge followed by the path.
transp-diag : {C : Type ℓ} {a b : C} (P : a ≡ b)
            → (λ k → transp (λ _ → C) k (P k)) ≡ transportRefl (P i0) ∙ P
transp-diag {C = C} {a = a} P =
  J (λ b' P' → (λ k → transp (λ _ → C) k (P' k)) ≡ transportRefl (P' i0) ∙ P')
    (sym (∙-idr (transportRefl a)))
    P

-- Right inverse: `p ∙ sym p` contracts to `refl`.
rCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel {x = x} p = J (λ _ p' → p' ∙ sym p' ≡ refl) (∙-idr refl) p

-- Left inverse: `sym p ∙ p` contracts to `refl`.
lCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
lCancel p = J (λ _ p' → sym p' ∙ p' ≡ refl) (∙-idr refl) p

-- `sym` is a contravariant functor on `_∙_`.
symDist : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
        → sym (p ∙ q) ≡ sym q ∙ sym p
symDist p q =
  J (λ _ q' → sym (p ∙ q') ≡ sym q' ∙ sym p)
    (cong sym (∙-idr p) ∙ sym (∙-idl (sym p)))
    q

{- A square (a `PathP` between two paths) gives the equality of its two
   ways around, for the `subst`-based `_∙_`.  Edges:
       top : a ≡ b,  bot : c ≡ d,  left : a ≡ c,  right : b ≡ d.
   Proof: `J` on `top` (abstracting `right`, whose type tracks `top`'s
   endpoint) reduces to the base case `top = refl`, where `left ∙ bot`
   is *definitionally* `transp (λ i → a ≡ bot i) i0 left`, so
   `fromPathP sq` is exactly `left ∙ bot ≡ right`. -}
Square→∙ : {A : Type ℓ} {a b c d : A}
           {top : a ≡ b} {bot : c ≡ d} {left : a ≡ c} {right : b ≡ d}
         → PathP (λ i → top i ≡ bot i) left right
         → top ∙ right ≡ left ∙ bot
Square→∙ {d = d} {top = top} {bot = bot} {left = left} {right = right} sq =
  J (λ _ top' → (right' : _ ≡ d)
              → PathP (λ i → top' i ≡ bot i) left right'
              → top' ∙ right' ≡ left ∙ bot)
    (λ right' sq' → ∙-idl right' ∙ sym (fromPathP sq'))
    top right sq

{- More h-levels: a prop is a set, contractibility implies set-ness,
   `PathP` between propositions, and Σ/retract closure. -}

isContr→isProp : {A : Type ℓ} → isContr A → isProp A
isContr→isProp (c , p) x y = sym (p x) ∙ p y

isProp→isSet : {A : Type ℓ} → isProp A
             → (x y : A) (p q : x ≡ y) → p ≡ q
isProp→isSet {A = A} h x y p q j i =
  primHComp
    (λ k → λ where
      (i = i0) → h x x k
      (i = i1) → h x y k
      (j = i0) → h x (p i) k
      (j = i1) → h x (q i) k)
    x

isContr→isSet : {A : Type ℓ} → isContr A
              → (x y : A) (p q : x ≡ y) → p ≡ q
isContr→isSet c = isProp→isSet (isContr→isProp c)

isProp→PathP : {A : I → Type ℓ} → ((i : I) → isProp (A i))
             → (a₀ : A i0) (a₁ : A i1) → PathP A a₀ a₁
isProp→PathP {A = A} hA a₀ a₁ i =
  hA i (transp (λ j → A (i ∧ j)) (~ i) a₀)
       (transp (λ j → A (i ∨ ~ j)) i a₁) i

Σ-isProp : {A : Type ℓ} {B : A → Type ℓ'}
         → isProp A → ((a : A) → isProp (B a)) → isProp (Σ A B)
Σ-isProp pa pb (x₀ , y₀) (x₁ , y₁) i =
    pa x₀ x₁ i
  , isProp→PathP (λ j → pb (pa x₀ x₁ j)) y₀ y₁ i

retract-isContr : {A : Type ℓ} {B : Type ℓ'}
                  (r : A → B) (s : B → A)
                → ((b : B) → r (s b) ≡ b)
                → isContr A → isContr B
retract-isContr r s rs (c , p) =
  r c , (λ b → cong r (p (s b)) ∙ rs b)

isSetΠ : {A : Type ℓ} {B : A → Type ℓ'}
       → ((a : A) → isSet (B a)) → isSet ((a : A) → B a)
isSetΠ h f g p q i j a =
  h a (f a) (g a) (λ k → p k a) (λ k → q k a) i j

-- Σ over a constant family (all `P` needs); Σ-eta makes the
-- rebuilt square's boundary match on the nose.
isSetΣconst : {A : Type ℓ} {B : Type ℓ'}
            → isSet A → isSet B → isSet (Σ A (λ _ → B))
isSetΣconst sa sb u v p q i j =
    sa (fst u) (fst v) (λ k → fst (p k)) (λ k → fst (q k)) i j
  , sb (snd u) (snd v) (λ k → snd (p k)) (λ k → snd (q k)) i j

isSetRetract : {A : Type ℓ} {B : Type ℓ'}
               (s : B → A) (r : A → B)
             → ((b : B) → r (s b) ≡ b)
             → isSet A → isSet B
isSetRetract s r rs sa x y p q i j =
  primHComp
    (λ k → λ where
      (i = i0) → rs (p j) k
      (i = i1) → rs (q j) k
      (j = i0) → rs x k
      (j = i1) → rs y k)
    (r (sa (s x) (s y) (cong s p) (cong s q) i j))

{- Non-dependent products and the `≃`-combinators. -}

infixr 2 _×_
_×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

≃-trans : {A B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
≃-trans e f = record
  { fwd     = λ x → fwd f (fwd e x)
  ; bwd-L   = λ z → bwd-L e (bwd-L f z)
  ; leftInv = λ x → cong (bwd-L e) (leftInv f (fwd e x)) ∙ leftInv e x
  ; bwd-R   = λ z → bwd-R e (bwd-R f z)
  ; rightInv = λ z → cong (fwd f) (rightInv e (bwd-R f z)) ∙ rightInv f z }

-- Componentwise congruence of `≃` under binary product.
≃-× : {A A' B B' : Type ℓ} → A ≃ A' → B ≃ B' → (A × B) ≃ (A' × B')
≃-× e f = record
  { fwd      = λ p → fwd e (fst p) , fwd f (snd p)
  ; bwd-L    = λ p → bwd-L e (fst p) , bwd-L f (snd p)
  ; leftInv  = λ p i → leftInv e (fst p) i , leftInv f (snd p) i
  ; bwd-R    = λ p → bwd-R e (fst p) , bwd-R f (snd p)
  ; rightInv = λ p i → rightInv e (fst p) i , rightInv f (snd p) i }
