{-# OPTIONS --without-K --cubical-compatible #-}

{-
    Shared basics: base types (ℕ, Σ, ⊤, ⊥, ⊎, Bool, Fin),
    the identity type with its path algebra, transport and funext
    lemmas, and bi-invertible equivalences `_≃_` with their
    triangle identities.
-}
module common where
open import Agda.Primitive renaming (Set to Type) public
variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level


data ℕ {l : Level} : Type l where
    zero : ℕ
    succ : ℕ {l} → ℕ

_+_ : {l : Level} → ℕ {l} → ℕ {l} → ℕ {l}
zero + y = y
succ x + y = succ (x + y)


infixr 4 _,_
record Σ (X : Type ℓ₁) (P : X -> Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : X
    snd : P fst
open Σ public

infixr 6 _×_
_×_ : (X : Type ℓ₁) -> (Y : Type ℓ₂) -> Type (ℓ₁ ⊔ ℓ₂)
X × Y = Σ X (λ _ -> Y)

data ⊥ {ℓ₁} : Type ℓ₁ where

module _ {Y : Type ℓ₂} where
  rec⊥ : ⊥ {ℓ₁} -> Y
  rec⊥ ()

record ⊤ : Type ℓ₁ where
  instance constructor tt

infixr 5 _⊎_
data _⊎_ {ℓ₁ ℓ₂} (X : Type ℓ₁) (Y : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  inl : X -> X ⊎ Y
  inr : Y -> X ⊎ Y

data Bool {ℓ₁} : Type ℓ₁ where
     true : Bool
     false : Bool

infix 4 _≡_
data _≡_ {X : Type ℓ₁} (x : X) : X -> Type ℓ₁ where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

module _ {X : Type ℓ₁} where
  infix 10 !
  ! : {x1 x2 : X} -> x1 ≡ x2 -> x2 ≡ x1
  ! refl = refl

module _ {X : Type ℓ₁} where
  infixr 8 _•_
  _•_ : {x1 x2 : X} -> x1 ≡ x2 -> {x3 : X} -> x2 ≡ x3 -> x1 ≡ x3
  refl • refl = refl

  •unitr : {x1 x2 : X} -> {e : x1 ≡ x2} -> e • refl ≡ e
  •unitr {e = refl} = refl

  •unitl : {x1 x2 : X} -> {e : x1 ≡ x2} -> refl • e ≡ e
  •unitl {e = refl} = refl

  •assoc : {w x x2 x3 : X} -> {p : w ≡ x} -> {q : x ≡ x2} -> {r : x2 ≡ x3}
           -> (p • q) • r ≡ p • q • r
  •assoc {p = refl} {refl} {refl} = refl

  •invl : {x1 x2 : X} -> {e : x1 ≡ x2} -> ! e • e ≡ refl
  •invl {e = refl} = refl

  •invr : {x1 x2 : X} -> {e : x1 ≡ x2} -> e • ! e ≡ refl
  •invr {e = refl} = refl

  !-comp : {x y z : X} -> (p : x ≡ y) -> (q : y ≡ z) -> ! (p • q) ≡ ! q • ! p
  !-comp refl refl = refl

  !! : {x y : X} -> (p : x ≡ y) → ! (! p) ≡ p
  !! refl = refl

!• : {X : Type ℓ₁} {x1 x2 : X} {p : x1 ≡ x2} {q : x1 ≡ x2} →
  (j : ! p • q ≡ refl) → q ≡ p
!• {p = refl} {q} j = ! •unitl • j

ap : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} {a b : X}
   (P : X → Y) → (p : a ≡ b) → P a ≡ P b
ap P refl = refl

ap-const : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} {a b : X}
  {c : Y} (p : a ≡ b) → ap (λ _ → c) p ≡ refl
ap-const refl = refl

ap-• : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} (f : X → Y) {x y z : X}
       (p : x ≡ y) (q : y ≡ z) → ap f (p • q) ≡ ap f p • ap f q
ap-• f refl refl = refl

ap2 : {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} {a b : X} {c d : Y}
   (P : X → Y → Z) → (p : a ≡ b) → (p2 : c ≡ d) → P a c ≡ P b d
ap2 P refl refl = refl

tpt : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {a b : X}
   (P : X → Type ℓ₂) → (p : a ≡ b) → P a → P b
tpt P refl x = x

tpt-• : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {a m b : X}
        (P : X → Type ℓ₂) → (p : a ≡ m) (q : m ≡ b) → (i : P a) →  tpt P (p • q) i ≡ tpt P q (tpt P p i)
tpt-• P refl refl i = refl

tptConst : {l : Level} {A B : Type l} {a a' : A} → (p : a ≡ a') → (b : B) → tpt (λ _ → B) p b ≡ b
tptConst refl b = refl

tpt-path : {l : Level} → {A B : Type l} (L R : A → B) {a a' : A} (q : a ≡ a') (e : L a ≡ R a)
           → tpt (λ x → L x ≡ R x) q e ≡ ! (ap L q) • e • (ap R q)
tpt-path L R refl e = ! •unitr • ! •unitl

apd : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {x1 x2 : X} (P : X -> Type ℓ₂) (f : (x : X) -> P x) -> (e : x1 ≡ x2) -> tpt P e (f x1) ≡ f x2
apd P f refl = refl

Σ-≡-intro : {l : Level} {A : Type l} {a a' : A} {B : A → Type l} {b : B a} {b' : B a'} → (p1 : a ≡ a') (p2 : tpt (λ x → B x) p1 b ≡ b') → (a , b)  ≡ (a' , b')
Σ-≡-intro refl refl = refl

_∘_ : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} → (g : B → C) → (f : A → B) → (A → C)
g ∘ f = λ x → (g (f x))

ap-∘ : {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃}
       {f : Y → Z} {g : X → Y} {x y : X} (p : x ≡ y)
     → ap (f ∘ g) p ≡ ap f (ap g p)
ap-∘ refl = refl

tpt-ap :  {l : Level} {A B : Type l} (P : B → Type l) (f : A → B) {x y : A} (p : x ≡ y) (b : P (f x))
       → tpt P (ap f p) b ≡ tpt (P ∘ f) p b
tpt-ap P f refl b = refl

Σ-≡-intro-ap : {l : Level} {A X : Type l} {B : A → Type l} {a : A} {x y : X}
    {f : X → B a} (q : x ≡ y) →
    Σ-≡-intro {B = B} refl (ap f q) ≡ ap (λ v → (a , f v)) q
Σ-≡-intro-ap refl = refl

Σ-≡-intro-refl : {l : Level} {A : Type l} {a : A} {B : A → Type l} {b b' : B a}
    (q : b ≡ b') → Σ-≡-intro {B = B} refl q ≡ ap (λ v → (a , v)) q
Σ-≡-intro-refl refl = refl

ap-Σ-const : {l : Level} {A B X : Type l}
    (f : X → A) (g : X → B) {x y : X} (p : x ≡ y) →
    ap (λ z → (f z , g z)) p ≡ Σ-≡-intro (ap f p) (tptConst (ap f p) _ • ap g p)
ap-Σ-const f g refl = refl

ext-fun : {l : Level} {A B : Type l} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
ext-fun refl = λ x → refl

happly : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : (x : A) → B x} →
  f ≡ g → (x : A) → f x ≡ g x
happly refl x = refl

happly-• : {a b : Level} {A : Type a} {B : A → Type b} {f g h : (x : A) → B x} →
  (p : f ≡ g) (q : g ≡ h) → (x : A) → happly (p • q) x ≡ happly p x • happly q x
happly-• refl refl x = refl

happly-! : {a b : Level} {A : Type a} {B : A → Type b} {f g : (x : A) → B x} →
  (p : f ≡ g) → (x : A) → happly (! p) x ≡ ! (happly p x)
happly-! refl x = refl

happly-precomp : {a b : Level} {A B C : Type a} {f g : A → B} →
  (e : f ≡ g) (h : C → A) → (x : C) → happly (ap (λ l → l ∘ h) e) x ≡ happly e (h x)
happly-precomp refl h x = refl

happly-ap : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : (x : A) → B x}
    (p : f ≡ g) (x : A) → happly p x ≡ ap (λ h → h x) p
happly-ap refl x = refl

happly-ap-double-∘ : {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} {W : Type ℓ₄}
       {f : Y → Z} {g : W → X → Y} {m n : W} (p : m ≡ n) (x : X)
     → happly (ap (λ z → f ∘ (g z)) p) x ≡ ap f (ap (λ z → g z x) p)
happly-ap-double-∘ refl x = refl

postulate
    ext : {a b : Level} {A : Type a} {B : A → Type b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
    happlyExt : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : (x : A) → B x} →
      (h : (x : A) → f x ≡ g x) → (x : A) → happly (ext h) x ≡ h x
    extHapply : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : (x : A) → B x} →
      (p : f ≡ g) → p ≡ ext (λ x → happly p x)

funext-refl : {a b : Level} {A : Type a} {B : A → Type b} {f : (x : A) → B x} →
  refl ≡ ext {f = f} (λ _ → refl)
funext-refl {_} {_} {_} {f} = extHapply refl

happly-inj : {a b : Level} {A : Type a} {B : A → Type b} {f g : (x : A) → B x} →
  {α : f ≡ g} {β : f ≡ g} → happly α ≡ happly β → α ≡ β
happly-inj {α = α} {β = β} happly_eq = extHapply α • ap ext happly_eq • !(extHapply β)

precomp-ext : {l : Level} {A B : Type l} {C : Type l}
    {f g : B → C} (i : A → B) (e : (x : B) → f x ≡ g x) →
    ap (_∘ i) (ext e) ≡ ext (λ x → e (i x))
precomp-ext {_} {A} {B} {C} {f} {g} i e =
    extHapply (ap (_∘ i) (ext e))
    • ap ext (ext pw)
    where
        pw : (x : A) → happly (ap (_∘ i) (ext e)) x ≡ e (i x)
        pw x = happly-ap (ap (_∘ i) (ext e)) x
            • ! (ap-∘ {f = λ (h : A → C) → h x} {g = _∘ i} (ext e))
            • ! (happly-ap (ext e) (i x))
            • happlyExt e (i x)

hnat : {A : Type ℓ₁} {f : A → A} (H : (x : A) → f x ≡ x)
     → (x : A) → H (f x) ≡ ap f (H x)
hnat {ℓ₁} {A} {f} H x = cancel-right (H x) (nat (H x))
  where
    -- Naturality square: for any p : a ≡ b, H a • p ≡ ap f p • H b
    nat : {a b : A} (p : a ≡ b) → H a • p ≡ ap f p • H b
    nat refl = •unitr • ! (•unitl)

    -- Right cancellation: if p • r ≡ q • r then p ≡ q
    cancel-right : {a b c : A} {p q : a ≡ b} (r : b ≡ c) → p • r ≡ q • r → p ≡ q
    cancel-right refl e = ! (•unitr) • e • •unitr

hnat-id : {l : Level} {A B : Type l} {f : A → A} (H : (x : A) → f x ≡ x)
         → {a b : A} (p : a ≡ b) → H a • p ≡ ap f p • H b
hnat-id H refl =  •unitr • ! (•unitl)

infix 4 _≃_
record _≃_ (X : Type ℓ₁) (Y : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor biinv
  field
    f : X -> Y
    g : Y -> X
    η : (x : X) -> g (f x) ≡ x
    h : Y -> X
    ε : (y : Y) -> f (h y) ≡ y

  g~h : (y : Y) → g y ≡ h y
  g~h y = ap g (! (ε y)) • η (h y)

  ε' : (y : Y) → f (g y) ≡ y
  ε' y = ap f (g~h y) • ε y
  ε'' : (y : Y) → f (g y) ≡ y
  ε'' y = ! (ε' (f (g y))) • ap f (η (g y)) • ε' y
  coh : (x : X) → ap f (η x) ≡ ε'' (f x)
  coh x = nat-ε' • ap (λ p → ! (ε' (f (g (f x)))) • p • ε' (f x)) middle
    where
      cancel-left : {a b c : Y} {p : b ≡ c} {q : a ≡ c}
                → (r : a ≡ b) → r • p ≡ q → p ≡ ! r • q
      cancel-left refl e = ! (•unitl) • e • (! •unitl)
      nat-ε' : ap f (η x) ≡ ! (ε' (f (g (f x)))) • ap (f ∘ g) (ap f (η x)) • ε' (f x)
      nat-ε' = cancel-left (ε' (f (g (f x)))) (hnat-id {B = Y} ε' (ap f (η x))) -- from naturality square, then path algebra

      -- ap(f∘g)(ap f (η x)) ≡ ap f (η(g(f x)))
      middle : ap (f ∘ g) (ap f (η x)) ≡ ap f (η (g (f x)))
      middle = ap-∘ (ap f (η x))                       -- ap (f∘g) (ap f (η x)) ≡ ap f (ap g (ap f (η x)))
       • ap (ap f) (! (ap-∘ (η x)))              -- ap f (ap g (ap f (η x))) ≡ ap f (ap (g∘f) (η x))
       • ap (ap f) (! (hnat η x))                -- ap f (ap (g∘f) (η x)) ≡ ap f (η (g (f x)))
open _≃_

{-
    Identity equivalence.
-}
id-eqv : {A : Type ℓ₁} → A ≃ A
id-eqv .f x = x
id-eqv .g x = x
id-eqv .η _ = refl
id-eqv .h x = x
id-eqv .ε _ = refl

{-
    Postcomposition: an equivalence `B ≃ C` lifts to an equivalence
    `(A → B) ≃ (A → C)`. Uses function extensionality.
-}
→-eqv-r : {A : Type ℓ₁} {B C : Type ℓ₂} → B ≃ C → (A → B) ≃ (A → C)
→-eqv-r e .f r = f e ∘ r
→-eqv-r e .g r = g e ∘ r
→-eqv-r e .η r = ext (λ x → η e (r x))
→-eqv-r e .h r = h e ∘ r
→-eqv-r e .ε r = ext (λ x → ε e (r x))

{-
    Cartesian product preserves equivalences componentwise.
-}
×-eqv : {A A' : Type ℓ₁} {B B' : Type ℓ₂} →
        A ≃ A' → B ≃ B' → (A × B) ≃ (A' × B')
×-eqv e1 e2 .f (a , b) = (f e1 a , f e2 b)
×-eqv e1 e2 .g (a , b) = (g e1 a , g e2 b)
×-eqv e1 e2 .η (a , b) = ap2 _,_ (η e1 a) (η e2 b)
×-eqv e1 e2 .h (a , b) = (h e1 a , h e2 b)
×-eqv e1 e2 .ε (a , b) = ap2 _,_ (ε e1 a) (ε e2 b)

{-
    Σ-equivalence on the dependent component: a pointwise family of
    equivalences in the second factor lifts to an equivalence of
    Σ-types over the same base.
-}
Σ-eqv-snd : {A : Type ℓ₁} {B B' : A → Type ℓ₂} →
            ((a : A) → B a ≃ B' a) → Σ A B ≃ Σ A B'
Σ-eqv-snd es .f (a , b) = (a , f (es a) b)
Σ-eqv-snd es .g (a , b) = (a , g (es a) b)
Σ-eqv-snd es .η (a , b) = ap (λ x → (a , x)) (η (es a) b)
Σ-eqv-snd es .h (a , b) = (a , h (es a) b)
Σ-eqv-snd es .ε (a , b) = ap (λ x → (a , x)) (ε (es a) b)

{-
    Heterogeneous equality across an equivalence: `a ≡[ eqv ] b` iff
    the forward map of `eqv` sends `a` to `b`. Propositionally
    equivalent to `_≃_.g eqv b ≡ a` and to the transport along
    `ua eqv`, but stated in the form most convenient for direct
    calculation.
-}
infix 4 _≡[_]_
_≡[_]_ : {A : Type ℓ₁} {B : Type ℓ₂} → A → A ≃ B → B → Type ℓ₂
a ≡[ eqv ] b = f eqv a ≡ b

iscontr : (A : Type ℓ₁) → Type ℓ₁
iscontr A = (Σ A (λ y → (x : A) → x ≡ y))


data Fin {l : Level} : (n : ℕ {l}) → Type l where
  zero : ∀ {n} → Fin (succ n)
  suc  : ∀ {n} → Fin n → Fin (succ n)

{- Additional path / transport / funext lemmas. -}

ap-! : {A : Type ℓ₁} {B : Type ℓ₂} (k : A → B) {x y : A} (p : x ≡ y) →
       ap k (! p) ≡ ! (ap k p)
ap-! k refl = refl

flip-tpt : {A : Type ℓ₁} (P : A → Type ℓ₂) {a b : A} (p : a ≡ b)
           {u : P a} {v : P b} → tpt P p u ≡ v → u ≡ tpt P (! p) v
flip-tpt P refl e = e

tpt-app2 : {A : Type ℓ₁} {B C : A → Type ℓ₂} (k : (a : A) → B a → C a)
           {a₁ a₂ : A} (δ : a₁ ≡ a₂) (b : B a₁) →
           tpt C δ (k a₁ b) ≡ k a₂ (tpt B δ b)
tpt-app2 k refl b = refl

lcancel : {A : Type ℓ₁} {x y z : A} (r : x ≡ y) {p : y ≡ z} {s : x ≡ z} →
          r • p ≡ s → p ≡ ! r • s
lcancel refl e = ! •unitl • e • ! •unitl

ap2-cong : {A : Type ℓ₁} {B : Type ℓ₂} {Z : Type ℓ₃} (m : A → B → Z)
           {a a' : A} {b b' : B} {α α' : a ≡ a'} {β β' : b ≡ b'} →
           α ≡ α' → β ≡ β' → ap2 m α β ≡ ap2 m α' β'
ap2-cong m refl refl = refl

ap-ap2-pair : {A : Type ℓ₁} {A' : Type ℓ₂} {B : Type ℓ₃} {B' : Type ℓ₄}
              (P : A → A') (Q : B → B')
              {a a₂ : A} {b b₂ : B} (α : a ≡ a₂) (β : b ≡ b₂) →
              ap (λ uv → (P (fst uv) , Q (snd uv))) (ap2 _,_ α β)
                ≡ ap2 _,_ (ap P α) (ap Q β)
ap-ap2-pair P Q refl refl = refl

postcomp-ext : {A : Type ℓ₁} {B : Type ℓ₂} {B' : Type ℓ₃} (k : B → B')
               {r s : A → B} (e : (x : A) → r x ≡ s x) →
               ap (λ t x → k (t x)) (ext e) ≡ ext (λ x → ap k (e x))
postcomp-ext {A = A} k {r} {s} e = happly-inj (ext pw)
  where
    pw : (x : A) → happly (ap (λ t x → k (t x)) (ext e)) x
                     ≡ happly (ext (λ x → ap k (e x))) x
    pw x = happly-ap-double-∘ {f = k} {g = λ t → t} (ext e) x
         • ap (ap k) (! (happly-ap (ext e) x) • happlyExt e x)
         • ! (happlyExt (λ x → ap k (e x)) x)

tpt-pi-dom : {Dom : Type ℓ₁} {Cod : Type ℓ₂} {Pm : Cod → Type ℓ₃} {u v : Dom → Cod}
             (e : u ≡ v) (hh : (d : Dom) → Pm (u d)) →
             tpt (λ w → (d : Dom) → Pm (w d)) e hh
               ≡ (λ d → tpt Pm (happly e d) (hh d))
tpt-pi-dom refl hh = refl

tpt-×-ap2 : {A : Type ℓ₁} {B : Type ℓ₂} (G : A → Type ℓ₃) (H : B → Type ℓ₄)
            {a a' : A} {b b' : B} (α : a ≡ a') (β : b ≡ b')
            (g : G a) (h : H b) →
            tpt (λ ab → G (fst ab) × H (snd ab)) (ap2 _,_ α β) (g , h)
              ≡ (tpt G α g , tpt H β h)
tpt-×-ap2 G H refl refl g h = refl

{- The two triangle identities of a bi-invertible map. -}

module _ {C : Type ℓ₁} {D : Type ℓ₂} (eqv : C ≃ D) where
  private
    ff = f eqv
    gg = g eqv

  -- `ap ff` reflects equality of paths, since gg is a retraction of ff.
  apf-inj : {a b : C} {p q : a ≡ b} → ap ff p ≡ ap ff q → p ≡ q
  apf-inj {a} {b} {p} {q} e =
      recover p
    • ap (λ z → ! (η eqv a) • (z • η eqv b))
         (ap-∘ {f = gg} {g = ff} p • ap (ap gg) e • ! (ap-∘ {f = gg} {g = ff} q))
    • ! (recover q)
    where
      recover : (r : a ≡ b) → r ≡ ! (η eqv a) • (ap (λ x → gg (ff x)) r • η eqv b)
      recover r = lcancel (η eqv a) (hnat-id {B = C} {f = λ x → gg (ff x)} (η eqv) r)

  -- The second (g-side) triangle, derived from `coh` (the f-side one).
  gtri : (y : D) → η eqv (gg y) ≡ ap gg (ε'' eqv y)
  gtri y = apf-inj chain
    where
      chain : ap ff (η eqv (gg y)) ≡ ap ff (ap gg (ε'' eqv y))
      chain = coh eqv (gg y)
            • hnat {f = λ z → ff (gg z)} (ε'' eqv) y
            • ap-∘ {f = ff} {g = gg} (ε'' eqv y)

{-
    Bi-invertibility is property-like: two equivalences with equal
    forward maps are equal (`≃-≡-intro`). Route: fibers of a
    bi-invertible map are contractible (via the half-adjoint
    coherence `coh`), and pre/post-composition by an equivalence is
    an equivalence, so the spaces of left and of right inverses of
    a fixed forward map are contractible — the bi-invertibility
    structure over it is a proposition.
-}

fib : {A B : Type ℓ₁} (k : A → B) → B → Type ℓ₁
fib {A = A} k b = Σ A (λ a → k a ≡ b)

retract-contr : {A B : Type ℓ₁} (r : A → B) (s : B → A) →
                ((b : B) → r (s b) ≡ b) → iscontr A → iscontr B
retract-contr r s rs (c , p) = r c , (λ b → ! (rs b) • ap r (p (s b)))

-- Fibers of a bi-invertible map are contractible.
biinv-fib-contr : {A B : Type ℓ₁} (e : A ≃ B) (b : B) →
                  iscontr (fib (f e) b)
biinv-fib-contr {A = A} {B} e b = (g e b , ε'' e b) , contr
  where
    ff = f e
    gg = g e
    contr : (w : fib (f e) b) → w ≡ (g e b , ε'' e b)
    contr (a , p) = Σ-≡-intro q r
      where
        q : a ≡ gg b
        q = ! (η e a) • ap gg p

        apfq : ap ff q ≡ ! (ε'' e (ff a)) • ap (λ y → ff (gg y)) p
        apfq = ap-• ff (! (η e a)) (ap gg p)
             • ap2 (λ u v → u • v)
                   (ap-! ff (η e a) • ap ! (coh e a))
                   (! (ap-∘ {f = ff} {g = gg} p))

        key : ap ff q • ε'' e b ≡ p
        key = ap (_• ε'' e b) apfq
            • •assoc {p = ! (ε'' e (ff a))} {q = ap (λ y → ff (gg y)) p} {r = ε'' e b}
            • ap (! (ε'' e (ff a)) •_)
                 (! (hnat-id {B = B} {f = λ y → ff (gg y)} (ε'' e) p))
            • ! (•assoc {p = ! (ε'' e (ff a))} {q = ε'' e (ff a)} {r = p})
            • ap (_• p) (•invl {e = ε'' e (ff a)})
            • •unitl

        r : tpt (λ a' → ff a' ≡ b) q p ≡ ε'' e b
        r = tpt-path ff (λ _ → b) q p
          • ap (λ z → ! (ap ff q) • p • z) (ap-const q)
          • ap (! (ap ff q) •_) (•unitr {e = p})
          • ! (lcancel (ap ff q) key)

-- Precomposition by an equivalence is an equivalence
-- (dual of `→-eqv-r`).
precomp-eqv : {X Y : Type ℓ₁} {Z : Type ℓ₂} → X ≃ Y → (Y → Z) ≃ (X → Z)
precomp-eqv e .f r = r ∘ f e
precomp-eqv e .g s = s ∘ g e
precomp-eqv e .η r = ext (λ y → ap r (ε'' e y))
precomp-eqv e .h s = s ∘ h e
precomp-eqv e .ε s = ext (λ x → ap s (! (g~h e (f e x)) • η e x))

-- Left and right inverses of a fixed map.
Linv : {X Y : Type ℓ₁} (k : X → Y) → Type ℓ₁
Linv {X = X} {Y} k = Σ (Y → X) (λ gg → (x : X) → gg (k x) ≡ x)

Rinv : {X Y : Type ℓ₁} (k : X → Y) → Type ℓ₁
Rinv {X = X} {Y} k = Σ (Y → X) (λ hh → (y : Y) → k (hh y) ≡ y)

-- Both inverse spaces of an equivalence's forward map are
-- contractible: each is (up to funext) a fiber of pre- resp.
-- post-composition by the map, over the identity.
Linv-contr : {X Y : Type ℓ₁} (e : X ≃ Y) → iscontr (Linv (f e))
Linv-contr {X = X} {Y} e =
    retract-contr fromFib toFib rt (biinv-fib-contr (precomp-eqv e) (λ x → x))
  where
    fromFib : fib (f (precomp-eqv e)) (λ x → x) → Linv (f e)
    fromFib (gg , pe) = (gg , happly pe)
    toFib : Linv (f e) → fib (f (precomp-eqv e)) (λ x → x)
    toFib (gg , ee) = (gg , ext ee)
    rt : (w : Linv (f e)) → fromFib (toFib w) ≡ w
    rt (gg , ee) = ap (λ z → (gg , z)) (ext (λ x → happlyExt ee x))

Rinv-contr : {X Y : Type ℓ₁} (e : X ≃ Y) → iscontr (Rinv (f e))
Rinv-contr {X = X} {Y} e =
    retract-contr fromFib toFib rt (biinv-fib-contr (→-eqv-r e) (λ y → y))
  where
    fromFib : fib (f (→-eqv-r e)) (λ y → y) → Rinv (f e)
    fromFib (hh , pe) = (hh , happly pe)
    toFib : Rinv (f e) → fib (f (→-eqv-r e)) (λ y → y)
    toFib (hh , ee) = (hh , ext ee)
    rt : (w : Rinv (f e)) → fromFib (toFib w) ≡ w
    rt (hh , ee) = ap (λ z → (hh , z)) (ext (λ y → happlyExt ee y))

-- The bi-invertibility structure over a fixed map, and its
-- repackaging as an equivalence.
Biinv : {X Y : Type ℓ₁} (k : X → Y) → Type ℓ₁
Biinv k = Linv k × Rinv k

mk≃ : {X Y : Type ℓ₁} (k : X → Y) → Biinv k → X ≃ Y
mk≃ k b = record { f = k ; g = fst (fst b) ; η = snd (fst b)
                 ; h = fst (snd b) ; ε = snd (snd b) }

-- Given any witness that `k` is bi-invertible, `Biinv k` is a
-- proposition (both factors are contractible).
Biinv-prop : {X Y : Type ℓ₁} (k : X → Y) → Biinv k →
             (b₁ b₂ : Biinv k) → b₁ ≡ b₂
Biinv-prop k b₀ b₁ b₂ =
    ap2 _,_ (snd lc (fst b₁) • ! (snd lc (fst b₂)))
            (snd rc (snd b₁) • ! (snd rc (snd b₂)))
  where
    e₀ = mk≃ k b₀
    lc : iscontr (Linv k)
    lc = Linv-contr e₀
    rc : iscontr (Rinv k)
    rc = Rinv-contr e₀

-- Two equivalences with equal forward maps are equal.
≃-≡-intro : {X Y : Type ℓ₁} (e₁ e₂ : X ≃ Y) → f e₁ ≡ f e₂ → e₁ ≡ e₂
≃-≡-intro {X = X} {Y} e₁ e₂ p =
    helper (f e₁) (f e₂) p (biinvOf e₁) (biinvOf e₂)
  where
    biinvOf : (e : X ≃ Y) → Biinv (f e)
    biinvOf e = ((g e , η e) , (h e , ε e))
    helper : (k₁ k₂ : X → Y) (q : k₁ ≡ k₂)
             (b₁ : Biinv k₁) (b₂ : Biinv k₂) →
             mk≃ k₁ b₁ ≡ mk≃ k₂ b₂
    helper k .k refl b₁ b₂ = ap (mk≃ k) (Biinv-prop k b₁ b₁ b₂)
