{-# OPTIONS --cubical --guardedness --safe #-}

{-
   Polynomial-functor coalgebras and the characterisation of M as a
   final coalgebra.

   Layered on top of `coinductive-repair.mtype`, which supplies the
   M-type itself, M-coind, paths, Σ, and `_≃_`.

   Structure:

     1. The polynomial endofunctor `P A B`, coalgebras `P-Coalg`,
        coalgebra homomorphisms `isCoalgHom`, and `M` as a P-coalgebra
        via `outM`.
     2. Finality `isFinal`: existence of a coalgebra morphism
        plus function-level uniqueness.  `M-isFinal` proves M
        satisfies this.
     3. Sojakova-style characterisation: a P-coalgebra is final
        iff it satisfies the "M-rules" `rec` / β / η.  Forward and
        backward maps assemble into a genuine type equivalence
        `HasMRules-≃-isFinal` (no extra hypothesis).  The coinduction
        principle `coind` is not a rule but is *derived* from the others
        (`HasMRules-coind`).
     4. Carrier-level corollary: every final P-coalgebra has
        carrier isomorphic to M A B (`M-Final-Iso`).
     5. The strong (homotopy) finality property `isHFinal`
        and the M-specific specialisation of coind-from-isFinal.
-}

module coinductive-repair.coalg where

open import Agda.Primitive
  using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import Agda.Primitive.Cubical
  using (I; i0; i1; primHComp)
  renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_;
            primTransp to transp)
open import coinductive-repair.mtype public

private variable
  ℓ ℓ' ℓ'' : Level

{-
   Polynomial functor and coalgebras.
-}

-- Polynomial functor, coalgebras, and coalgebra morphisms.
P : (A : Type ℓ) → (A → Type ℓ) → Type ℓ → Type ℓ
P A B X = Σ A (λ a → B a → X)

P-mor : {A : Type ℓ} {B : A → Type ℓ} {X Y : Type ℓ}
      → (X → Y) → P A B X → P A B Y
P-mor f (a , p) = (a , λ b → f (p b))

-- Definition 4.1 (Coalgebra)
P-Coalg : (A : Type ℓ) (B : A → Type ℓ) → Type (lsuc ℓ)
P-Coalg {ℓ} A B = Σ (Type ℓ) (λ C → C → P A B C)

CoalgCarrier : {A : Type ℓ} {B : A → Type ℓ} → P-Coalg A B → Type ℓ
CoalgCarrier C = fst C

CoalgOut : {A : Type ℓ} {B : A → Type ℓ} (C : P-Coalg A B)
         → CoalgCarrier C → P A B (CoalgCarrier C)
CoalgOut C = snd C

-- Definition 4.4 (Coalgebra Homomorphism)
isCoalgHom : {A : Type ℓ} {B : A → Type ℓ}
             (C₁ C₂ : P-Coalg A B) → (CoalgCarrier C₁ → CoalgCarrier C₂)
           → Type ℓ
isCoalgHom {A = A} {B = B} C₁ C₂ f =
  PathP (λ _ → CoalgCarrier C₁ → P A B (CoalgCarrier C₂))
        (λ x → P-mor f (CoalgOut C₁ x)) (λ x → CoalgOut C₂ (f x))

-- Definition 4.4 (Coalgebra Homomorphism)
-- Bundled coalgebra hom: function together with its is-hom witness.
-- Convenient downstream when one wants a single value to pass around.
CoalgHom : {A : Type ℓ} {B : A → Type ℓ}
         → P-Coalg A B → P-Coalg A B → Type ℓ
CoalgHom C₁ C₂ = Σ (CoalgCarrier C₁ → CoalgCarrier C₂) (isCoalgHom C₁ C₂)

-- M as a P-coalgebra: bundled destructor outM, and a bundled corec
-- wrapping the unbundled `corec` above.
outM : {A : Type ℓ} {B : A → Type ℓ} → M A B → P A B (M A B)
outM m = shape m , pos m

P-corec : {A : Type ℓ} {B : A → Type ℓ} (C : P-Coalg A B)
        → CoalgCarrier C → M A B
P-corec C =
  corec (CoalgCarrier C)
        (λ c → fst (CoalgOut C c))
        (λ c b → snd (CoalgOut C c) b)

corec-isHom : {A : Type ℓ} {B : A → Type ℓ}
              (C : P-Coalg A B)
            → isCoalgHom C (M A B , outM) (P-corec C)
corec-isHom C = λ _ x → P-mor (P-corec C) (CoalgOut C x)

{- Function-level uniqueness: any coalgebra morphism h : D → M agrees
   with P-corec, by M-coind on a relation linking the two. -}
module _ {A : Type ℓ} {B : A → Type ℓ} (C : P-Coalg A B) where
  private
    D = CoalgCarrier C
    e = CoalgOut C
    co : D → M A B
    co = P-corec C

  module Uniq (h : D → M A B)
              (p-hom : isCoalgHom C (M A B , outM) h) where

    shape-p : (x : D) → fst (e x) ≡ shape (h x)
    shape-p x i = fst (p-hom i x)

    pos-p : (x : D) → PathP (λ i → B (shape-p x i) → M A B)
                            (λ b → h (snd (e x) b)) (pos (h x))
    pos-p x i = snd (p-hom i x)

    data R : M A B → M A B → Type ℓ where
      R-intro : (x : D) → R (h x) (co x)

    bridge : (x : D)
             (b₀ : B (shape (h x))) (b₁ : B (fst (e x)))
             (bp : PathP (λ i → B (shape-p x (~ i))) b₀ b₁)
           → h (snd (e x) b₁) ≡ pos (h x) b₀
    bridge x b₀ b₁ bp i = pos-p x i (bp (~ i))

    isBis : ∀ {m₀ m₁} → R m₀ m₁ → bisimMR R m₀ m₁
    shape-≡R (isBis (R-intro x))             = sym (shape-p x)
    pos-R    (isBis (R-intro x)) b₀ b₁ bp    =
      transport (λ i → R (bridge x b₀ b₁ bp i) (co (snd (e x) b₁)))
                (R-intro (snd (e x) b₁))

    pwEq : (x : D) → h x ≡ co x
    pwEq x = M-coind R isBis (R-intro x)

    funEq : h ≡ co
    funEq = funExt pwEq

  uniq-fun : (h : D → M A B) → isCoalgHom C (M A B , outM) h → h ≡ co
  uniq-fun h p-hom = Uniq.funEq h p-hom

{-
   Finality.
-}
-- Definition 4.6 (Final Coalgebra)
-- Finality: existence of a coalgebra morphism plus function-level
-- uniqueness.  M-isFinal proves M satisfies this.
isFinal : {A : Type ℓ} {B : A → Type ℓ} → P-Coalg A B → Type (lsuc ℓ)
isFinal {ℓ = ℓ} {A = A} {B = B} F =
  (C : P-Coalg A B)
  → Σ (Σ (CoalgCarrier C → CoalgCarrier F) (isCoalgHom C F))
      (λ h-pair → (h' : CoalgCarrier C → CoalgCarrier F)
                  (p' : isCoalgHom C F h')
                → fst h-pair ≡ h')

M-isFinal : {A : Type ℓ} {B : A → Type ℓ} → isFinal (M A B , outM)
M-isFinal C =
    (P-corec C , corec-isHom C)
  , λ h p-hom i x → uniq-fun C h p-hom (~ i) x

{-
   Sojakova-style theorem.

   A P-coalgebra (X, xc) is final IF AND ONLY IF it satisfies
   the M-rules — rec, β, η.  This is the coalgebraic dual of Sojakova:
   there, having the dependent eliminator for W is equivalent to being
   a homotopy-initial algebra.  Here, having (rec + β + η) on (X, xc)
   is equivalent to being a final P-coalgebra — and indeed a
   genuine type equivalence, since the coinduction principle is derived
   rather than stored.
-}
-- Definition 4.9 (Bisimulation)
-- General bisimulation record on a type X with destructors (s : X → A)
-- and (p : (x : X) → B (s x) → X), parameterised over a relation R.
-- Field names use `b` prefix to avoid clashing with bisimMR.
record Bisim
  {A : Type ℓ} {B : A → Type ℓ}
  (X : Type ℓ) (s : X → A) (p : (x : X) → B (s x) → X)
  (R : X → X → Type ℓ)
  (x y : X) : Type ℓ where
  field
    b-shape : s x ≡ s y
    b-pos   : (b₀ : B (s x)) (b₁ : B (s y))
              (bp : PathP (λ i → B (b-shape i)) b₀ b₁)
            → R (p x b₀) (p y b₁)
open Bisim public

{- Definition 4.9 (Bisimulation)
   `R` is a bisimulation for the destructors (s, p) when every
   R-related pair is `Bisim`-related. -}
isBisim : {A : Type ℓ} {B : A → Type ℓ}
          (X : Type ℓ) (s : X → A) (p : (x : X) → B (s x) → X)
          (R : X → X → Type ℓ) → Type ℓ
isBisim {B = B} X s p R = ∀ {x y} → R x y → Bisim {B = B} X s p R x y

{- 
  Definition 4.14 (M-Types)
  The M-rules for a type X with destructors (s, p), in traditional
   type-theoretic style: the corecursor `rec`, its two computation
   rules `β-shape` / `β-pos`, and function-level uniqueness `η`.
   The coinduction principle is NOT a field — it is derivable from
   these rules and exposed separately as `HasMRules-coind`. -}
record HasMRules
  {A : Type ℓ} {B : A → Type ℓ}
  (X : Type ℓ)
  (s : X → A) (p : (x : X) → B (s x) → X)
  : Type (lsuc ℓ) where
  field
    rec : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
        → C → X

    β-shape : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C) (c : C)
            → s (rec C sC pC c) ≡ sC c

    β-pos   : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C) (c : C)
            → PathP (λ i → B (β-shape C sC pC c i) → X)
                    (p (rec C sC pC c))
                    (λ b → rec C sC pC (pC c b))

    η : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
        (h : C → X)
        (h-shape : (c : C) → s (h c) ≡ sC c)
        (h-pos   : (c : C) → PathP (λ i → B (h-shape c i) → X)
                                   (p (h c)) (λ b → h (pC c b)))
      → h ≡ rec C sC pC
open HasMRules public

{- Rutten's construction (Proposition 4.10 and the prose after it).
   For a span R on the carrier of (X, xc), `Rel-Total R` is its total
   space Σ x y. R x y, and `isRuttenBisim xc R` says that it carries a
   coalgebra structure for which both projections are coalgebra
   homomorphisms into (X, xc). -}
Rel-Total : {X : Type ℓ} → (X → X → Type ℓ) → Type ℓ
Rel-Total {X = X} R = Σ X (λ x → Σ X (λ y → R x y))

isRuttenBisim : {A : Type ℓ} {B : A → Type ℓ} {X : Type ℓ}
                (xc : X → P A B X) (R : X → X → Type ℓ) → Type ℓ
isRuttenBisim {A = A} {B = B} {X = X} xc R =
  Σ (Rel-Total R → P A B (Rel-Total R)) (λ γR →
      isCoalgHom (Rel-Total R , γR) (X , xc) (λ q → fst q)
    × isCoalgHom (Rel-Total R , γR) (X , xc) (λ q → fst (snd q)))

{- Prose after Proposition 4.10: Bisim supports the construction.
   This is the coalgebra on the total space used by coind-from-isFinal. -}
isBisim→isRuttenBisim :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {xc : X → P A B X}
  → (R : X → X → Type ℓ)
  → isBisim {B = B} X (λ x → fst (xc x)) (λ x b → snd (xc x) b) R
  → isRuttenBisim xc R
isBisim→isRuttenBisim {A = A} {B = B} {X = X} {xc = xc} R isBis =
  R-Coalg , R-fst-hom , R-snd-hom
  where
    R-Coalg : Rel-Total R → P A B (Rel-Total R)
    R-Coalg (x' , y' , r') =
      fst (xc x') ,
      λ b →
        let bis = isBis r'
            b₁ : B (fst (xc y'))
            b₁ = transp (λ k → B (b-shape bis k)) i0 b
            bp : PathP (λ i → B (b-shape bis i)) b b₁
            bp i = transp (λ j → B (b-shape bis (i ∧ j))) (~ i) b
        in snd (xc x') b , snd (xc y') b₁ , b-pos bis b b₁ bp

    R-fst-hom : isCoalgHom (Rel-Total R , R-Coalg) (X , xc) (λ q → fst q)
    R-fst-hom = refl

    R-snd-hom : isCoalgHom (Rel-Total R , R-Coalg) (X , xc) (λ q → fst (snd q))
    R-snd-hom i (x' , y' , r') =
      b-shape (isBis r') i ,
      λ b → snd (xc y') (transp (λ j → B (b-shape (isBis r') (i ∨ j))) i b)

{- Prose after Proposition 4.10: every condition supporting the
   construction implies Bisim.  Reading the two homomorphism squares
   at a point (x , y , r) with γR (x , y , r) = (a , w) gives
   a = shape x and a = shape y, and each w b relates a position of x
   to the matching position of y. -}
private
  span-step :
      {A : Type ℓ} {B : A → Type ℓ} {X : Type ℓ}
      (R : X → X → Type ℓ) {a : A} (w : B a → Rel-Total R)
      {u v : P A B X}
    → _≡_ {A = P A B X} (a , λ b → fst (w b)) u
    → _≡_ {A = P A B X} (a , λ b → fst (snd (w b))) v
    → Σ (fst u ≡ fst v) (λ sh →
        (b₀ : B (fst u)) (b₁ : B (fst v))
        (bp : PathP (λ i → B (sh i)) b₀ b₁)
      → R (snd u b₀) (snd v b₁))
  span-step {A = A} {B = B} {X = X} R {a} w {u} {v} e₁ e₂ =
    J (λ u' _ → Goal u' v) (J (λ v' _ → Goal (a , λ b → fst (w b)) v') base e₂) e₁
    where
      Goal : P A B X → P A B X → Type _
      Goal u' v' =
        Σ (fst u' ≡ fst v') (λ sh →
          (b₀ : B (fst u')) (b₁ : B (fst v'))
          (bp : PathP (λ i → B (sh i)) b₀ b₁)
        → R (snd u' b₀) (snd v' b₁))

      base : Goal (a , λ b → fst (w b)) (a , λ b → fst (snd (w b)))
      base = refl , λ b₀ b₁ bp →
        subst (λ b → R (fst (w b₀)) (fst (snd (w b)))) bp (snd (snd (w b₀)))

isRuttenBisim→isBisim :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {xc : X → P A B X}
  → (R : X → X → Type ℓ)
  → isRuttenBisim xc R
  → isBisim {B = B} X (λ x → fst (xc x)) (λ x b → snd (xc x) b) R
isRuttenBisim→isBisim R (γR , h₁ , h₂) {x} {y} r =
  record { b-shape = fst st ; b-pos = snd st }
  where
    q = (x , y , r)
    st = span-step R (snd (γR q)) (λ i → h₁ i q) (λ i → h₂ i q)

{- Prose after Proposition 4.10: Bisim is the weakest one-step
   condition supporting Rutten's construction.  Any Φ that, holding
   throughout R, yields the construction, implies Bisim; and Bisim
   itself supports the construction (isBisim→isRuttenBisim). -}
Bisim-weakest :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {xc : X → P A B X}
  → (Φ : (X → X → Type ℓ) → X → X → Type ℓ)
  → ((R : X → X → Type ℓ) → (∀ {x y} → R x y → Φ R x y) → isRuttenBisim xc R)
  → (R : X → X → Type ℓ) → (∀ {x y} → R x y → Φ R x y)
  → isBisim {B = B} X (λ x → fst (xc x)) (λ x b → snd (xc x) b) R
Bisim-weakest Φ supports R hR = isRuttenBisim→isBisim R (supports R hR)

{- 
  Proposition 4.10 (Coinduction Principle for Final Coalgebra)
  Finality ⇒ the 1-D coinduction principle, by the
   Rutten graph argument: both graph projections are coalgebra
   morphisms, and finality forces them equal. -}
coind-from-isFinal :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {xc : X → P A B X}
  → isFinal (X , xc)
  → (R : X → X → Type ℓ)
  → (isBis : ∀ {x y} → R x y → Bisim {B = B} X (λ x → fst (xc x))
                                       (λ x b → snd (xc x) b) R x y)
  → ∀ {x y} → R x y → x ≡ y
coind-from-isFinal {A = A} {B = B} {X = X} {xc = xc} wf R isBis {x} {y} r =
  subst (λ a → a ≡ y)
        (λ i → fst-eq i (x , y , r))
        (λ i → snd-eq i (x , y , r))
  where
    rb = isBisim→isRuttenBisim {xc = xc} R isBis

    wf-data = wf (Rel-Total R , fst rb)

    fst-eq : fst (fst wf-data) ≡ (λ q → fst q)
    fst-eq = snd wf-data (λ q → fst q) (fst (snd rb))

    snd-eq : fst (fst wf-data) ≡ (λ q → fst (snd q))
    snd-eq = snd wf-data (λ q → fst (snd q)) (snd (snd rb))

-- Forward: the rules give finality.  rec + β package as a
-- coalgebra morphism; η gives function-level uniqueness.
HasMRules→isFinal :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {s : X → A} {p : (x : X) → B (s x) → X}
  → HasMRules {A = A} { B = B } X s p
  → isFinal {A = A} {B = B} (X , λ x → s x , p x)
HasMRules→isFinal {A = A} {B = B} {X = X} {s = s} {p = p} rules (D , e) =
    (rec rules D sD pD , r-hom)
  , (λ h' h'-hom → sym (η rules D sD pD h'
                          (λ d i → fst (h'-hom (~ i) d))
                          (λ d i → snd (h'-hom (~ i) d))))
  where
    sD : D → A
    sD d = fst (e d)
    pD : (d : D) → B (sD d) → D
    pD d b = snd (e d) b
    r : D → X
    r = rec rules D sD pD
    r-hom : isCoalgHom (D , e) (X , λ x → s x , p x) r
    r-hom i d =
      β-shape rules D sD pD d (~ i) ,
      λ b → β-pos rules D sD pD d (~ i) b

-- Backward: finality gives the rules.  rec, β-shape, β-pos, η read
-- off from the isFinal data.
isFinal→HasMRules :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {s : X → A} {p : (x : X) → B (s x) → X}
  → isFinal {A = A} {B = B} (X , λ x → s x , p x)
  → HasMRules X s p
isFinal→HasMRules {A = A} {B = B} {X = X} {s = s} {p = p} wf = r
  where
    -- The result type is annotated explicitly so the record's implicit
    -- `B` is pinned to the telescope `B` (it is not inferable from
    -- `X`/`s`/`p` alone, and there is no longer a `coind` field to fix it).
    r : HasMRules {A = A} {B = B} X s p
    r = record
      { rec     = λ C sC pC → fst (fst (wf (C , λ c → sC c , pC c)))
      ; β-shape = λ C sC pC c i → fst (snd (fst (wf (C , λ c' → sC c' , pC c'))) (~ i) c)
      ; β-pos   = λ C sC pC c i → snd (snd (fst (wf (C , λ c' → sC c' , pC c'))) (~ i) c)
      ; η       = λ C sC pC h' h-shape h-pos →
                    sym (snd (wf (C , λ c → sC c , pC c)) h'
                           (λ i c → h-shape c (~ i) , λ b → h-pos c (~ i) b))
      }

-- Section 4.3: M itself has the M-rules (the M record's destructors are
-- `shape`/`pos`).
M-HasMRules : {A : Type ℓ} {B : A → Type ℓ} → HasMRules (M A B) shape pos
M-HasMRules = isFinal→HasMRules M-isFinal

-- Definition 4.14 (coinduction is derivable, not a rule)
-- The coinduction principle (bisim ⇒ path) is *derived* from the
-- M-rules, not carried as a field: rec/β/η give finality, and
-- finality yields coind by the Rutten graph argument.
HasMRules-coind :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {s : X → A} {p : (x : X) → B (s x) → X}
  → HasMRules X s p
  → (R : X → X → Type ℓ)
  → (∀ {x y} → R x y → Bisim {B = B} X s p R x y)
  → ∀ {x y} → R x y → x ≡ y
HasMRules-coind rules = coind-from-isFinal (HasMRules→isFinal rules)

{-
  Theorem 4.21 ((Homotopy) M-Types are (Homotopy) Final Coalgebras), part (1)
  HasMRules ≃ isFinal.

-}
HasMRules-≃-isFinal :
    {A : Type ℓ} {B : A → Type ℓ}
    {X : Type ℓ} {s : X → A} {p : (x : X) → B (s x) → X}
  → HasMRules {B = B} X s p ≃ isFinal {A = A} {B = B} (X , λ x → s x , p x)
HasMRules-≃-isFinal {A = A} {B = B} {X = X} {s = s} {p = p} = record
  { fwd      = HasMRules→isFinal
  ; bwd-L    = isFinal→HasMRules
  ; leftInv  = λ rules i → record
      { rec     = rec rules
      ; β-shape = β-shape rules
      ; β-pos   = β-pos rules
      ; η       = η rules
      }
  ; bwd-R    = isFinal→HasMRules
  ; rightInv = λ _ → refl
  }

{-
   Carrier-level corollary: any final coalgebra has carrier
   isomorphic to M A B.  This is weaker than the rules-equivalence
   above; it only sees the underlying type, not the coalgebra structure
   or the rules.
-}

-- Composition of coalgebra morphisms is a coalgebra morphism.
∘-isCoalgHom :
  {A : Type ℓ} {B : A → Type ℓ}
  {C₁ C₂ C₃ : P-Coalg A B}
  {f : CoalgCarrier C₁ → CoalgCarrier C₂}
  {g : CoalgCarrier C₂ → CoalgCarrier C₃}
  → isCoalgHom C₁ C₂ f → isCoalgHom C₂ C₃ g
  → isCoalgHom C₁ C₃ (λ x → g (f x))
∘-isCoalgHom {f = f} {g = g} p q =
  (λ i x → P-mor g (p i x)) ∙ (λ i x → q i (f x))

-- The type of final P A B-coalgebras.
FinalCoalg : (A : Type ℓ) (B : A → Type ℓ) → Type (lsuc ℓ)
FinalCoalg {ℓ = ℓ} A B =
  Σ (Type ℓ) (λ X →
    Σ (X → P A B X) (λ xc →
      isFinal (X , xc)))

M-as-Final : {A : Type ℓ} {B : A → Type ℓ} → FinalCoalg A B
M-as-Final {A = A} {B = B} = (M A B , outM , M-isFinal)

M-Final-Iso :
  {A : Type ℓ} {B : A → Type ℓ}
  → (W : FinalCoalg A B) → Iso (M A B) (fst W)
M-Final-Iso {A = A} {B = B} (X , xc , wX) = record
  { fwd      = g-fun
  ; bwd-L    = f-fun
  ; leftInv  = λ m → λ i → ((sym fg-eq) ∙ idM-eq) i m
  ; bwd-R    = f-fun
  ; rightInv = λ x → λ i → ((sym gf-eq) ∙ idX-eq) i x
  }
  where
    M-coalg : P-Coalg A B
    M-coalg = (M A B , outM)

    -- f : X → M and g : M → X from the two corecs.
    f-data = M-isFinal (X , xc)
    f-fun  : X → M A B
    f-fun  = fst (fst f-data)
    f-hom  : isCoalgHom (X , xc) M-coalg f-fun
    f-hom  = snd (fst f-data)

    g-data = wX M-coalg
    g-fun  : M A B → X
    g-fun  = fst (fst g-data)
    g-hom  : isCoalgHom M-coalg (X , xc) g-fun
    g-hom  = snd (fst g-data)

    -- id and round-trips as coalgebra morphisms.
    idX-hom : isCoalgHom (X , xc) (X , xc) (λ x → x)
    idX-hom = refl
    idM-hom : isCoalgHom M-coalg M-coalg (λ x → x)
    idM-hom = refl
    gf-hom  : isCoalgHom (X , xc) (X , xc) (λ x → g-fun (f-fun x))
    gf-hom  = ∘-isCoalgHom {C₁ = X , xc} {C₂ = M-coalg} {C₃ = X , xc}
                            {f = f-fun} {g = g-fun} f-hom g-hom
    fg-hom  : isCoalgHom M-coalg M-coalg (λ m → f-fun (g-fun m))
    fg-hom  = ∘-isCoalgHom {C₁ = M-coalg} {C₂ = X , xc} {C₃ = M-coalg}
                            {f = g-fun} {g = f-fun} g-hom f-hom

    -- Uniqueness identifies the round-trips with id.
    idX-eq : fst (fst (wX (X , xc))) ≡ (λ x → x)
    idX-eq = snd (wX (X , xc)) (λ x → x) idX-hom
    gf-eq  : fst (fst (wX (X , xc))) ≡ (λ x → g-fun (f-fun x))
    gf-eq  = snd (wX (X , xc)) _ gf-hom
    idM-eq : fst (fst (M-isFinal M-coalg)) ≡ (λ x → x)
    idM-eq = snd (M-isFinal M-coalg) (λ x → x) idM-hom
    fg-eq  : fst (fst (M-isFinal M-coalg)) ≡ (λ m → f-fun (g-fun m))
    fg-eq  = snd (M-isFinal M-coalg) _ fg-hom

{-
   Homotopy finality.

   (a) isHFinal: the strong (homotopy) finality property,
       requiring contractibility of the morphism space.  Not provable
       in plain Cubical Agda for a general polynomial — see the 2-D
       obstacle discussed at `bisim2DR` in `coinductive-repair.mtype`.
   (b) M-coind-from-isFinal: M-specific specialisation of the
       general coind-from-isFinal proven above in the main flow.
-}

-- Definition 4.7 (Homotopy-Final Coalgebra)
-- (a) Strong (homotopy) finality — uniqueness up to a Σ-Path including
-- the homomorphism-witness component.  Cannot be proven for general M
-- without extra hypotheses (e.g. A : Set, à la Cubical.Codata.Containers).
isHFinal : {A : Type ℓ} {B : A → Type ℓ} → P-Coalg A B → Type (lsuc ℓ)
isHFinal {A = A} {B = B} F =
  (C : P-Coalg A B)
  → Σ (Σ (CoalgCarrier C → CoalgCarrier F) (isCoalgHom C F))
      (λ h → (g : Σ (CoalgCarrier C → CoalgCarrier F) (isCoalgHom C F)) → h ≡ g)

{- Specialisation of coind-from-isFinal to (M, outM): recovers
   M-coind from finality of M. -}
M-coind-from-isFinal :
    {A : Type ℓ} {B : A → Type ℓ}
  → isFinal (M A B , outM)
  → (R : M A B → M A B → Type ℓ)
  → (isBis : ∀ {m₀ m₁} → R m₀ m₁ → bisimMR R m₀ m₁)
  → ∀ {m₀ m₁} → R m₀ m₁ → m₀ ≡ m₁
M-coind-from-isFinal wf R isBis =
  coind-from-isFinal wf R
    (λ r → record { b-shape = shape-≡R (isBis r)
                  ; b-pos   = pos-R    (isBis r) })


{-
   HasMRules + M-coind-2D  ≃  isHFinal M.

   The strong (homotopy) finality of M is *equivalent* to having
   the 1-D M-rules (`HasMRules`) plus the 2-D coinduction
   principle `M-coind-2D`. We've already shown:

     • `HasMRules M shape pos` is provable from `M-isFinal`
       (via `M-HasMRules`), so it's automatic.
     • The remaining content of `isHFinal` beyond
       `isFinal` is the *Σ-level uniqueness* of coalg-homs
       — i.e., the hom-witness PathP coherence over the
       function path. That extra coherence is precisely what a
       2-D coinduction principle provides.

   Below we make the equivalence concrete:

       `M-Coind-2D-Type ≃ isHFinal (M A B , outM)`

   as types, with the 2-D principle reified as a type rather than
   assumed as a rule.
   The forward direction (`M-Coind-2D-Type → isHFinal`)
   upgrades the M-isFinal function path to a Σ-path by
   building the hom-witness PathP via the 2-D principle. The
   backward direction (`isHFinal → M-Coind-2D-Type`)
   discharges the 2-D principle by an "outer Rutten"
   construction: build a coalgebra on the 2-D-graph carrier,
   both 2-projections are coalg-homs into M, contractibility
   of the coalg-hom space forces them equal as Σ-elements, and
   extracting the path gives the 2-D PathP.
-}

-- The signature of a 2-D coinduction principle reified as a type,
-- so we can *quantify over* and *prove* equivalences involving 2-D
-- coinduction (rather than assuming it as a rule).
M-Coind-2D-Type : {A : Type ℓ} {B : A → Type ℓ} → Type (lsuc ℓ)
M-Coind-2D-Type {ℓ = ℓ} {A = A} {B = B} =
  (R₂ : {X₀ X₁ Y₀ Y₁ : M A B}
        (px : X₀ ≡ X₁) (py : Y₀ ≡ Y₁)
        (p : X₀ ≡ Y₀) (q : X₁ ≡ Y₁) → Type ℓ)
  (isBis : {X₀ X₁ Y₀ Y₁ : M A B}
           {px : X₀ ≡ X₁} {py : Y₀ ≡ Y₁}
           {p : X₀ ≡ Y₀} {q : X₁ ≡ Y₁}
         → R₂ px py p q → bisim2DR R₂ px py p q)
  → {X₀ X₁ Y₀ Y₁ : M A B}
    {px : X₀ ≡ X₁} {py : Y₀ ≡ Y₁}
    {p : X₀ ≡ Y₀} {q : X₁ ≡ Y₁}
  → R₂ px py p q → PathP (λ j → px j ≡ py j) p q

{-
   (⇐)  isHFinal (M, outM)  →  M-Coind-2D-Type.

   Given homotopy-finality of M, the 2-D coinduction
   principle is derivable. Outer Rutten construction:

     • For any 2-bisim R₂ and witness `r : R₂ px py p q`,
       form the "2-D graph carrier": the type of 4-tuples
       of paths in M together with R₂-witnesses. Equip with
       a P-coalgebra structure whose destructor is built
       from the 2-D bisim's `shape-2D-R` and `pos-2D-R`
       fields (in parallel to `R-Coalg` in
       `coind-from-isFinal`).

     • The two "2-projections" — sending a 4-tuple of paths
       to `px` (or `py`) — are coalg-homs from this 2-D
       graph coalgebra into (M, outM). Their hom witnesses
       are square-of-squares constructions analogous to
       `R-fst-hom` and `R-snd-hom`.

     • By `isHFinal` applied to the 2-D graph coalgebra,
       the two 2-projections are equal as *Σ-elements*
       (function + hom witness). Extract the function-level
       path, evaluate at the original `r` witness, and
       reassemble — that path is exactly the 2-D PathP from
       `p` to `q` over `px ⇄ py` that `M-coind-2D` outputs.

   This is the dual chase of the (⇒) direction; it shares the
   same 2-bisim setup in reverse.
-}

module isHFinal→M-Coind-2D-Proof
    {A : Type ℓ} {B : A → Type ℓ}
    (iFC : isHFinal {A = A} {B = B} (M A B , outM)) where

  {-
      Local abbreviations for the 2-relation signature and
      its bisim2DR-witness signature — the parameters of
      `M-coind-2D` everywhere.
  -}
  R2Type : Type (lsuc ℓ)
  R2Type =
    {X₀ X₁ Y₀ Y₁ : M A B}
    (px : X₀ ≡ X₁) (py : Y₀ ≡ Y₁)
    (p : X₀ ≡ Y₀) (q : X₁ ≡ Y₁) → Type ℓ

  isBisType : R2Type → Type ℓ
  isBisType R₂ =
    {X₀ X₁ Y₀ Y₁ : M A B}
    {px : X₀ ≡ X₁} {py : Y₀ ≡ Y₁}
    {p : X₀ ≡ Y₀} {q : X₁ ≡ Y₁}
    → R₂ px py p q → bisim2DR R₂ px py p q

  {-
      The 2-D graph carrier: 4-tuples of M-elements,
      together with 4 paths between them forming a square,
      together with an `R₂`-witness on those paths.

      Indexed by the 2-bisim relation `R₂` we want to
      close. A coalgebra on this carrier turns the
      square's structure (via `shape-2D-R` and `pos-2D-R`
      from `isBis`) into recursive square-data at one
      destructor depth.
  -}
  Graph2D : R2Type → Type ℓ
  Graph2D R₂ =
    Σ (M A B) (λ X₀ →
    Σ (M A B) (λ X₁ →
    Σ (M A B) (λ Y₀ →
    Σ (M A B) (λ Y₁ →
    Σ (X₀ ≡ X₁) (λ px →
    Σ (Y₀ ≡ Y₁) (λ py →
    Σ (X₀ ≡ Y₀) (λ p →
    Σ (X₁ ≡ Y₁) (λ q →
        R₂ {X₀} {X₁} {Y₀} {Y₁} px py p q))))))))

  {-
      Coalgebra structure on `Graph2D R₂`, given an `isBis`
      witness saying every `R₂`-square's destructors form a
      2-D bisim.

      From a square `(X₀, X₁, Y₀, Y₁, px, py, p, q, r)`,
      the bisim2DR data yields:

        • `shape-2D-R (isBis r)` — a 2-cell in A on the
          shapes of the corners. We pick the (j=0, k=0)
          corner's A-component `shape X₀ = shape (px 0)`
          to seed the P-coalgebra's `fst`.

        • `pos-2D-R (isBis r)` — given 4 b-values and 4
          PathPs, produces an `R₂`-witness on the next
          destructor depth. This becomes the P-coalgebra's
          `snd`: at each `b₀₀ : B (shape X₀)`, transport
          through the bisim2D data to derive recursive
          square data, then pack as another `Graph2D R₂`
          element.

      Concrete construction below: pick the (0,0) corner's
      shape as the seed A-value; at each `b₀₀ : B (shape X₀)`,
      derive `b₀₁, b₁₀, b₁₁` via standard `subst-filler`s
      along `shape ∘ p`, `shape ∘ px`, and the diagonal of
      `shape-2D-R (isBis r)`, then call `pos-2D-R (isBis r)`
      to produce the recursive `R₂`-witness, and pack
      everything as the next `Graph2D R₂` element.
  -}
  graph2D-coalg :
    (R₂ : R2Type) (isBis : isBisType R₂) →
    Graph2D R₂ → P A B (Graph2D R₂)
  graph2D-coalg R₂ isBis
      (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
    shape X₀ , next-square
    where
      bisR : bisim2DR R₂ px py p q
      bisR = isBis r

      next-square : B (shape X₀) → Graph2D R₂
      next-square b₀₀ =
          pos X₀ b₀₀
        , pos X₁ b₁₀
        , pos Y₀ b₀₁
        , pos Y₁ b₁₁
        , (λ j → pos (px j) (bpx j))
        , (λ j → pos (py j) (bpy j))
        , (λ i → pos (p  i) (bp  i))
        , (λ i → pos (q  i) (bq  i))
        , pos-2D-R bisR b₀₀ b₀₁ b₁₀ b₁₁ bp bq bpx bpy
        where
          {-
              The four corner b-values: `b₀₀` is given; we
              derive `b₁₀` along `shape ∘ px`, `b₀₁` along
              `shape ∘ p`, and `b₁₁` along the diagonal of
              `shape-2D-R bisR`.
          -}
          bpx : PathP (λ j → B (shape (px j))) b₀₀ _
          bpx j = transp (λ k → B (shape (px (j ∧ k)))) (~ j) b₀₀

          b₁₀ : B (shape X₁)
          b₁₀ = bpx i1

          bp : PathP (λ i → B (shape (p i))) b₀₀ _
          bp i = transp (λ k → B (shape (p (i ∧ k)))) (~ i) b₀₀

          b₀₁ : B (shape Y₀)
          b₀₁ = bp i1

          {-
              `bq` and `bpy` use `shape-2D-R bisR` as a
              2-cell "track" for transport, parameterised so
              the boundary endpoints match `b₁₀` / `b₀₁` /
              and a single shared `b₁₁` *definitionally*.

              `shape-2D-R bisR` is a 2-cell in `A` with
              corners

                (0,0)  shape X₀     (1,0)  shape X₁
                (0,1)  shape Y₀     (1,1)  shape Y₁

              Edges: `shape ∘ px` along i=0, `shape ∘ py`
              along i=1, `shape ∘ p` along j=0, `shape ∘ q`
              along j=1. (Note the convention here matches
              `bisim2DR`'s field, where the PathP outer
              parameter is `j` and the inner Path index is
              `i`.)

              The "track" `λ l → shape-2D-R bisR α(l) β(l)`
              traces a path through the 2-cell from `(0,0)`
              at `l=0` to a chosen endpoint at `l=1`,
              passing through specific edges depending on
              `α, β`.

              `b₁₁` is defined as the result of running the
              `bq`-track all the way (which equals the
              `bpy`-track endpoint by virtue of the same
              transport landing at `shape Y₁`). This makes
              both PathPs concrete and their (i=1)/(j=1)
              endpoints coincide on the nose.
          -}
          b₁₁ : B (shape Y₁)
          b₁₁ = transp (λ l → B (shape-2D-R bisR l l)) i0 b₀₀

          bq  : PathP (λ i → B (shape (q i))) b₁₀ b₁₁
          bq i =
            transp (λ l → B (shape-2D-R bisR l (i ∧ l))) i0 b₀₀

          bpy : PathP (λ j → B (shape (py j))) b₀₁ b₁₁
          bpy j =
            transp (λ l → B (shape-2D-R bisR (j ∧ l) l)) i0 b₀₀

  {-
      The four "corner projections" — each `proj-X` maps a
      `Graph2D R₂` element to the corresponding corner
      `M A B`. Each is concretely a Σ-projection chain.
  -}
  proj-X₀ : (R₂ : R2Type) → Graph2D R₂ → M A B
  proj-X₀ _ g = fst g

  proj-X₁ : (R₂ : R2Type) → Graph2D R₂ → M A B
  proj-X₁ _ g = fst (snd g)

  proj-Y₀ : (R₂ : R2Type) → Graph2D R₂ → M A B
  proj-Y₀ _ g = fst (snd (snd g))

  proj-Y₁ : (R₂ : R2Type) → Graph2D R₂ → M A B
  proj-Y₁ _ g = fst (snd (snd (snd g)))

  {-
      Each projection should be a coalgebra-hom from
      `(Graph2D R₂, graph2D-coalg R₂ isBis)` into `(M, outM)`.
      Concretely the hom-witness comes from
      `bisim2DR (isBis r)`'s destruction at the
      corresponding corner.

      The four projections are coalg-homs, proved below:
      each proof unfolds `graph2D-coalg`'s definition and
      matches against `outM` of the corresponding corner.
  -}
  {-
      `proj-X₀` is the "seed corner": `graph2D-coalg`
      uses `shape X₀` as the A-value and packs `pos X₀ b₀₀`
      as `next-square b₀₀`'s X₀-component. So
      `P-mor proj-X₀ (graph2D-coalg g) = (shape X₀,
       λ b → pos X₀ b) = outM (proj-X₀ g)` on the nose.
  -}
  proj-X₀-hom :
    (R₂ : R2Type) (isBis : isBisType R₂) →
    isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (proj-X₀ R₂)
  proj-X₀-hom R₂ isBis = refl

  {-
      The other three projections are NOT strict coalg-homs:
      their A-component disagrees with `shape X₀` (the seed
      coalgebra's A-value), and the disagreement is exactly
      mediated by `shape-2D-R`'s 2-cell. The hom witnesses
      thread the appropriate edge of `shape-2D-R` through
      the A-component and transport-along-it through the
      B-component, paralleling `R-snd-hom` in
      `coind-from-isFinal` lifted to 2-D.
  -}

  proj-X₁-hom :
    (R₂ : R2Type) (isBis : isBisType R₂) →
    isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (proj-X₁ R₂)
  proj-X₁-hom R₂ isBis i (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
    shape (px i)
    , λ b → pos X₁ (transp (λ j → B (shape (px (i ∨ j)))) i b)

  proj-Y₀-hom :
    (R₂ : R2Type) (isBis : isBisType R₂) →
    isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (proj-Y₀ R₂)
  proj-Y₀-hom R₂ isBis i (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
    shape (p i)
    , λ b → pos Y₀ (transp (λ j → B (shape (p (i ∨ j)))) i b)

  proj-Y₁-hom :
    (R₂ : R2Type) (isBis : isBisType R₂) →
    isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (proj-Y₁ R₂)
  proj-Y₁-hom R₂ isBis i (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
    shape-2D-R (isBis r) i i
    , λ b → pos Y₁ (transp (λ j → B (shape-2D-R (isBis r) (i ∨ j) (i ∨ j))) i b)

  {-
      The 2-D extraction step. Given an `R₂`-witness `r`
      with shape `px py p q`, apply `iFC` at the
      `Graph2D R₂` coalgebra to get the center and Σ-paths
      to each projection. The 4 projections give us 4
      "spoke" paths from `center` to the corners (X₀, X₁,
      Y₀, Y₁), and the 2-PathP from `p` to `q` over
      `(px, py)` is the cubical filler whose 4 boundary
      edges are `(p, q, px, py)` and whose interior pivots
      through `center`.

      ─── Implementation plan ───────────────────────────

      With the spokes in hand, the 2-PathP follows from
      an `hcomp` whose base is `center.fst g` and whose
      four faces interpolate from the base out to each
      boundary edge along the corresponding pair of
      spokes:

        face-j0 k l : connects `center.fst g` (at l=i0) to
          `p k` (at l=i1), with sides `spoke-X₀ l` (at k=i0)
          and `spoke-Y₀ l` (at k=i1).
        face-j1 k l : same but with q, spoke-X₁, spoke-Y₁.
        face-k0 j l : same but with px, spoke-X₀, spoke-X₁.
        face-k1 j l : same but with py, spoke-Y₀, spoke-Y₁.

      Each face is itself a 2-cell defined either by
      another (nested) `hcomp` or by direct cubical
      composition through the spoke-and-edge pairs.

      We extract the spokes below as concrete definitions;
      the final hcomp assembly is `result` at the end of
      this module. The 2-cell coherence connecting
      `spoke-X₀ ∙ p` and `spoke-Y₀` (etc.) is provided by
      the Σ-uniqueness half of `iFC` — specifically, by the
      fact that the 4 projections are Σ-equal to the unique
      `center`.
  -}

  module ExtractCenter
      (R₂ : R2Type) (isBis : isBisType R₂)
      {X₀ X₁ Y₀ Y₁ : M A B}
      {px : X₀ ≡ X₁} {py : Y₀ ≡ Y₁}
      {p : X₀ ≡ Y₀} {q : X₁ ≡ Y₁}
      (r : R₂ px py p q) where

    g : Graph2D R₂
    g = X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r

    iFC-data = iFC (Graph2D R₂ , graph2D-coalg R₂ isBis)

    center : Σ (Graph2D R₂ → M A B)
               (isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis)
                           (M A B , outM))
    center = fst iFC-data

    center-fn : Graph2D R₂ → M A B
    center-fn = fst center

    uniq :
      (g' : Σ (Graph2D R₂ → M A B)
              (isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis)
                          (M A B , outM))) →
      center ≡ g'
    uniq = snd iFC-data

    {-
        The four Σ-paths to each projection.
    -}
    σ-X₀ : center ≡ (proj-X₀ R₂ , proj-X₀-hom R₂ isBis)
    σ-X₀ = uniq (proj-X₀ R₂ , proj-X₀-hom R₂ isBis)

    σ-X₁ : center ≡ (proj-X₁ R₂ , proj-X₁-hom R₂ isBis)
    σ-X₁ = uniq (proj-X₁ R₂ , proj-X₁-hom R₂ isBis)

    σ-Y₀ : center ≡ (proj-Y₀ R₂ , proj-Y₀-hom R₂ isBis)
    σ-Y₀ = uniq (proj-Y₀ R₂ , proj-Y₀-hom R₂ isBis)

    σ-Y₁ : center ≡ (proj-Y₁ R₂ , proj-Y₁-hom R₂ isBis)
    σ-Y₁ = uniq (proj-Y₁ R₂ , proj-Y₁-hom R₂ isBis)

    {-
        The four "spokes": paths in `M A B` from
        `center-fn g` to each corner.
    -}
    spoke-X₀ : center-fn g ≡ X₀
    spoke-X₀ k = fst (σ-X₀ k) g

    spoke-X₁ : center-fn g ≡ X₁
    spoke-X₁ k = fst (σ-X₁ k) g

    spoke-Y₀ : center-fn g ≡ Y₀
    spoke-Y₀ k = fst (σ-Y₀ k) g

    spoke-Y₁ : center-fn g ≡ Y₁
    spoke-Y₁ k = fst (σ-Y₁ k) g

    {-
        The four EDGE-PARAMETERISED projections + hom-witnesses.
        Each `e-fn-X`-style projection is a k-(or j-)family of
        functions Graph2D R₂ → M A B; at k=0/i1 it matches one
        of the corner projections (proj-X₀ etc.), and for
        interior k it gives the edge value at that interval.
        Each comes with a hom-witness threading the appropriate
        shape-edge (px / py / p / q) through the A-component and
        a matching transp through the B-component.
    -}
    p-fn : (k : I) → Graph2D R₂ → M A B
    p-fn k g = fst (snd (snd (snd (snd (snd (snd g)))))) k

    p-fn-hom : (k : I) →
      isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (p-fn k)
    p-fn-hom k i (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
      shape (p (i ∧ k)) ,
      λ b → pos (p k) (transp (λ j → B (shape (p (k ∧ (i ∨ j))))) (i ∨ ~ k) b)

    q-fn : (k : I) → Graph2D R₂ → M A B
    q-fn k g = fst (snd (snd (snd (snd (snd (snd (snd g))))))) k

    q-fn-hom : (k : I) →
      isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (q-fn k)
    q-fn-hom k i (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
      shape-2D-R (isBis r) i (k ∧ i) ,
      λ b → pos (q k) (transp (λ l → B (shape-2D-R (isBis r) (i ∨ l) (k ∧ (i ∨ l)))) i b)
    -- NOTE: q's bq uses φ = i0; the (i ∨ l)-track makes our transp at i=i0
    -- coincide with bq, and at i=i1 reduces to identity. Confirmed at endpoints.

    px-fn : (j : I) → Graph2D R₂ → M A B
    px-fn j g = fst (snd (snd (snd (snd g)))) j

    px-fn-hom : (j : I) →
      isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (px-fn j)
    px-fn-hom j i (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
      shape (px (i ∧ j)) ,
      λ b → pos (px j) (transp (λ k → B (shape (px (j ∧ (i ∨ k))))) (i ∨ ~ j) b)

    py-fn : (j : I) → Graph2D R₂ → M A B
    py-fn j g = fst (snd (snd (snd (snd (snd g))))) j

    py-fn-hom : (j : I) →
      isCoalgHom (Graph2D R₂ , graph2D-coalg R₂ isBis) (M A B , outM) (py-fn j)
    py-fn-hom j i (X₀ , X₁ , Y₀ , Y₁ , px , py , p , q , r) =
      shape-2D-R (isBis r) (j ∧ i) i ,
      λ b → pos (py j) (transp (λ l → B (shape-2D-R (isBis r) ((i ∨ l) ∧ j) (i ∨ l))) i b)

    {-
        σ-paths for each edge, by `uniq`. At the endpoints (k=0/1
        or j=0/1) these reduce to the corner σ-paths σ-X₀, σ-X₁,
        σ-Y₀, σ-Y₁ above (with proj-corner-hom matching the
        endpoint-of-edge-hom).
    -}
    σ-p : (k : I) → center ≡ (p-fn k , p-fn-hom k)
    σ-p k = uniq (p-fn k , p-fn-hom k)

    σ-q : (k : I) → center ≡ (q-fn k , q-fn-hom k)
    σ-q k = uniq (q-fn k , q-fn-hom k)

    σ-px : (j : I) → center ≡ (px-fn j , px-fn-hom j)
    σ-px j = uniq (px-fn j , px-fn-hom j)

    σ-py : (j : I) → center ≡ (py-fn j , py-fn-hom j)
    σ-py j = uniq (py-fn j , py-fn-hom j)

    {-
        The four "edge-spokes": 2-cells from `center-fn g` to
        the edge value. At k=0/1 (resp j=0/1) these reduce to
        the corresponding corner spokes.
    -}
    spoke-p : (k l : I) → M A B
    spoke-p k l = fst (σ-p k l) g

    spoke-q : (k l : I) → M A B
    spoke-q k l = fst (σ-q k l) g

    spoke-px : (j l : I) → M A B
    spoke-px j l = fst (σ-px j l) g

    spoke-py : (j l : I) → M A B
    spoke-py j l = fst (σ-py j l) g

  {-
      Final assembly via 4-face primHComp on the edge-spokes.
      Each side condition picks one edge-spoke at l=i1 (giving
      the boundary edge) and at l=i0 gives `center-fn g` (the
      base). Corner consistency holds because adjacent edge-
      spokes share the corresponding corner σ-path (e.g.,
      `σ-p 0 = σ-X₀ = σ-px 0` definitionally, since p-fn 0 =
      proj-X₀ = px-fn 0 with matching hom-witnesses, both
      computing as constant outM X₀).
  -}
  result :
    (R₂ : R2Type) (isBis : isBisType R₂)
    {X₀ X₁ Y₀ Y₁ : M A B}
    {px : X₀ ≡ X₁} {py : Y₀ ≡ Y₁}
    {p : X₀ ≡ Y₀} {q : X₁ ≡ Y₁}
    → R₂ px py p q → PathP (λ j → px j ≡ py j) p q
  result R₂ isBis {X₀} {X₁} {Y₀} {Y₁} {px} {py} {p} {q} r j k =
    primHComp
      (λ l → λ where
        (j = i0) → EC.spoke-p k l
        (j = i1) → EC.spoke-q k l
        (k = i0) → EC.spoke-px j l
        (k = i1) → EC.spoke-py j l)
      (EC.center-fn EC.g)
    where module EC = ExtractCenter R₂ isBis r

isHFinal→M-Coind-2D :
    {A : Type ℓ} {B : A → Type ℓ}
  → isHFinal {A = A} {B = B} (M A B , outM)
  → M-Coind-2D-Type {A = A} {B = B}
isHFinal→M-Coind-2D iFC =
  isHFinal→M-Coind-2D-Proof.result iFC


{-
   Bundling as biimplication (`_↔_`).

   We package the two directions into mtype.agda's `_↔_`
   record (logical biimplication: forward and backward maps,
   no round-trip witnesses).

   We deliberately do NOT claim a full `_≃_`. To upgrade
   biimplication to equivalence we would need either side to
   be a proposition; `isHFinal M` is provably one (see
   `isHFinal-isProp` below — kept as a documented fact),
   but `M-Coind-2D-Type` requires "2-cells in M with any
   fixed boundary are unique," which depends on M's higher
   structure (e.g. holds trivially if `isSet A`, but requires
   substantial extra cubical work otherwise).

   The biimplication is what's actually load-bearing: the two
   directions transport content between the two formulations
   of M's finality. Promoting it to an equivalence is purely
   about h-level bookkeeping, not about the content of the
   theorem.
-}

-- Kept for reference: `isHFinal M` is a proposition.
-- Not used in the biimplication below, but documents what we
-- know about the right-hand side.
isContr-isHFinal : {A : Type ℓ} {B : A → Type ℓ}
                       (F : P-Coalg A B) (C : P-Coalg A B) →
                       isProp (isContr
                         (Σ (CoalgCarrier C → CoalgCarrier F) (isCoalgHom C F)))
isContr-isHFinal _ _ = isPropIsContr

isHFinal-isProp : {A : Type ℓ} {B : A → Type ℓ}
                      {F : P-Coalg A B} → isProp (isHFinal F)
isHFinal-isProp {F = F} =
  isPropΠ (λ C → isContr-isHFinal F C)

{- Only the (⇐) direction `isHFinal→M-Coind-2D` is included;
   the (⇒) direction is not needed by the development. -}

{-
   Homotopy M-types at the carrier level.

   This is the exact dual of `HasMRules ≃ isFinal`, one h-level up.
   A *homotopy M-type* on `(X, s, p)` bundles the M-rules with `η`
   strengthened to Σ-level uniqueness (`η-Σ`): the corecursor and its
   two β-rules verbatim from `HasMRules`, plus the rule that *any*
   M-homomorphism bundle `(h, h-shape, h-pos)` equals the corecursor
   bundle `(rec, β-shape, β-pos)`.  Contractibility of the
   M-homomorphism space `MHom` is *derived* from the rules
   (`HasHMRules→homContr`), not taken as the definition; since `MHom`
   is definitionally isomorphic to the coalgebra-hom space, the rules
   are a genuine type equivalence with homotopy-finality of the
   induced coalgebra `(X, λ x → (s x, p x))`:

       HasHMRules {A = A} {B = B} X s p  ≃  isHFinal (X , λ x → s x , p x).

   Unlike the fixed-M `M-Coind-2D-↔-isHFinal`, the coalgebra `(s, p)`
   is a parameter on *both* sides, so nothing collapses to a bare
   proposition and the biimplication upgrades to a real `≃` (both sides
   are propositions).
-}

-- The M-homomorphism space: functions `C → X` with the M-rules
-- hom-witness (shape/pos), the traditional-style encoding of a coalgebra
-- homomorphism used by `HasMRules`.
MHom : {A : Type ℓ} {B : A → Type ℓ}
       (X : Type ℓ) (s : X → A) (p : (x : X) → B (s x) → X)
       (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
     → Type ℓ
MHom {B = B} X s p C sC pC =
  Σ (C → X) (λ h →
    Σ ((c : C) → s (h c) ≡ sC c) (λ hs →
      (c : C) → PathP (λ i → B (hs c i) → X) (p (h c)) (λ b → h (pC c b))))

{-
  Definition 4.15 (Homotopy M-Types)
  A homotopy M-type: the M-rules with `η` strengthened to Σ-level
   uniqueness.  `rec`, `β-shape`, and `β-pos` are verbatim the
   corresponding `HasMRules` fields; `η-Σ` replaces the function-level
   `η`, identifying any M-homomorphism bundle `(h, h-shape, h-pos)`
   with the corecursor bundle `(rec, β-shape, β-pos)` in one Σ-path.
   Contractibility of `MHom` is derived (`HasHMRules→homContr`). -}
record HasHMRules {A : Type ℓ} {B : A → Type ℓ}
                  (X : Type ℓ) (s : X → A) (p : (x : X) → B (s x) → X)
                  : Type (lsuc ℓ) where
  field
    rec : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
        → C → X

    β-shape : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C) (c : C)
            → s (rec C sC pC c) ≡ sC c

    β-pos   : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C) (c : C)
            → PathP (λ i → B (β-shape C sC pC c i) → X)
                    (p (rec C sC pC c))
                    (λ b → rec C sC pC (pC c b))

    η-Σ : (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
          (m : MHom {A = A} {B = B} X s p C sC pC)
        → m ≡ ( rec C sC pC
              , (λ c → β-shape C sC pC c)
              , (λ c → β-pos C sC pC c) )

module _ {A : Type ℓ} {B : A → Type ℓ}
         (X : Type ℓ) (s : X → A) (p : (x : X) → B (s x) → X) where

  -- `MHom ⇄ CoalgHom`, a definitional iso (both round-trips `refl`): the
  -- shape/pos witness is just the coalgebra-hom path read componentwise
  -- (up to interval reversal).
  MHom→CoalgHom :
      (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
    → MHom {A = A} {B = B} X s p C sC pC
    → CoalgHom {A = A} {B = B} (C , λ c → sC c , pC c) (X , λ x → s x , p x)
  MHom→CoalgHom C sC pC (h , hs , hp) =
    h , (λ i c → hs c (~ i) , λ b → hp c (~ i) b)

  CoalgHom→MHom :
      (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
    → CoalgHom {A = A} {B = B} (C , λ c → sC c , pC c) (X , λ x → s x , p x)
    → MHom {A = A} {B = B} X s p C sC pC
  CoalgHom→MHom C sC pC (h , k) =
    h , (λ c i → fst (k (~ i) c)) , (λ c i → snd (k (~ i) c))

  MHom→CoalgHom→MHom :
      (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
      (m : MHom {A = A} {B = B} X s p C sC pC)
    → CoalgHom→MHom C sC pC (MHom→CoalgHom C sC pC m) ≡ m
  MHom→CoalgHom→MHom C sC pC m = refl

  CoalgHom→MHom→CoalgHom :
      (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
      (k : CoalgHom {A = A} {B = B} (C , λ c → sC c , pC c) (X , λ x → s x , p x))
    → MHom→CoalgHom C sC pC (CoalgHom→MHom C sC pC k) ≡ k
  CoalgHom→MHom→CoalgHom C sC pC k = refl

  -- The corecursor bundle `(rec, β-shape, β-pos)` as a point of `MHom`.
  recMHom : (hm : HasHMRules {A = A} {B = B} X s p)
            (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
          → MHom {A = A} {B = B} X s p C sC pC
  recMHom hm C sC pC =
      HasHMRules.rec hm C sC pC
    , (λ c → HasHMRules.β-shape hm C sC pC c)
    , (λ c → HasHMRules.β-pos hm C sC pC c)

  {- `η-Σ` says every point of `MHom` equals the corecursor bundle:
     `MHom` is contractible with that bundle as centre.  This is the
     derivation of the contractibility packaging from the rules. -}
  HasHMRules→homContr :
      HasHMRules {A = A} {B = B} X s p
    → (C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
    → isContr (MHom {A = A} {B = B} X s p C sC pC)
  HasHMRules→homContr hm C sC pC =
    recMHom hm C sC pC , (λ m → sym (HasHMRules.η-Σ hm C sC pC m))

  {- Conversely, the rules are read off a contraction of `MHom`:
     the centre supplies `rec` and the β-rules (by Σ-η they *are* its
     components), and the contraction, reversed, is `η-Σ`. -}
  homContr→HasHMRules :
      ((C : Type ℓ) (sC : C → A) (pC : (c : C) → B (sC c) → C)
        → isContr (MHom {A = A} {B = B} X s p C sC pC))
    → HasHMRules {A = A} {B = B} X s p
  homContr→HasHMRules hc = record
    { rec     = λ C sC pC → fst (fst (hc C sC pC))
    ; β-shape = λ C sC pC → fst (snd (fst (hc C sC pC)))
    ; β-pos   = λ C sC pC → snd (snd (fst (hc C sC pC)))
    ; η-Σ     = λ C sC pC m → sym (snd (hc C sC pC) m)
    }

  {- Both round-trips of the packaging are definitional (Σ-η for the
     centre components, `sym (sym _) = _` for the contraction), so
     `HasHMRules` is a definitional retract of the contractibility
     formulation, which is a proposition. -}
  isProp-HasHMRules : isProp (HasHMRules {A = A} {B = B} X s p)
  isProp-HasHMRules x y =
    cong homContr→HasHMRules
         (isPropΠ (λ C → isPropΠ (λ sC → isPropΠ (λ pC → isPropIsContr)))
                  (HasHMRules→homContr x) (HasHMRules→homContr y))

  HasHMRules→isHFinal :
      HasHMRules {A = A} {B = B} X s p → isHFinal {A = A} {B = B} (X , λ x → s x , p x)
  HasHMRules→isHFinal hm (C , γC) =
    retract-isContr
      (MHom→CoalgHom C (λ c → fst (γC c)) (λ c → snd (γC c)))
      (CoalgHom→MHom C (λ c → fst (γC c)) (λ c → snd (γC c)))
      (CoalgHom→MHom→CoalgHom C (λ c → fst (γC c)) (λ c → snd (γC c)))
      (HasHMRules→homContr hm C (λ c → fst (γC c)) (λ c → snd (γC c)))

  isHFinal→HasHMRules :
      isHFinal {A = A} {B = B} (X , λ x → s x , p x) → HasHMRules {A = A} {B = B} X s p
  isHFinal→HasHMRules iFC = homContr→HasHMRules (λ C sC pC →
    retract-isContr
      (CoalgHom→MHom C sC pC)
      (MHom→CoalgHom C sC pC)
      (MHom→CoalgHom→MHom C sC pC)
      (iFC (C , λ c → sC c , pC c)))

  -- Theorem 4.21 ((Homotopy) M-Types are (Homotopy) Final Coalgebras), part (2)
  -- The genuine type equivalence, dual to `HasMRules-≃-isFinal` one
  -- h-level up.  Both sides are propositions, so the biimplication is an
  -- equivalence.
  HasHMRules-≃-isHFinal :
      HasHMRules {A = A} {B = B} X s p ≃ isHFinal {A = A} {B = B} (X , λ x → s x , p x)
  HasHMRules-≃-isHFinal = record
    { fwd      = HasHMRules→isHFinal
    ; bwd-L    = isHFinal→HasHMRules
    ; leftInv  = λ hm → isProp-HasHMRules
                          (isHFinal→HasHMRules (HasHMRules→isHFinal hm)) hm
    ; bwd-R    = isHFinal→HasHMRules
    ; rightInv = λ f → isHFinal-isProp {A = A} {B = B} {F = X , λ x → s x , p x}
                          (HasHMRules→isHFinal (isHFinal→HasHMRules f)) f
    }
