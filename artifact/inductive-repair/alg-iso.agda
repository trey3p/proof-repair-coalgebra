{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import palg

{-
    Toward `WTypeConfig A B C D ≃ Σ supC supD (AlgEquiv (C,supC) (D,supD)
                                                 × isInitAlg (C,supC))`.

    This file builds the supporting HoTT/algebra infrastructure
    bottom-up:

      • basic propositional-truncation lemmas (`isProp`, a prop
        is a set, `iscontr` is a prop, `isInitAlg` is a prop);
      • `retract-iscontr` (a retract of a contractible type is
        contractible);
      • the `palg` algebra-category laws and the initiality
        transfer across an algebra equivalence;
      • the core equivalence and its assembly.
-}
module inductive-repair.alg-iso where

  {-
     Propositional-truncation lemmas
  -}

  isProp : ∀ {ℓ} → Type ℓ → Type ℓ
  isProp A = (x y : A) → x ≡ y

  isContr→isProp : ∀ {ℓ} {A : Type ℓ} → iscontr A → isProp A
  isContr→isProp (c , p) x y = p x • ! (p y)

  Π-isProp : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} →
             ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
  Π-isProp pf f g = ext (λ a → pf a (f a) (g a))

  {-
      A proposition is a set: any two parallel paths agree.
      Standard "the homotopy `h x` is natural, so every path is
      forced" argument.
  -}
  isProp→isSet : ∀ {ℓ} {A : Type ℓ} → isProp A →
                 (x y : A) (p q : x ≡ y) → p ≡ q
  isProp→isSet {A = A} h x y p q = aux p • ! (aux q)
    where
      g : (z : A) → x ≡ z
      g z = h x z
      nat : {z w : A} (r : z ≡ w) → g z • r ≡ g w
      nat refl = •unitr
      aux : {z w : A} (r : z ≡ w) → r ≡ ! (g z) • g w
      aux {z} r =
          ! (! •assoc • ap (_• r) •invl • •unitl)
        • ap (! (g z) •_) (nat r)

  {-
      `iscontr A` is itself a proposition.
  -}
  isProp-iscontr : ∀ {ℓ} {A : Type ℓ} → isProp (iscontr A)
  isProp-iscontr cc1@(c1 , p1) (c2 , p2) =
      Σ-≡-intro (p2 c1)
                (Π-isProp (λ x → isProp→isSet (isContr→isProp cc1) x c2) _ p2)

  {-
      Being an initial algebra is a proposition: it is a Π of
      `iscontr`s.
  -}
  isProp-isInitAlg : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂}
                     (X : P-Alg {ℓ₃ = ℓ₃} A B) → isProp (isInitAlg X)
  isProp-isInitAlg X = Π-isProp (λ Y → isProp-iscontr)

  {-
      Level-polymorphic Σ path introduction and `isProp` of a Σ
      whose base and fibres are all propositions.
  -}
  Σ-≡-intro' : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
               {a a' : A} {b : B a} {b' : B a'}
               (p : a ≡ a') → tpt B p b ≡ b' → (a , b) ≡ (a' , b')
  Σ-≡-intro' refl refl = refl

  Σ-isProp : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} →
             isProp A → ((a : A) → isProp (B a)) → isProp (Σ A B)
  Σ-isProp pa pb (a , b) (a' , b') =
      Σ-≡-intro' (pa a a') (pb a' (tpt _ (pa a a') b) b')

  isContr→isSet : ∀ {ℓ} {A : Type ℓ} → iscontr A →
                  (x y : A) → isProp (x ≡ y)
  isContr→isSet ct x y = isProp→isSet (isContr→isProp ct) x y


  {-
     Retract of a contractible type
  -}

  {-
      If `B` is a retract of `A` (maps `s : B → A`, `r : A → B`
      with `r ∘ s ∼ id`) and `A` is contractible, then so is `B`.
  -}
  retract-iscontr : ∀ {ℓ} {A B : Type ℓ} (r : A → B) (s : B → A) →
                    ((b : B) → r (s b) ≡ b) → iscontr A → iscontr B
  retract-iscontr r s rs (c , p) =
      r c , (λ b → ! (rs b) • ap r (p (s b)))

  ap-id : ∀ {ℓ} {X : Type ℓ} {x y : X} (p : x ≡ y) → ap (λ z → z) p ≡ p
  ap-id refl = refl

  -- `happly` of a *post*-composition: `happly (ap (m ∘_) e) z` is just
  -- `ap m (happly e z)` (dual of `common.happly-precomp`). Used below to
  -- evaluate the homomorphism-square of `AlgHom-∘` pointwise.
  happly-post : ∀ {ℓ} {U V W : Type ℓ} (m : V → W) {k₁ k₂ : U → V}
                (e : k₁ ≡ k₂) (z : U) →
                happly (ap (λ k → m ∘ k) e) z ≡ ap m (happly e z)
  happly-post m refl z = refl


  {-
     `palg` algebra-category laws

     The carriers are all at one level `l` (which is all the
     downstream `≃` needs).
  -}

  module _ {l : Level} {A : Type l} {B : A → Type l} where

    {-
        Left unit law for `AlgHom-∘`. Function part is `refl`
        (`κ ∘ id = κ`); the `isAlgHom` proof reduces because
        `P-map id` is the identity (`P-id`) and `P-∘ κ id` is
        `ext refl`.
    -}
    ∘-id-l : {X Y : P-Alg {ℓ₃ = l} A B} (k : AlgHom X Y) →
             AlgHom-∘ X X Y (id-hom X) k ≡ k
    ∘-id-l {X = (CX , fX)} {Y = (CY , fY)} (κ , κ-hom) =
        Σ-≡-intro refl
          ( •unitl
          • ap (_• ap (fY ∘_) (P-∘ κ (λ x → x))) (ap-id κ-hom)
          • ap (κ-hom •_) (ap (ap (fY ∘_)) (! funext-refl))
          • •unitr )

    {-
       Initiality transfer along an algebra equivalence — *without
       univalence*.

       For any algebra `Y`, pre-composing with the equivalence's
       homomorphisms makes `AlgHom (D,supD) Y` a *retract* of
       `AlgHom (C,supC) Y`: send `k : AlgHom (C,supC) Y` to `k ∘ hh`
       and back via `m ↦ m ∘ fwd`; the round-trip is the identity
       because `fwd ∘ hh ≡ id` (the right-inverse equation of the
       algebra equivalence) — this is `AlgHom-∘-assoc` followed by
       that equation and the left-unit law `∘-id-l`. Since `AlgHom
       (C,supC) Y` is contractible by initiality of `C`, so is its
       retract `AlgHom (D,supD) Y` (`retract-iscontr`), giving
       initiality of `D`. This is the exact dual of the coinductive
       `finalTransfer`/`hFinalTransfer`.

       The one ingredient not yet available is associativity of
       `AlgHom-∘`. Its carrier part is `refl` (function composition is
       definitionally associative), so the whole lemma reduces to a
       pointwise comparison of the two homomorphism-squares, which is
       just re-association of `•` (no h-level / set assumption needed).
    -}

    -- Pointwise value of the homomorphism-square of `AlgHom-∘`. The
    -- `P-∘` whisker vanishes pointwise (`P-∘ = ext (λ _ → refl)`),
    -- leaving the two naturality contributions.
    sq-pt : (X Y Z : P-Alg {ℓ₃ = l} A B)
            (p : AlgHom X Y) (q : AlgHom Y Z) (z : P A B (Carrier X)) →
            happly (snd (AlgHom-∘ X Y Z p q)) z
              ≡ ap (fst q) (happly (snd p) z) • happly (snd q) (P-map (fst p) z)
    sq-pt (CX , σX) (CY , σY) (CZ , σZ) (p , p̂) (q , q̂) z =
        happly-• (ap (q ∘_) p̂) (ap (_∘ P-map p) q̂ • ap (σZ ∘_) (P-∘ q p)) z
      • ap2 (λ u v → u • v) (happly-post q p̂ z) restEq
      where
        restEq : happly (ap (_∘ P-map p) q̂ • ap (σZ ∘_) (P-∘ q p)) z
                   ≡ happly q̂ (P-map p z)
        restEq =
            happly-• (ap (_∘ P-map p) q̂) (ap (σZ ∘_) (P-∘ q p)) z
          • ap (happly (ap (_∘ P-map p) q̂) z •_) whisker-refl
          • •unitr
          • happly-precomp {l} {l} q̂ (P-map p) z
          where
            whisker-refl : happly (ap (σZ ∘_) (P-∘ q p)) z ≡ refl
            whisker-refl =
                happly-post σZ (P-∘ q p) z
              • ap (ap σZ)
                   (happlyExt {f = P-map q ∘ P-map p} {g = P-map (q ∘ p)}
                              (λ _ → refl) z)

    -- Associativity of `AlgHom-∘`. The carrier path is `refl`; the
    -- square equality is checked pointwise via `sq-pt`, where it is a
    -- bare re-association of `•`.
    AlgHom-∘-assoc :
      (X Y Z W : P-Alg {ℓ₃ = l} A B)
      (p : AlgHom X Y) (q : AlgHom Y Z) (t : AlgHom Z W) →
      AlgHom-∘ X Y W p (AlgHom-∘ Y Z W q t)
        ≡ AlgHom-∘ X Z W (AlgHom-∘ X Y Z p q) t
    AlgHom-∘-assoc (CX , σX) (CY , σY) (CZ , σZ) (CW , σW)
                   (p , p̂) (q , q̂) (t , t̂) =
        Σ-≡-intro refl (happly-inj (ext ptwise))
      where
        ptwise : (z : P A B CX) →
          happly (snd (AlgHom-∘ (CX , σX) (CY , σY) (CW , σW) (p , p̂)
                         (AlgHom-∘ (CY , σY) (CZ , σZ) (CW , σW) (q , q̂) (t , t̂)))) z
            ≡ happly (snd (AlgHom-∘ (CX , σX) (CZ , σZ) (CW , σW)
                         (AlgHom-∘ (CX , σX) (CY , σY) (CZ , σZ) (p , p̂) (q , q̂)) (t , t̂))) z
        ptwise z =
            sq-pt (CX , σX) (CY , σY) (CW , σW) (p , p̂)
                  (AlgHom-∘ (CY , σY) (CZ , σZ) (CW , σW) (q , q̂) (t , t̂)) z
          • ap (ap (t ∘ q) a' •_)
               (sq-pt (CY , σY) (CZ , σZ) (CW , σW) (q , q̂) (t , t̂) (P-map p z))
          • ! fwd-eq
          • ! ( sq-pt (CX , σX) (CZ , σZ) (CW , σW)
                      (AlgHom-∘ (CX , σX) (CY , σY) (CZ , σZ) (p , p̂) (q , q̂)) (t , t̂) z
              • ap (_• c') (ap (ap t) (sq-pt (CX , σX) (CY , σY) (CZ , σZ) (p , p̂) (q , q̂) z)) )
          where
            a' = happly p̂ z
            b' = happly q̂ (P-map p z)
            c' = happly t̂ (P-map q (P-map p z))
            fwd-eq : ap t (ap q a' • b') • c'
                       ≡ ap (t ∘ q) a' • (ap t b' • c')
            fwd-eq =
                ap (_• c')
                   (ap-• t (ap q a') b' • ap (_• ap t b') (! (ap-∘ {f = t} {g = q} a')))
              • •assoc

    -- Sealed: `isInitAlg` is a proposition and no consumer computes
    -- with the transferred witness, while its body (through
    -- `AlgHom-∘-assoc`) is large enough to make eta-comparisons of
    -- records containing it expensive (cf. the seals in
    -- `palg-config`).
    abstract
     initTransfer : {C D : Type l} {supC : P A B C → C} {supD : P A B D → D} →
                    AlgEquiv (C , supC) (D , supD) → isInitAlg (C , supC) →
                    isInitAlg (D , supD)
     initTransfer {C} {D} {supC} {supD}
                  (fwd , (_ , (hh , h-eq))) isInitC Y =
         retract-iscontr r s rs (isInitC Y)
      where
        r : AlgHom (C , supC) Y → AlgHom (D , supD) Y
        r k = AlgHom-∘ (D , supD) (C , supC) Y hh k
        s : AlgHom (D , supD) Y → AlgHom (C , supC) Y
        s m = AlgHom-∘ (C , supC) (D , supD) Y fwd m
        rs : (m : AlgHom (D , supD) Y) → r (s m) ≡ m
        rs m =
            AlgHom-∘-assoc (D , supD) (C , supC) (D , supD) Y hh fwd m
          • ap (λ z → AlgHom-∘ (D , supD) (D , supD) Y z m) h-eq
          • ∘-id-l {X = D , supD} {Y = Y} m

    {-
       `AlgEquiv X Y` is a proposition when the source `X` is
       initial.

       The underlying `AlgHom X Y` is contractible (initiality of
       `X`), and from any equivalence the target `Y` is initial
       too (`initTransfer`), making every component of
       `isAlgEquiv` either a contractible base or a path in a
       contractible hom-set — all propositions.
    -}
    isProp-AlgEquiv : {X Y : P-Alg {ℓ₃ = l} A B} →
                      isInitAlg X → isProp (AlgEquiv X Y)
    isProp-AlgEquiv {X} {Y} isInitX e1 e2 =
        Σ-isProp homXY-isProp isAlgEquiv-isProp e1 e2
      where
        isInitY : isInitAlg Y
        isInitY = initTransfer e1 isInitX
        homXY-isProp : isProp (AlgHom X Y)
        homXY-isProp = isContr→isProp (isInitX Y)
        homYX-isProp : isProp (AlgHom Y X)
        homYX-isProp = isContr→isProp (isInitY X)
        isAlgEquiv-isProp : (f : AlgHom X Y) → isProp (isAlgEquiv X Y f)
        isAlgEquiv-isProp f =
          Σ-isProp
            (Σ-isProp homYX-isProp
                      (λ g → isContr→isSet (isInitX X) _ (id-hom X)))
            (λ _ → Σ-isProp homYX-isProp
                      (λ h → isContr→isSet (isInitY Y) _ (id-hom Y)))

    {-
       Uniqueness of repair.

       Two initial algebras for the same polynomial are related by
       an algebra equivalence (the unique homomorphisms each way,
       whose round-trips are endomorphisms of an initial algebra
       and hence the identities), and by `isProp-AlgEquiv` that
       equivalence is the *only* one: `AlgEquiv X Y` is
       contractible. An algebra configuration therefore determines
       exactly one repair.
    -}
    algEquivFromInits : {X Y : P-Alg {ℓ₃ = l} A B} →
                        isInitAlg X → isInitAlg Y → AlgEquiv X Y
    algEquivFromInits {X} {Y} isInitX isInitY =
        fwd , ((bwd , left) , (bwd , right))
      where
        fwd : AlgHom X Y
        fwd = isInitX Y .fst
        bwd : AlgHom Y X
        bwd = isInitY X .fst
        left : AlgHom-∘ X Y X fwd bwd ≡ id-hom X
        left = homEqInitId X isInitX (AlgHom-∘ X Y X fwd bwd)
        right : AlgHom-∘ Y X Y bwd fwd ≡ id-hom Y
        right = homEqInitId Y isInitY (AlgHom-∘ Y X Y bwd fwd)

    -- Theorem 3.11 (uniqueness): the algebra equivalence between two
    -- initial algebras is unique, i.e. `AlgEquiv X Y` is contractible.
    isContr-AlgEquiv : {X Y : P-Alg {ℓ₃ = l} A B} →
                       isInitAlg X → isInitAlg Y → iscontr (AlgEquiv X Y)
    isContr-AlgEquiv isInitX isInitY =
        algEquivFromInits isInitX isInitY ,
        λ e → isProp-AlgEquiv isInitX e (algEquivFromInits isInitX isInitY)
