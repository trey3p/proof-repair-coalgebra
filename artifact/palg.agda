{-# OPTIONS --without-K  --cubical-compatible #-}

open import common

{-
    Algebras for a polynomial endofunctor, following Awodey,
    Gambino, and Sojakova (JACM 2017): the functor `P`, P-algebras
    and their homomorphisms, and homotopy-initial algebras.
-}
module palg where

    {-
        Definition 3.1 (Polynomial Endofunctor)
        P A B X ≔ Σ a:A. (B a → X): a shape together with a
        (B a)-indexed family of children in X.
    -}
    P : ∀ {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (B : A → Type ℓ₂) (X : Type ℓ₃)
      → Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
    P A B X = Σ A (λ a → B a → X)

    -- Functorial action of P on a map C → D.
    P-map : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : A → Type ℓ₂}
            {C : Type ℓ₃} {D : Type ℓ₄}
          → (C → D) → P A B C → P A B D
    P-map f (a , u) = (a , f ∘ u)

    -- P preserves composition (up to funext on the second component).
    P-∘ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
                 {A : Type ℓ₁} {B : A → Type ℓ₂}
                 {X : Type ℓ₃} {Y : Type ℓ₄} {Z : Type ℓ₅}
               → (g : Y → Z) (f : X → Y)
               → P-map {A = A} {B = B} g ∘ P-map f
                 ≡ P-map {A = A} {B = B} (g ∘ f)
    P-∘ g f = ext (λ _ → refl)

    -- P preserves identities.
    P-id : ∀ {ℓ₁ ℓ₂ ℓ₃}
               {A : Type ℓ₁} {B : A → Type ℓ₂} {X : Type ℓ₃}
             → P-map {A = A} {B = B} {C = X} {D = X} (λ x → x) ≡ λ p → p
    P-id = ext (λ _ → refl)

    {-
        Action of P on pointwise equalities: a homotopy f ∼ g lifts
        to P-map f ∼ P-map g — `refl` on the shape, pointwise α on
        children. Single universe level because `Σ-≡-intro` is
        level-monomorphic in `common`.
    -}
    P-resp : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {C D : Type ℓ}
            (f g : C → D)
          → (∀ x → f x ≡ g x)
          → ∀ p → P-map {A = A} {B = B} f p ≡ P-map g p
    P-resp f g α (a , u) = Σ-≡-intro refl (ext (λ b → α (u b)))

    {-
        `P-resp` agrees with the canonical proof `ap (P-map _) (ext α)`,
        for reasoning about `P-map` at the level of function equality.
    -}
    P-resp-is-ap-P-map : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ}
                        {C D : Type ℓ} {f g : C → D}
                        (α : ∀ x → f x ≡ g x) (p : P A B C)
                      → P-resp f g α p ≡ ap (λ h → P-map h p) (ext α)
    P-resp-is-ap-P-map α (a , u) =
        ap (Σ-≡-intro refl) (! (precomp-ext u α))
      • Σ-≡-intro-ap (ext α)

    {-
        Definition 3.2 (P-algebra)
        A P-algebra: a carrier C with a structure map P A B C → C.
    -}
    P-Alg : ∀ {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (B : A → Type ℓ₂)
          → Type (ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃)
    P-Alg {ℓ₃ = ℓ₃} A B = Σ (Type ℓ₃) (λ C → P A B C → C)

    Carrier : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂}
            → P-Alg {ℓ₃ = ℓ₃} A B → Type ℓ₃
    Carrier = fst

    SMap : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂}
         → (X : P-Alg {ℓ₃ = ℓ₃} A B) → P A B (Carrier X) → Carrier X
    SMap = snd

    -- Definition 3.4 (Algebra Homomorphism)
    -- A carrier map is a homomorphism when it commutes with the
    -- structure maps.
    isAlgHom : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
               {A : Type ℓ₁} {B : A → Type ℓ₂}
             → (X : P-Alg {ℓ₃ = ℓ₃} A B) (Y : P-Alg {ℓ₃ = ℓ₄} A B)
             → (Carrier X → Carrier Y) → Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
    isAlgHom (C , f) (D , g) h = h ∘ f ≡ g ∘ P-map h

    {-
        Definition 3.4 (Algebra Homomorphism)
        Algebra homomorphism: a carrier map paired with the proof
        that it intertwines the structure maps.
    -}
    AlgHom : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
             {A : Type ℓ₁} {B : A → Type ℓ₂}
           → P-Alg {ℓ₃ = ℓ₃} A B → P-Alg {ℓ₃ = ℓ₄} A B
           → Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
    AlgHom X Y = Σ (Carrier X → Carrier Y) (isAlgHom X Y)

    -- Composition of algebra homomorphisms.
    AlgHom-∘ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
                 {A : Type ℓ₁} {B : A → Type ℓ₂}
                 (X : P-Alg {ℓ₃ = ℓ₃} A B)
                 (Y : P-Alg {ℓ₃ = ℓ₄} A B)
                 (Z : P-Alg {ℓ₃ = ℓ₅} A B)
               → AlgHom X Y → AlgHom Y Z → AlgHom X Z
    AlgHom-∘ (C , f) (D , g) (E , h) (s , s-hom) (r , r-hom) =
        r ∘ s , square
      where
        -- (r ∘ s) ∘ f ≡ r ∘ (g ∘ P-map s) ≡ (h ∘ P-map r) ∘ P-map s
        --             ≡ h ∘ P-map (r ∘ s)
        square : r ∘ (s ∘ f) ≡ h ∘ P-map (r ∘ s)
        square = ap (r ∘_) s-hom
               • ap (_∘ P-map s) r-hom
               • ap (h ∘_) (P-∘ r s)

    {-  Definition 3.7 (Homotopy-initial Algebra)
        X is homotopy-initial when, for every algebra Y, the type of
        homomorphisms X → Y is contractible.
    -}
    isInitAlg : ∀ {ℓ₁ ℓ₂ ℓ₃}
                {A : Type ℓ₁} {B : A → Type ℓ₂}
              → P-Alg {ℓ₃ = ℓ₃} A B → Type (ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃)
    isInitAlg {ℓ₃ = ℓ₃} {A = A} {B = B} X =
        (Y : P-Alg {ℓ₃ = ℓ₃} A B) → iscontr (AlgHom X Y)

    -- Definition 3.7
    -- An initial algebra: an algebra together with proof of initiality.
    InitAlg : ∀ {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (B : A → Type ℓ₂)
            → Type (ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃)
    InitAlg {ℓ₃ = ℓ₃} A B = Σ (P-Alg {ℓ₃ = ℓ₃} A B) isInitAlg

    {-
        Definition 3.13 (Algebra Configuration): `InitAlgOn`
        Initial algebra structure on a fixed carrier C, for when the
        carrier comes from elsewhere and we equip it with its sup map
        and initiality.
    -}
    record InitAlgOn {ℓ₁ ℓ₂ ℓ₃ : Level} (A : Type ℓ₁) (B : A → Type ℓ₂)
                     (C : Type ℓ₃) : Type (ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃) where
      field
        sup    : P A B C → C
        isInit : isInitAlg (C , sup)

    -- Identity homomorphism.
    id-hom : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂}
             (X : P-Alg {ℓ₃ = ℓ₃} A B) → AlgHom X X
    id-hom X = (λ x → x) , refl

    {-
        Definition 3.6 (Algebra Equivalence)
        A homomorphism is an algebra equivalence when it has both a
        left and a right inverse (bi-invertibility).
    -}
    isAlgEquiv : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                 {A : Type ℓ₁} {B : A → Type ℓ₂}
                 (X : P-Alg {ℓ₃ = ℓ₃} A B) (Y : P-Alg {ℓ₃ = ℓ₄} A B)
               → AlgHom X Y → Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
    isAlgEquiv X Y f =
        Σ (AlgHom Y X) (λ g → AlgHom-∘ X Y X f g ≡ id-hom X)
      × Σ (AlgHom Y X) (λ h → AlgHom-∘ Y X Y h f ≡ id-hom Y)

    -- Definition 3.6 (Algebra Equivalence)
    AlgEquiv : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
               {A : Type ℓ₁} {B : A → Type ℓ₂}
             → P-Alg {ℓ₃ = ℓ₃} A B → P-Alg {ℓ₃ = ℓ₄} A B
             → Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
    AlgEquiv X Y = Σ (AlgHom X Y) (isAlgEquiv X Y)

    {-
        Any endomorphism of an initial algebra equals the identity:
        AlgHom X X is contractible by initiality (with Y ≔ X).
    -}
    homEqInitId : ∀ {ℓ₁ ℓ₂ ℓ₃}
                  {A : Type ℓ₁} {B : A → Type ℓ₂}
                  (X : P-Alg {ℓ₃ = ℓ₃} A B)
                → isInitAlg X → (f : AlgHom X X) → f ≡ id-hom X
    homEqInitId X isInit f =
        isInit X .snd f • ! (isInit X .snd (id-hom X))
