{-# OPTIONS --cubical --guardedness --safe #-}


{- 

  Coinductive dual of `inductive-repair.config-alg-equiv`
  for Final and HFinal
-} 
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import Agda.Primitive.Cubical using (I; i0; i1; primHComp)
  renaming (primIMin to _∧_; primIMax to _∨_;
            primINeg to ~_; primTransp to transp)
open import coinductive-repair.coalg hiding (corec)
open import coinductive-repair.config
-- Theorem 4.24: `mtypeCoConfig↔` (final tier) and `hcoConfigEqvˢ`
-- (homotopy-final tier) below.
module coinductive-repair.coconfig-coalg-equiv {ℓ : Level} where

    open CoSignature
    open _≃_

    {-
      Definition 4.22 (M-type Configuration)
       The M-type signature and the Outputs ↔ P A B translation.

       Dual of `WTypeSignature A B` (Op = ⊤, arity = the single
       destructor with one Nonrec head `a : A` and one Rec child
       `B a → X`).  `DestrAlgebra (MTypeSignature A B) X` is then iso to
       `X → P A B X`, with the round-trips definitional by record η (the
       only difference is a trailing `⊤`).
    -}

    MTypeArity : (A : Type ℓ) (B : A → Type ℓ) → ⊤ {ℓ} → DestrArity {ℓ}
    MTypeArity A B _ = Nonrec A (λ a → Rec (B a) Done)

    -- Definition 4.22 (M-type Configuration)
    MTypeSignature : (A : Type ℓ) (B : A → Type ℓ) → CoSignature {ℓ}
    MTypeSignature A B .Op    = ⊤
    MTypeSignature A B .arity = MTypeArity A B

    -- Definition 4.22 (M-type Configuration)
    MTypeCoindCoalg : (A : Type ℓ) (B : A → Type ℓ) (C : Type ℓ) → Type (lsuc ℓ)
    MTypeCoindCoalg A B C = CoindCoalg (MTypeSignature A B) C

    -- Definition 4.22 (M-type Configuration)
    MTypeCoConfig : (A : Type ℓ) (B : A → Type ℓ) (C D : Type ℓ) → Type (lsuc ℓ)
    MTypeCoConfig A B C D = CoConfig (MTypeSignature A B) C D

    module _ {A : Type ℓ} {B : A → Type ℓ} where

      -- The single destructor's output type, and its iso to `P A B X`.
      out→P : {X : Type ℓ} → Outputs (MTypeArity A B tt) X → P A B X
      out→P (a , (r , tt)) = a , r

      P→out : {X : Type ℓ} → P A B X → Outputs (MTypeArity A B tt) X
      P→out (a , r) = a , (r , tt)

      -- Round-trips are definitional (record η).  Kept as named refls so
      -- downstream code can cite them.
      out→P→out : {X : Type ℓ} (o : Outputs (MTypeArity A B tt) X)
                → P→out (out→P o) ≡ o
      out→P→out o = refl

      P→out→P : {X : Type ℓ} (p : P A B X) → out→P (P→out p) ≡ p
      P→out→P p = refl

      -- `mapOutputs` on the M-type arity is `P-mor` transported across
      -- the iso — definitionally.
      mapOutputs-out→P : {X Y : Type ℓ} (f : X → Y)
                         (o : Outputs (MTypeArity A B tt) X)
                       → out→P (mapOutputs (MTypeArity A B tt) f o)
                           ≡ P-mor f (out→P o)
      mapOutputs-out→P f (a , (r , tt)) = refl

    {-
       Polynomial coalgebra-isomorphism vocabulary.

       `CoalgHom-∘` / `id-coalgHom` complete the (weak) category of
       P-coalgebras started in `coalg.agda` (which only had the
       `isCoalgHom` witnesses and `∘-isCoalgHom`).

       At the plain final tier `isFinal` only pins coalg-hom functions, so
       the matching notion of isomorphism is an underlying function
       equivalence (`_≃_`) whose forward and backward maps are both
       coalgebra homomorphisms.  (The strong tier upgrades to the full
       Σ-level `AlgEquiv`-dual below.)
    -}

    module _ {A : Type ℓ} {B : A → Type ℓ} where

      id-coalgHom : (C : P-Coalg A B) → CoalgHom C C
      id-coalgHom C = (λ x → x) , refl

      CoalgHom-∘ : (C₁ C₂ C₃ : P-Coalg A B)
                 → CoalgHom C₁ C₂ → CoalgHom C₂ C₃ → CoalgHom C₁ C₃
      CoalgHom-∘ C₁ C₂ C₃ (f , f-h) (g , g-h) =
          (λ x → g (f x))
        , ∘-isCoalgHom {C₁ = C₁} {C₂ = C₂} {C₃ = C₃} {f = f} {g = g} f-h g-h

      -- Section 4.4 (`CoalgEquiv`, used in Theorem 4.24 (1))
      -- Function-level coalgebra isomorphism between `(C, xcC)` and `(D, xcD)`:
      -- a carrier equivalence whose two maps are both coalg-homs.
      CoalgEquiv : (X Y : P-Coalg A B) → Type ℓ
      CoalgEquiv X Y =
        Σ (CoalgCarrier X ≃ CoalgCarrier Y) (λ e →
            isCoalgHom X Y (fwd e) × isCoalgHom Y X (bwd-L e))

    {-
      Definition 4.12 ((Homotopy) Coalgebra Configuration): `FinalCoalgOn`
      and `CoalgConfig` below. `FinalCoalgOn` is also the carrier-level
      bridge of Theorem 4.24:

           MTypeCoindCoalg A B X  ≃  FinalCoalgOn A B X

       (dual of `inductive-repair.bridge`'s `WTypeIndAlg ≃ InitAlgOn`),
       where `FinalCoalgOn A B X = Σ xc (isFinal (X , xc))`.  Because
       the M-type signature is just a `⊤`-wrapper around `P A B`, the
       `destr`/`corec` legs round-trip by record η, and the
       `corec-β`/`corec-η` proof legs collapse the same way — so no
       Sojakova `bridgeη-beta` 2-cell is needed at this tier.
    -}

    FinalCoalgOn : (A : Type ℓ) (B : A → Type ℓ) (X : Type ℓ) → Type (lsuc ℓ)
    FinalCoalgOn A B X = Σ (X → P A B X) (λ xc → isFinal (X , xc))

    -- Definition 4.12 ((Homotopy) Coalgebra Configuration)
    CoalgConfig : (A : Type ℓ) (B : A → Type ℓ) (C D : Type ℓ) → Type (lsuc ℓ)
    CoalgConfig A B C D = FinalCoalgOn A B C × FinalCoalgOn A B D

    module _ {A : Type ℓ} {B : A → Type ℓ} {X : Type ℓ} where

      -- Forward: read the coalgebra off `destr`, package corec/β/η as
      -- finality.
      coalgBridgeFwd : MTypeCoindCoalg A B X → FinalCoalgOn A B X
      coalgBridgeFwd ind = xc , wf
        where
          open CoindCoalg ind
          xc : X → P A B X
          xc x = out→P (destr tt x)

          wf : isFinal (X , xc)
          wf (E , ec) = (center , center-hom) , uniq
            where
              destrE : DestrAlgebra (MTypeSignature A B) E
              destrE op e = P→out (ec e)

              center : E → X
              center = corec destrE

              center-hom : isCoalgHom (E , ec) (X , xc) center
              center-hom = funExt (λ e →
                  sym (cong out→P (corec-β destrE tt e)
                         ∙ mapOutputs-out→P center (destrE tt e)))

              uniq : (h' : E → X) (p' : isCoalgHom (E , ec) (X , xc) h')
                   → center ≡ h'
              uniq h' p' = funExt (λ e →
                  sym (corec-η destrE h'
                        (λ op e' → cong P→out (sym (λ i → p' i e'))) e))

      -- Backward: read `destr` off the coalgebra, corec/β/η off
      -- finality's center + function-level uniqueness.
      coalgBridgeBwd : FinalCoalgOn A B X → MTypeCoindCoalg A B X
      coalgBridgeBwd (xc , wf) = record
        { destr = λ op x → P→out (xc x)
        ; corec = λ {C} destrC c →
            fst (fst (wf (C , λ c' → out→P (destrC tt c')))) c
        ; corec-β = λ {C} destrC op c →
            cong P→out
              (sym (λ i → snd (fst (wf (C , λ c' → out→P (destrC tt c')))) i c))
        ; corec-η = λ {C} destrC h h-hom c →
            sym (λ i →
              snd (wf (C , λ c' → out→P (destrC tt c'))) h
                  (funExt (λ c' → sym (cong out→P (h-hom tt c')))) i c)
        }

      {- NOTE on round-trips.  `coalgBridgeFwd`/`coalgBridgeBwd` are NOT
         mutually inverse at the plain final tier: `isFinal` stores the
         coalg-hom *witness* of its center (`center-hom`), which
         finality does not pin (it pins only the *function*).  So the
         `FinalCoalgOn → CoindCoalg → FinalCoalgOn` round-trip would have
         to identify two `isCoalgHom` witnesses for the same function —
         a 2-cell that does not exist unless `P A B X` is a set.

         This is the same obstruction the codebase already documents for
         `M-Coind-2D-↔-isHFinal` (see `mtype.agda`), and the same
         resolution: the final-tier result below is a biimplication
         `_↔_`, which needs only `coalgBridgeFwd`/`coalgBridgeBwd` as
         maps.  The strong tier (§6) upgrades to a genuine `_≃_` because
         `isHFinal` *is* a proposition. -}

    {-
      Used in Definition 4.12 (a coalgebra configuration determines a
      coalgebra isomorphism: `coalgEquivFromFinals`) and in the proof
      of Theorem 4.24.
       Coalgebra-iso ⇄ finality.

       `homEqFinalId` — a self-hom of a final coalgebra is the
       identity (function level; dual of `homEqInitId`).

       `coalgEquivFromFinals` — two final coalgebras for the same
       functor are isomorphic (the two corecursors), dual of
       `algConfigToAlgEquiv`.

       `finalTransfer` — finality transfers across a
       `CoalgEquiv`, built directly by composing hom-spaces with the iso
       (no univalence), dual of `initTransfer`.  The concrete payoff of
       "any two final coalgebras are isomorphic".
    -}

    module _ {A : Type ℓ} {B : A → Type ℓ} where

      homEqFinalId : (F : P-Coalg A B) → isFinal F
                       → (f : CoalgCarrier F → CoalgCarrier F)
                       → isCoalgHom F F f → f ≡ (λ x → x)
      homEqFinalId F wf f f-h =
          sym (snd (wf F) f f-h) ∙ snd (wf F) (λ x → x) refl

      coalgEquivFromFinals : {C D : Type ℓ}
          (xcC : C → P A B C) (xcD : D → P A B D)
        → isFinal (C , xcC) → isFinal (D , xcD)
        → CoalgEquiv (C , xcC) (D , xcD)
      coalgEquivFromFinals {C} {D} xcC xcD wfC wfD = e , (f-h , g-h)
        where
          f   = fst (fst (wfD (C , xcC)))
          f-h = snd (fst (wfD (C , xcC)))
          g   = fst (fst (wfC (D , xcD)))
          g-h = snd (fst (wfC (D , xcD)))

          gf-h : isCoalgHom (C , xcC) (C , xcC) (λ x → g (f x))
          gf-h = ∘-isCoalgHom {C₁ = C , xcC} {C₂ = D , xcD} {C₃ = C , xcC}
                              {f = f} {g = g} f-h g-h
          fg-h : isCoalgHom (D , xcD) (D , xcD) (λ y → f (g y))
          fg-h = ∘-isCoalgHom {C₁ = D , xcD} {C₂ = C , xcC} {C₃ = D , xcD}
                              {f = g} {g = f} g-h f-h

          e : C ≃ D
          e = record
            { fwd      = f
            ; bwd-L    = g
            ; leftInv  = λ c i →
                homEqFinalId (C , xcC) wfC (λ x → g (f x)) gf-h i c
            ; bwd-R    = g
            ; rightInv = λ d i →
                homEqFinalId (D , xcD) wfD (λ y → f (g y)) fg-h i d
            }

      finalTransfer : {C D : Type ℓ}
          (xcC : C → P A B C) (xcD : D → P A B D)
        → CoalgEquiv (C , xcC) (D , xcD)
        → isFinal (C , xcC) → isFinal (D , xcD)
      finalTransfer {C} {D} xcC xcD (e , (f-h , g-h)) wfC (E , ec) =
          (centerD , centerD-h) , uniqD
        where
          f = fwd e
          g = bwd-L e

          cC   = fst (fst (wfC (E , ec)))
          cC-h = snd (fst (wfC (E , ec)))

          centerD : E → D
          centerD x = f (cC x)

          centerD-h : isCoalgHom (E , ec) (D , xcD) centerD
          centerD-h = ∘-isCoalgHom {C₁ = E , ec} {C₂ = C , xcC} {C₃ = D , xcD}
                                   {f = cC} {g = f} cC-h f-h

          -- `f ∘ g ≡ id` pointwise, derived from the bi-invertible `e`.
          fwd-bwdL : (z : D) → f (g z) ≡ z
          fwd-bwdL z =
              cong f (cong g (sym (rightInv e z)) ∙ leftInv e (bwd-R e z))
            ∙ rightInv e z

          uniqD : (h' : E → D) (p' : isCoalgHom (E , ec) (D , xcD) h')
                → centerD ≡ h'
          uniqD h' p' = funExt (λ x →
              cong f (λ i → cC≡gh' i x) ∙ fwd-bwdL (h' x))
            where
              gh'-h : isCoalgHom (E , ec) (C , xcC) (λ x → g (h' x))
              gh'-h = ∘-isCoalgHom {C₁ = E , ec} {C₂ = D , xcD} {C₃ = C , xcC}
                                   {f = h'} {g = g} p' g-h
              cC≡gh' : cC ≡ (λ x → g (h' x))
              cC≡gh' = snd (wfC (E , ec)) (λ x → g (h' x)) gh'-h

      -- Definition 4.12: a coalgebra configuration determines a coalgebra
      -- isomorphism (dual of `algConfigToAlgEquiv`).
      coalgConfigToCoalgEquiv : {C D : Type ℓ} (cfg : CoalgConfig A B C D)
        → CoalgEquiv (C , fst (fst cfg)) (D , fst (snd cfg))
      coalgConfigToCoalgEquiv ((xcC , wfC) , (xcD , wfD)) =
        coalgEquivFromFinals xcC xcD wfC wfD

    {-
      Theorem 4.24 (1) (Coinductive Configurations are Coalgebra Isomorphisms)
       Final-tier theorem.

           MTypeCoConfig A B C D
             ↔
           Σ xcC Σ xcD (CoalgEquiv (C,xcC) (D,xcD) × isFinal (C,xcC))

       A coinductive configuration over the M-type signature is exactly
       (logically) a coalgebra isomorphism whose source is final.
       This is a biimplication, not a `≃`: `isFinal` stores its
       center's hom-witness, which it does not pin, so it is not a
       proposition and the round-trips do not close.  The strong tier
       below is a genuine `≃`.
    -}

    CoCoalgIsoData : (A : Type ℓ) (B : A → Type ℓ) (C D : Type ℓ) → Type (lsuc ℓ)
    CoCoalgIsoData A B C D =
      Σ (C → P A B C) (λ xcC →
      Σ (D → P A B D) (λ xcD →
        CoalgEquiv (C , xcC) (D , xcD) × isFinal (C , xcC)))

    module _ {A : Type ℓ} {B : A → Type ℓ} {C D : Type ℓ} where

      toIso : MTypeCoConfig A B C D → CoCoalgIsoData A B C D
      toIso cfg =
          xcC , xcD , coalgEquivFromFinals xcC xcD wfC wfD , wfC
        where
          open CoConfig cfg
          fC = coalgBridgeFwd coindCoalgC
          fD = coalgBridgeFwd coindCoalgD
          xcC = fst fC
          wfC = snd fC
          xcD = fst fD
          wfD = snd fD

      fromIso : CoCoalgIsoData A B C D → MTypeCoConfig A B C D
      fromIso (xcC , xcD , equiv , wfC) = record
        { coindCoalgC = coalgBridgeBwd (xcC , wfC)
        ; coindCoalgD = coalgBridgeBwd (xcD , finalTransfer xcC xcD equiv wfC)
        }

      -- Theorem 4.24 (1) (Coinductive Configurations are Coalgebra Isomorphisms)
      mtypeCoConfig↔ :
        MTypeCoConfig A B C D ↔ CoCoalgIsoData A B C D
      mtypeCoConfig↔ = record { fwd = toIso ; bwd = fromIso }

    {-
      Theorem 4.24 (2), supporting lemmas follow; the theorem is `hcoConfigEqvˢ`.
       Strong tier: HCoConfig ≃ isHFinal-isomorphism.

       Now a genuine `_≃_`, because `isHFinal` *is* a proposition.
       The generic supporting machinery (path algebra, h-levels, the
       `≃`-combinators) lives in `cubical-common`; what remains here is
       the coalgebra-specific part.
    -}

    {-
       Coalgebra category laws and finality transfer.

       Function parts of associativity / right-unit are definitional; the
       `isCoalgHom`-witness parts reduce (modulo P-functoriality, which is
       definitional) to `∙`-associativity / `∙`-right-unit and `cong-∙`.
       `hFinalTransfer` then makes `CoalgHom S D` a retract of the
       contractible `CoalgHom S C` — no univalence.
    -}

    module _ {A : Type ℓ} {B : A → Type ℓ} where

      -- Right unit.  Witness = `kh ∙ refl` (P-mor id = id by η; the
      -- second whisker is constant); closed by `∙-idr`.
      CoalgHom-idR :
        (C₁ C₂ : P-Coalg A B) (k : CoalgHom C₁ C₂)
        → CoalgHom-∘ C₁ C₂ C₂ k (id-coalgHom C₂) ≡ k
      CoalgHom-idR C₁ C₂ (kf , kh) i = kf , ∙-idr kh i

      -- Associativity.  Witness via `cong-∙` (twice) and `∙assoc`; the
      -- three P-functoriality re-bracketings are definitional.
      CoalgHom-∘-assoc :
        (C₁ C₂ C₃ C₄ : P-Coalg A B)
        (k : CoalgHom C₁ C₂) (l : CoalgHom C₂ C₃) (n : CoalgHom C₃ C₄)
        → CoalgHom-∘ C₁ C₃ C₄ (CoalgHom-∘ C₁ C₂ C₃ k l) n
          ≡ CoalgHom-∘ C₁ C₂ C₄ k (CoalgHom-∘ C₂ C₃ C₄ l n)
      CoalgHom-∘-assoc C₁ C₂ C₃ C₄ (kf , kh) (lf , lh) (nf , nh) i =
          (λ x → nf (lf (kf x)))
        , ( cong (_∙ (λ i₁ x → nh i₁ (lf (kf x))))
                 (cong-∙ (λ (φ : CoalgCarrier C₁ → P A B (CoalgCarrier C₃))
                            x → P-mor nf (φ x))
                         (λ i₁ x → P-mor lf (kh i₁ x))
                         (λ i₁ x → lh i₁ (kf x)))
          ∙ ∙assoc (λ i₁ x → P-mor nf (P-mor lf (kh i₁ x)))
                   (λ i₁ x → P-mor nf (lh i₁ (kf x)))
                   (λ i₁ x → nh i₁ (lf (kf x)))
          ∙ cong ((λ i₁ x → P-mor nf (P-mor lf (kh i₁ x))) ∙_)
                 (sym (cong-∙ (λ (φ : CoalgCarrier C₂ → P A B (CoalgCarrier C₄))
                                x → φ (kf x))
                              (λ i₁ x → P-mor nf (lh i₁ x))
                              (λ i₁ x → nh i₁ (lf x)))) ) i

      -- Section 4.4 (`CoalgEquiv^H`, used in Theorem 4.24 (2))
      -- Σ-level coalgebra isomorphism (the exact dual of `AlgEquiv`).
      isCoalgEquivˢ : (X Y : P-Coalg A B) → CoalgHom X Y → Type ℓ
      isCoalgEquivˢ X Y f =
          Σ (CoalgHom Y X) (λ g → CoalgHom-∘ X Y X f g ≡ id-coalgHom X)
        × Σ (CoalgHom Y X) (λ h → CoalgHom-∘ Y X Y h f ≡ id-coalgHom Y)

      -- Section 4.4 (`CoalgEquiv^H`)
      CoalgEquivˢ : (X Y : P-Coalg A B) → Type ℓ
      CoalgEquivˢ X Y = Σ (CoalgHom X Y) (isCoalgEquivˢ X Y)

      -- Finality transfers across a Σ-level coalgebra iso: `CoalgHom S D`
      -- is a retract of the contractible `CoalgHom S C`.
      hFinalTransfer : {C D : Type ℓ}
          {xcC : C → P A B C} {xcD : D → P A B D}
        → CoalgEquivˢ (C , xcC) (D , xcD)
        → isHFinal (C , xcC) → isHFinal (D , xcD)
      hFinalTransfer {C} {D} {xcC} {xcD}
                    (f , ((g , _) , (h , hf≡id))) isHFinalC (S , sc) =
        retract-isContr r s rs (isHFinalC (S , sc))
        where
          r : CoalgHom (S , sc) (C , xcC) → CoalgHom (S , sc) (D , xcD)
          r k = CoalgHom-∘ (S , sc) (C , xcC) (D , xcD) k f
          s : CoalgHom (S , sc) (D , xcD) → CoalgHom (S , sc) (C , xcC)
          s m = CoalgHom-∘ (S , sc) (D , xcD) (C , xcC) m h
          rs : (m : CoalgHom (S , sc) (D , xcD)) → r (s m) ≡ m
          rs m =
              CoalgHom-∘-assoc (S , sc) (D , xcD) (C , xcC) (D , xcD) m h f
            ∙ cong (CoalgHom-∘ (S , sc) (D , xcD) (D , xcD) m) hf≡id
            ∙ CoalgHom-idR (S , sc) (D , xcD) m

      -- `isHFinal` is a proposition: a Π of `isContr`s.
      isProp-isHFinal : (F : P-Coalg A B) → isProp (isHFinal F)
      isProp-isHFinal F = isPropΠ (λ _ → isPropIsContr)

      -- An endomorphism of a final coalgebra is the identity (dual of
      -- `homEqInitId`), now at the full `CoalgHom` level via
      -- contractibility.
      homEqHFinalId : (F : P-Coalg A B) → isHFinal F
                   → (k : CoalgHom F F) → k ≡ id-coalgHom F
      homEqHFinalId F finalF k =
        sym (snd (finalF F) k) ∙ snd (finalF F) (id-coalgHom F)

      -- Two final coalgebras for the same functor are isomorphic — the
      -- two unique homs, with both round-trips the identity (dual of
      -- `algConfigToAlgEquiv`).
      coalgEquivˢFromFinals : {C D : Type ℓ}
          (xcC : C → P A B C) (xcD : D → P A B D)
        → isHFinal (C , xcC) → isHFinal (D , xcD)
        → CoalgEquivˢ (C , xcC) (D , xcD)
      coalgEquivˢFromFinals {C} {D} xcC xcD finalC finalD =
          fwd-hom , ((bwd-hom , left) , (bwd-hom , right))
        where
          fwd-hom : CoalgHom (C , xcC) (D , xcD)
          fwd-hom = fst (finalD (C , xcC))
          bwd-hom : CoalgHom (D , xcD) (C , xcC)
          bwd-hom = fst (finalC (D , xcD))
          left : CoalgHom-∘ (C , xcC) (D , xcD) (C , xcC) fwd-hom bwd-hom
                   ≡ id-coalgHom (C , xcC)
          left = homEqHFinalId (C , xcC) finalC _
          right : CoalgHom-∘ (D , xcD) (C , xcC) (D , xcD) bwd-hom fwd-hom
                    ≡ id-coalgHom (D , xcD)
          right = homEqHFinalId (D , xcD) finalD _

      -- Section 4.4 (uniqueness of coinductive repair)
      -- `CoalgEquivˢ` out of a final source is a proposition (dual of
      -- `isProp-AlgEquiv`).
      isProp-CoalgEquivˢ : {X Y : P-Coalg A B}
                         → isHFinal X → isProp (CoalgEquivˢ X Y)
      isProp-CoalgEquivˢ {X} {Y} finalX e1 e2 =
        Σ-isProp homXY-isProp isCoalgEquivˢ-isProp e1 e2
        where
          finalY : isHFinal Y
          finalY = hFinalTransfer e1 finalX
          homXY-isProp : isProp (CoalgHom X Y)
          homXY-isProp = isContr→isProp (finalY X)
          homYX-isProp : isProp (CoalgHom Y X)
          homYX-isProp = isContr→isProp (finalX Y)
          isCoalgEquivˢ-isProp : (f : CoalgHom X Y)
                               → isProp (isCoalgEquivˢ X Y f)
          isCoalgEquivˢ-isProp f =
            Σ-isProp
              (Σ-isProp homYX-isProp
                 (λ g → isContr→isSet (finalX X) _ (id-coalgHom X)))
              (λ _ → Σ-isProp homYX-isProp
                 (λ h → isContr→isSet (finalY Y) _ (id-coalgHom Y)))

    {-
       Definition 4.12 (homotopy coalgebra configuration): `FinalCoalgOnˢ`
       and `HCoalgConfig` below.
       The strong carrier bridge  HCoindCoalg (MTypeSig) X ≃ FinalCoalgOnˢ X,
       where `FinalCoalgOnˢ A B X = Σ xc (isHFinal (X , xc))`.  The
       op-form coalg-hom space `HomOp` (what `corec-uniq-Σ` is about) and
       the polynomial `CoalgHom` are definitionally iso (both round-trips
       `refl`), so contractibility transports.
    -}

    FinalCoalgOnˢ : (A : Type ℓ) (B : A → Type ℓ) (X : Type ℓ) → Type (lsuc ℓ)
    FinalCoalgOnˢ A B X = Σ (X → P A B X) (λ xc → isHFinal (X , xc))

    -- Definition 4.12 (homotopy coalgebra configuration)
    HCoalgConfig : (A : Type ℓ) (B : A → Type ℓ) (C D : Type ℓ) → Type (lsuc ℓ)
    HCoalgConfig A B C D = FinalCoalgOnˢ A B C × FinalCoalgOnˢ A B D

    module _ {A : Type ℓ} {B : A → Type ℓ} {X : Type ℓ} where

      bridgeˢFwd : HCoindCoalg (MTypeSignature A B) X → FinalCoalgOnˢ A B X
      bridgeˢFwd hind = xc , hfin
        where
          open HCoindCoalg hind
          xc : X → P A B X
          xc x = out→P (destr tt x)

          hfin : isHFinal (X , xc)
          hfin (E , ec) = retract-isContr toCoalg fromCoalg rt isContrOp
            where
              destrE : DestrAlgebra (MTypeSignature A B) E
              destrE op e = P→out (ec e)

              OpHom : (E → X) → Type ℓ
              OpHom h = (op : ⊤) (e : E)
                      → destr op (h e)
                          ≡ mapOutputs (MTypeArity A B op) h (destrE op e)

              HomOp : Type ℓ
              HomOp = Σ (E → X) OpHom

              isContrOp : isContr HomOp
              isContrOp =
                  (corec destrE , corec-β destrE)
                , (λ hp → sym (λ i →
                      fst (corec-uniq-Σ destrE (fst hp) (snd hp)) i
                    , snd (corec-uniq-Σ destrE (fst hp) (snd hp)) i))

              toCoalg : HomOp → CoalgHom (E , ec) (X , xc)
              toCoalg (h , h-hom) =
                h , funExt (λ e → sym (cong out→P (h-hom tt e)))

              fromCoalg : CoalgHom (E , ec) (X , xc) → HomOp
              fromCoalg (h , kh) =
                h , (λ op e → cong P→out (sym (λ i → kh i e)))

              rt : (k : CoalgHom (E , ec) (X , xc))
                 → toCoalg (fromCoalg k) ≡ k
              rt k = refl

      bridgeˢBwd : FinalCoalgOnˢ A B X → HCoindCoalg (MTypeSignature A B) X
      bridgeˢBwd (xc , hfin) = record
        { destr = λ op x → P→out (xc x)
        ; corec = λ {C} destrC c →
            fst (fst (hfin (C , λ c' → out→P (destrC tt c')))) c
        ; corec-β = λ {C} destrC op c →
            cong P→out
              (sym (λ i → snd (fst (hfin (C , λ c' → out→P (destrC tt c')))) i c))
        ; corec-uniq-Σ = λ {C} destrC h h-hom →
            let ecC : C → P A B C
                ecC = λ c' → out→P (destrC tt c')
                HomOpC : Type ℓ
                HomOpC = Σ (C → X) (λ h' → (op : ⊤) (e : C)
                           → P→out (xc (h' e))
                               ≡ mapOutputs (MTypeArity A B op) h' (destrC op e))
                khom : isCoalgHom (C , ecC) (X , xc) h
                khom = funExt (λ c → sym (cong out→P (h-hom tt c)))
                mapped : CoalgHom (C , ecC) (X , xc) → HomOpC
                mapped k = fst k
                         , (λ op e → cong P→out (sym (λ i → snd k i e)))
                pth : mapped (h , khom) ≡ mapped (fst (hfin (C , ecC)))
                pth = cong mapped (sym (snd (hfin (C , ecC)) (h , khom)))
            in (λ i → fst (pth i)) , (λ i → snd (pth i))
        }

      -- `FinalCoalgOnˢ` round-trip: `xc` returns by record-η, the
      -- finality witness by `isProp-isHFinal`.
      bridgeˢε : (F : FinalCoalgOnˢ A B X) → bridgeˢFwd (bridgeˢBwd F) ≡ F
      bridgeˢε (xc , hfin) i =
          xc
        , isProp-isHFinal (X , xc)
            (snd (bridgeˢFwd (bridgeˢBwd (xc , hfin)))) hfin i

      -- `HCoindCoalg` round-trip: `destr`/`corec`/`corec-β` return by
      -- record-η; `corec-uniq-Σ` lands in a path-space of the
      -- contractible op-hom space, hence a proposition.
      bridgeˢη : (hind : HCoindCoalg (MTypeSignature A B) X)
               → bridgeˢBwd (bridgeˢFwd hind) ≡ hind
      bridgeˢη hind i = record
        { destr        = destr
        ; corec        = corec
        ; corec-β      = corec-β
        ; corec-uniq-Σ = λ {C} destrC h h-hom → uniqBody {C} destrC h h-hom i
        }
        where
          open HCoindCoalg hind

          isProp-Σform :
            {C : Type ℓ} (destrC : DestrAlgebra (MTypeSignature A B) C)
            (h : C → X)
            (h-hom : (op : ⊤) (e : C)
                   → destr op (h e)
                       ≡ mapOutputs (MTypeArity A B op) h (destrC op e))
            → isProp (Σ (h ≡ corec destrC)
                        (λ p → PathP (λ i₁ → (op : ⊤) (c : C)
                                       → destr op (p i₁ c)
                                           ≡ mapOutputs (MTypeArity A B op)
                                                        (p i₁) (destrC op c))
                                     h-hom (corec-β destrC)))
          isProp-Σform {C} destrC h h-hom = Σform-isProp
            where
              OpHom : (C → X) → Type ℓ
              OpHom h' = (op : ⊤) (e : C)
                       → destr op (h' e)
                           ≡ mapOutputs (MTypeArity A B op) h' (destrC op e)
              HomOp : Type ℓ
              HomOp = Σ (C → X) OpHom

              isContrHomOp : isContr HomOp
              isContrHomOp =
                  (corec destrC , corec-β destrC)
                , (λ hp → sym (λ i₁ →
                      fst (corec-uniq-Σ destrC (fst hp) (snd hp)) i₁
                    , snd (corec-uniq-Σ destrC (fst hp) (snd hp)) i₁))

              Σform : Type ℓ
              Σform = Σ (h ≡ corec destrC)
                        (λ p → PathP (λ i₁ → OpHom (p i₁)) h-hom (corec-β destrC))

              toPath : Σform → ((h , h-hom) ≡ (corec destrC , corec-β destrC))
              toPath (p , pp) i₁ = p i₁ , pp i₁

              fromPath : ((h , h-hom) ≡ (corec destrC , corec-β destrC)) → Σform
              fromPath q = (λ i₁ → fst (q i₁)) , (λ i₁ → snd (q i₁))

              Σform-isProp : isProp Σform
              Σform-isProp x y =
                cong fromPath
                  (isContr→isSet isContrHomOp _ _ (toPath x) (toPath y))

          uniqBody :
            {C : Type ℓ} (destrC : DestrAlgebra (MTypeSignature A B) C)
            (h : C → X)
            (h-hom : (op : ⊤) (e : C)
                   → destr op (h e)
                       ≡ mapOutputs (MTypeArity A B op) h (destrC op e))
            → HCoindCoalg.corec-uniq-Σ (bridgeˢBwd (bridgeˢFwd hind)) destrC h h-hom
                ≡ corec-uniq-Σ destrC h h-hom
          uniqBody destrC h h-hom =
            isProp-Σform destrC h h-hom
              (HCoindCoalg.corec-uniq-Σ (bridgeˢBwd (bridgeˢFwd hind)) destrC h h-hom)
              (corec-uniq-Σ destrC h h-hom)

      bridgeˢ : HCoindCoalg (MTypeSignature A B) X ≃ FinalCoalgOnˢ A B X
      bridgeˢ = record
        { fwd = bridgeˢFwd ; bwd-L = bridgeˢBwd ; leftInv = bridgeˢη
        ; bwd-R = bridgeˢBwd ; rightInv = bridgeˢε }

    {-
       The "two finals ⇄ one-final-iso" equivalence (dual of
       `fullAlgIso`).  Both round-trips close by propositionality:
       `isProp-isHFinal` and `isProp-CoalgEquivˢ`.
    -}

    CoCoalgIsoDataˢ : (A : Type ℓ) (B : A → Type ℓ) (C D : Type ℓ)
                    → Type (lsuc ℓ)
    CoCoalgIsoDataˢ A B C D =
      Σ (C → P A B C) (λ xcC →
      Σ (D → P A B D) (λ xcD →
        CoalgEquivˢ (C , xcC) (D , xcD) × isHFinal (C , xcC)))

    module _ {A : Type ℓ} {B : A → Type ℓ} {C D : Type ℓ} where

      fullCoalgIsoˢ :
        HCoalgConfig A B C D ≃ CoCoalgIsoDataˢ A B C D
      fullCoalgIsoˢ = record
        { fwd = λ ((xcC , finalC) , (xcD , finalD)) →
            xcC , xcD , coalgEquivˢFromFinals xcC xcD finalC finalD , finalC
        ; bwd-L = bwdF
        ; leftInv = λ { ((xcC , finalC) , (xcD , finalD)) i →
              (xcC , finalC)
            , (xcD , isProp-isHFinal (D , xcD)
                       (hFinalTransfer (coalgEquivˢFromFinals xcC xcD finalC finalD)
                                      finalC)
                       finalD i) }
        ; bwd-R = bwdF
        ; rightInv = λ { (xcC , xcD , equivˢ , finalC) i →
              xcC , xcD
            , isProp-CoalgEquivˢ finalC
                (coalgEquivˢFromFinals xcC xcD finalC
                   (hFinalTransfer equivˢ finalC))
                equivˢ i
            , finalC }
        }
        where
          bwdF : CoCoalgIsoDataˢ A B C D → HCoalgConfig A B C D
          bwdF (xcC , xcD , equivˢ , finalC) =
              (xcC , finalC)
            , (xcD , hFinalTransfer equivˢ finalC)

      -- Record-η: an `HCoConfig` is its pair of `HCoindCoalg`s.
      HCoConfig-η-≃ :
        HCoConfig (MTypeSignature A B) C D
          ≃ (HCoindCoalg (MTypeSignature A B) C × HCoindCoalg (MTypeSignature A B) D)
      HCoConfig-η-≃ = record
        { fwd     = λ hcfg → HCoConfig.hCoindCoalgC hcfg , HCoConfig.hCoindCoalgD hcfg
        ; bwd-L   = λ p → record { hCoindCoalgC = fst p ; hCoindCoalgD = snd p }
        ; leftInv = λ _ → refl
        ; bwd-R   = λ p → record { hCoindCoalgC = fst p ; hCoindCoalgD = snd p }
        ; rightInv = λ _ → refl
        }

      {-
         Theorem 4.24 (2) (Coinductive Configurations are Coalgebra Isomorphisms)
         Strong-tier theorem.

             HCoConfig (MTypeSignature A B) C D
               ≃
             Σ xcC Σ xcD (CoalgEquivˢ (C,xcC) (D,xcD) × isHFinal (C,xcC))

         A genuine equivalence (not just `_↔_`): a strong coinductive
         configuration is exactly a Σ-level coalgebra isomorphism whose
         source is a final coalgebra.
      -}
      hcoConfigEqvˢ :
        HCoConfig (MTypeSignature A B) C D ≃ CoCoalgIsoDataˢ A B C D
      hcoConfigEqvˢ =
        ≃-trans HCoConfig-η-≃
          (≃-trans (≃-× (bridgeˢ {X = C}) (bridgeˢ {X = D})) fullCoalgIsoˢ)
