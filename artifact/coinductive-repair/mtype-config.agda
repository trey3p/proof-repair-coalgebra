{-# OPTIONS --cubical --guardedness --safe #-}

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import coinductive-repair.mtype hiding (corec)
open import coinductive-repair.config
open import coinductive-repair.coconfig-coalg-equiv
  using (MTypeArity; MTypeSignature; MTypeCoindCoalg; MTypeCoConfig)

{-  Lemma 4.23
    M-type configurations: every cosignature embeds into the
    single-destructor M-type signature (shape + positions), and every
    `CoConfig` induces an M-type configuration
    (`allCoConfigMTypeCoConfig`) without changing the repair
    equivalence (`mtypeCoConfigEquivAgree-f` / `-g`). Dual of
    `inductive-repair.wtype-config`; the core is the polynomial view
    of `Outputs` (`convert` / `unconvert`). A shape observes every
    destructor at once (a product over labels, dual to the inductive
    coproduct of constructors), and a position picks a label together
    with a recursive position in its shape.
-}
module coinductive-repair.mtype-config {ℓ : Level} where

    {-
        Local empty and sum types (no library imports), for the
        positions of the recursive outputs.
    -}
    data ⊥ : Type ℓ where

    ⊥-elim : {C : Type ℓ} → ⊥ → C
    ⊥-elim ()

    data _⊎_ (A B : Type ℓ) : Type ℓ where
      inl : A → A ⊎ B
      inr : B → A ⊎ B

    {-
        Sum eliminator, factored to module scope (as `β-emb-pos` on
        the inductive side) so every occurrence is intensionally the
        same function.
    -}
    sumElim : {D X C : Type ℓ} → (D → C) → (X → C) → D ⊎ X → C
    sumElim r q (inl d) = r d
    sumElim r q (inr z) = q z

    -- Sum-η pointwise: rebuilding a sum function from its two
    -- restrictions agrees with it on every input.
    sumElim-η : {D X C : Type ℓ} (p : D ⊎ X → C) (w : D ⊎ X) →
                sumElim (λ d → p (inl d)) (λ z → p (inr z)) w ≡ p w
    sumElim-η p (inl d) = refl
    sumElim-η p (inr z) = refl

    -- `sumElim` commutes with postcomposition.
    sumElim-map : {D X C C' : Type ℓ} (h : C → C') (r : D → C) (q : X → C)
                  (w : D ⊎ X) →
                  sumElim (λ d → h (r d)) (λ z → h (q z)) w
                    ≡ h (sumElim r q w)
    sumElim-map h r q (inl d) = refl
    sumElim-map h r q (inr z) = refl

    module _ {sig : CoSignature {ℓ}} where
        arity = CoSignature.arity sig
        Op = CoSignature.Op sig

        {-
            Positions of the recursive outputs inside a shape: a
            "shape" is `Outputs` with the carrier erased to `⊤`.
        -}
        recPos : (cs : DestrArity {ℓ}) → Outputs cs (⊤ {ℓ}) → Type ℓ
        recPos Done         _        = ⊥
        recPos (Nonrec A k) (a , s)  = recPos (k a) s
        recPos (Rec D cs)   (_ , s)  = D ⊎ recPos cs s

        {-
            Polynomial view: `Outputs cs X` is equivalent to a shape
            together with a function on its recursive positions;
            `convert` and `unconvert` are the two directions.
        -}
        convert : (cs : DestrArity {ℓ}) {X : Type ℓ} → Outputs cs X →
                  Σ (Outputs cs (⊤ {ℓ})) (λ s → recPos cs s → X)
        convert Done         _        = (tt , ⊥-elim)
        convert (Nonrec A k) (a , o)  =
            ((a , fst (convert (k a) o)) , snd (convert (k a) o))
        convert (Rec D cs)   (r , o)  =
            (((λ _ → tt) , fst (convert cs o)) , sumElim r (snd (convert cs o)))

        unconvert : (cs : DestrArity {ℓ}) {X : Type ℓ} →
                    Σ (Outputs cs (⊤ {ℓ})) (λ s → recPos cs s → X) →
                    Outputs cs X
        unconvert Done         _              = tt
        unconvert (Nonrec A k) ((a , s) , p)  = (a , unconvert (k a) (s , p))
        unconvert (Rec D cs)   ((_ , s) , p)  =
            ((λ d → p (inl d)) , unconvert cs (s , (λ z → p (inr z))))

        -- `unconvert ∘ convert = id`, by structural induction; the
        -- `Rec` case collapses via `sumElim`'s computation rules.
        unconvert-convert : {X : Type ℓ} (cs : DestrArity {ℓ}) (o : Outputs cs X) →
                            unconvert cs (convert cs o) ≡ o
        unconvert-convert Done         _         = refl
        unconvert-convert (Nonrec A k) (a , o) i = (a , unconvert-convert (k a) o i)
        unconvert-convert (Rec D cs)   (r , o) i = (r , unconvert-convert cs o i)

        -- `convert ∘ unconvert = id`, up to sum-η on the positions
        -- (the shape side matches by `⊤`- and function-η).
        convert-unconvert : {X : Type ℓ} (cs : DestrArity {ℓ})
                            (sp : Σ (Outputs cs (⊤ {ℓ})) (λ s → recPos cs s → X)) →
                            convert cs (unconvert cs sp) ≡ sp
        convert-unconvert Done         (_ , p)       i = (tt , eA i)
          where
            eA : ⊥-elim ≡ p
            eA = funExt (λ ())
        convert-unconvert (Nonrec A k) ((a , s) , p) i =
            ((a , fst (ih i)) , snd (ih i))
          where
            ih = convert-unconvert (k a) (s , p)
        convert-unconvert (Rec D cs)   ((_ , s) , p)   = step1 ∙ step2
          where
            ih = convert-unconvert cs (s , (λ z → p (inr z)))
            step1 : convert (Rec D cs) (unconvert (Rec D cs) (((λ _ → tt) , s) , p))
                      ≡ (((λ _ → tt) , s) ,
                         sumElim (λ d → p (inl d)) (λ z → p (inr z)))
            step1 i = (((λ _ → tt) , fst (ih i)) ,
                       sumElim (λ d → p (inl d)) (snd (ih i)))
            step2 : (((λ _ → tt) , s) ,
                     sumElim (λ d → p (inl d)) (λ z → p (inr z)))
                      ≡ (((λ _ → tt) , s) , p)
            step2 i = (((λ _ → tt) , s) , funExt (sumElim-η p) i)

        -- Naturality of `convert` in the carrier: converting a mapped
        -- output keeps the shape and postcomposes the positions.
        convert-mapOutputs : (cs : DestrArity {ℓ}) {X Y : Type ℓ} (h : X → Y)
                             (o : Outputs cs X) →
                             convert cs (mapOutputs cs h o)
                               ≡ (fst (convert cs o) ,
                                  (λ z → h (snd (convert cs o) z)))
        convert-mapOutputs Done         h _       i = (tt , eA i)
          where
            eA : ⊥-elim ≡ (λ z → h (⊥-elim z))
            eA = funExt (λ ())
        convert-mapOutputs (Nonrec A k) h (a , o) i =
            ((a , fst (ih i)) , snd (ih i))
          where
            ih = convert-mapOutputs (k a) h o
        convert-mapOutputs (Rec D cs)   h (r , o)   = step1 ∙ step2
          where
            w  = convert cs o
            ih = convert-mapOutputs cs h o
            step1 : convert (Rec D cs) (mapOutputs (Rec D cs) h (r , o))
                      ≡ (((λ _ → tt) , fst w) ,
                         sumElim (λ d → h (r d)) (λ z → h (snd w z)))
            step1 i = (((λ _ → tt) , fst (ih i)) ,
                       sumElim (λ d → h (r d)) (snd (ih i)))
            step2 : (((λ _ → tt) , fst w) ,
                     sumElim (λ d → h (r d)) (λ z → h (snd w z)))
                      ≡ (((λ _ → tt) , fst w) , (λ z → h (sumElim r (snd w) z)))
            step2 i = (((λ _ → tt) , fst w) , funExt (sumElim-map h r (snd w)) i)

        -- Naturality of `unconvert` in the carrier (mirror of the
        -- inductive `unconvert-mapArgs`).
        unconvert-mapOutputs : (cs : DestrArity {ℓ}) {X Y : Type ℓ} (h : X → Y)
                               (sp : Σ (Outputs cs (⊤ {ℓ})) (λ s → recPos cs s → X)) →
                               unconvert cs (fst sp , (λ z → h (snd sp z)))
                                 ≡ mapOutputs cs h (unconvert cs sp)
        unconvert-mapOutputs Done         h _             = refl
        unconvert-mapOutputs (Nonrec A k) h ((a , s) , p) i =
            (a , unconvert-mapOutputs (k a) h (s , p) i)
        unconvert-mapOutputs (Rec D cs)   h ((_ , s) , p) i =
            ((λ d → h (p (inl d))) ,
             unconvert-mapOutputs cs h (s , (λ z → p (inr z))) i)

        {-
            Lemma 4.23: the polynomial read off the cosignature.
            The signature-wide M-type polynomial: a shape observes
            every destructor at once, a position picks a label and a
            recursive position in its shape.
        -}
        A : Type ℓ
        A = (op : Op) → Outputs (arity op) (⊤ {ℓ})

        B : A → Type ℓ
        B a = Σ Op (λ op → recPos (arity op) (a op))

        mtypeSignature : CoSignature
        mtypeSignature = MTypeSignature A B

        {-
            Translate an M-type destructor algebra on a source carrier
            back to a `sig` destructor algebra: project the per-label
            shape and positions, then `unconvert`.
        -}
        origDestrAlg : {E : Type ℓ} → DestrAlgebra mtypeSignature E →
                       DestrAlgebra sig E
        origDestrAlg destrE op e =
            unconvert (arity op)
                (fst (destrE tt e) op ,
                 (λ z → fst (snd (destrE tt e)) (op , z)))

        module _ {X : Type ℓ} (coalg : CoindCoalg sig X) where
            open CoindCoalg coalg

            {-
                The M-type destructor: observe `x` under every
                destructor of `sig` and package the results as one
                shape with one positions-function.
            -}
            mtypeDestr : DestrAlgebra mtypeSignature X
            mtypeDestr _ x =
                (λ op → fst (convert (arity op) (destr op x))) ,
                (λ bz → snd (convert (arity (fst bz)) (destr (fst bz) x)) (snd bz)) ,
                tt

            mtypeCorec : {E : Type ℓ} → DestrAlgebra mtypeSignature E → E → X
            mtypeCorec destrE = corec (origDestrAlg destrE)

            {-
                β for the M-type structure: per label, the original β
                followed by `convert`'s naturality and the
                convert/unconvert round-trip; the per-label paths
                assemble into one Σ-path by interval abstraction.
            -}
            mtypeCorec-β : {E : Type ℓ} (destrE : DestrAlgebra mtypeSignature E)
                           (op : ⊤ {ℓ}) (e : E) →
                           mtypeDestr op (mtypeCorec destrE e)
                             ≡ mapOutputs (MTypeArity A B op) (mtypeCorec destrE)
                                          (destrE op e)
            mtypeCorec-β {E} destrE _ e i =
                ((λ op → fst (q op i)) ,
                 (λ bz → snd (q (fst bz) i) (snd bz)) ,
                 tt)
              where
                dE' : DestrAlgebra sig E
                dE' = origDestrAlg destrE

                q : (op : Op) →
                    convert (arity op) (destr op (corec dE' e))
                      ≡ (fst (destrE tt e) op ,
                         (λ z → corec dE' (fst (snd (destrE tt e)) (op , z))))
                q op =
                    cong (convert (arity op)) (corec-β dE' op e)
                  ∙ convert-mapOutputs (arity op) (corec dE') (dE' op e)
                  ∙ cong (λ w → (fst w , (λ z → corec dE' (snd w z))))
                         (convert-unconvert (arity op)
                             (fst (destrE tt e) op ,
                              (λ z → fst (snd (destrE tt e)) (op , z))))

            {-
                η for the M-type structure: an M-type homomorphism
                projects, label by label, to a homomorphism for the
                original destructors (via `unconvert`'s naturality),
                and the original `corec-η` applies.
            -}
            mtypeCorec-η : {E : Type ℓ} (destrE : DestrAlgebra mtypeSignature E)
                           (h : E → X) →
                           ((op : ⊤ {ℓ}) (e : E) →
                            mtypeDestr op (h e)
                              ≡ mapOutputs (MTypeArity A B op) h (destrE op e)) →
                           (e : E) → h e ≡ mtypeCorec destrE e
            mtypeCorec-η {E} destrE h h-hom = corec-η dE' h orig-hom
              where
                dE' : DestrAlgebra sig E
                dE' = origDestrAlg destrE

                orig-hom : (op : Op) (e : E) →
                           destr op (h e) ≡ mapOutputs (arity op) h (dE' op e)
                orig-hom op e =
                      sym (unconvert-convert (arity op) (destr op (h e)))
                    ∙ cong (unconvert (arity op)) r-path
                    ∙ unconvert-mapOutputs (arity op) h
                          (fst (destrE tt e) op ,
                           (λ z → fst (snd (destrE tt e)) (op , z)))
                  where
                    r-path : convert (arity op) (destr op (h e))
                               ≡ (fst (destrE tt e) op ,
                                  (λ z → h (fst (snd (destrE tt e)) (op , z))))
                    r-path i =
                        (fst (h-hom tt e i) op ,
                         (λ z → fst (snd (h-hom tt e i)) (op , z)))

            coindCoalgMType : MTypeCoindCoalg A B X
            coindCoalgMType = record
                { destr   = mtypeDestr
                ; corec   = mtypeCorec
                ; corec-β = mtypeCorec-β
                ; corec-η = mtypeCorec-η
                }

            allCoindCoalgMType : Σ (Type ℓ) (λ A' → Σ (A' → Type ℓ)
                (λ B' → MTypeCoindCoalg A' B' X))
            allCoindCoalgMType = (A , B , coindCoalgMType)

        module _ {C D : Type ℓ} (cfg : CoConfig sig C D) where
            open CoConfig cfg

            coConfigMTypeCoConfig : MTypeCoConfig A B C D
            coConfigMTypeCoConfig = record
                { coindCoalgC = coindCoalgMType coindCoalgC
                ; coindCoalgD = coindCoalgMType coindCoalgD }

            -- Lemma 4.23 (Coinductive Configurations Faithfully Embed into
            -- M-type Configurations): the embedding, with the polynomial (A , B).
            allCoConfigMTypeCoConfig :
                Σ (Type ℓ) (λ A' → Σ (A' → Type ℓ)
                    (λ B' → MTypeCoConfig A' B' C D))
            allCoConfigMTypeCoConfig = (A , B , coConfigMTypeCoConfig)

            {-
                Lemma 4.23 (faithfulness)
                Fidelity of the embedding: it does not change the
                repair equivalence. Because `corec` is data, the
                M-type forward map is the original corecursor applied
                to a pointwise-equal source coalgebra (the
                convert/unconvert round-trip), so — unlike the
                inductive side, which needs uniqueness of folds — the
                agreement is a single congruence.
            -}
            mtypeCoConfigEquivAgree-f :
                _≃_.fwd (coConfigToEquiv coConfigMTypeCoConfig)
                  ≡ _≃_.fwd (coConfigToEquiv cfg)
            mtypeCoConfigEquivAgree-f =
                cong (λ dA → CoindCoalg.corec coindCoalgD dA)
                     (funExt (λ op → funExt (λ c' →
                         unconvert-convert (arity op)
                             (CoindCoalg.destr coindCoalgC op c'))))

            mtypeCoConfigEquivAgree-g :
                _≃_.bwd-L (coConfigToEquiv coConfigMTypeCoConfig)
                  ≡ _≃_.bwd-L (coConfigToEquiv cfg)
            mtypeCoConfigEquivAgree-g =
                cong (λ dA → CoindCoalg.corec coindCoalgC dA)
                     (funExt (λ op → funExt (λ d' →
                         unconvert-convert (arity op)
                             (CoindCoalg.destr coindCoalgD op d'))))
