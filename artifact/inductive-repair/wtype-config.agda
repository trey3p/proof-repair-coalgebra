{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import inductive-repair.indspec
open import inductive-repair.config

{-  Lemma 3.10
    W-type configurations: every signature embeds into a
    single-constructor W-type signature (shape + positions), and
    every `Config` induces a `WTypeConfig` (`allConfigWTypeConfig`).
    The core is the polynomial view of `Args` (`convert` /
    `unconvert`) with its triangle identity.
-}
module inductive-repair.wtype-config {ℓ : Level} where
    {-
        Definition 3.9 (W-type Configurations)
        The single constructor for a W-type has one nonrec arg and one rec arg.
        `WTypeArity`, `WTypeSignature`, `WTypeIndAlg`, `WTypeConfig`.
    -}
    WTypeArity : {ℓ : Level} → (A : Type ℓ) → (B : A → Type ℓ) → ⊤ {ℓ} → ConstrArity {ℓ}
    WTypeArity A B _ = Nonrec A (λ a → Rec (B a) Done)

    WTypeSignature : {ℓ : Level} → (A : Type ℓ) → (B : A → Type ℓ) → Signature
    WTypeSignature _ _ .Signature.Op = ⊤
    WTypeSignature {ℓ} A B .Signature.arity = WTypeArity {ℓ} A B

    WTypeIndAlg : {ℓ : Level} → (A : Type ℓ) → (B : A → Type ℓ) → (C : Type ℓ) → Type (lsuc ℓ)
    WTypeIndAlg {ℓ} A B C = IndAlg (WTypeSignature {ℓ} A B) C

    -- Definition 3.9 (W-type Configurations)
    WTypeConfig : {ℓ : Level} → (A : Type ℓ) → (B : A → Type ℓ) → (C D : Type ℓ) → Type (lsuc ℓ)
    WTypeConfig {ℓ} A B C D = Config (WTypeSignature {ℓ} A B) C D

    module _ {sig : Signature {ℓ}} where
        arity = Signature.arity sig
        Op = Signature.Op sig

        {-
            Positions of the recursive arguments inside a shape.

            A "shape" is just `Args` with the carrier replaced by `⊤`;
            it forgets the recursive functions and keeps the nonrec data.
        -}
        recPos : (cs : ConstrArity {ℓ}) → Args cs (⊤ {ℓ}) → Type ℓ
        recPos Done         _          = ⊥
        recPos (Nonrec A k) (a , s)    = recPos (k a) s
        recPos (Rec D cs)   (_ , s)    = D ⊎ recPos cs s

        {-
            Sum eliminator used as `β-emb`'s position function. Factored to
            module scope so any term that builds the same sum function (in
            β-emb output, in convert (Rec D cs), in path proofs against it)
            references the same name. Agda treats `λ where`s at distinct
            source locations as intensionally distinct, which would
            otherwise block definitional equalities.
        -}
        β-emb-pos : {D X C : Type ℓ} (r : D → C) (q : X → C) → D ⊎ X → C
        β-emb-pos r q (inl d) = r d
        β-emb-pos r q (inr x) = q x

        {-
            Embed a `Σ Shape (Pos → C)` for `cs` into one for `Rec D cs` by
            providing the rec function `r : D → C`.
        -}
        β-emb : (D : Type ℓ) (cs : ConstrArity {ℓ}) {C : Type ℓ} → (D → C) →
                Σ (Args cs (⊤ {ℓ})) (λ s' → recPos cs s' → C) →
                Σ (Args (Rec D cs) (⊤ {ℓ})) (λ s' → recPos (Rec D cs) s' → C)
        β-emb D cs r q = (((λ _ → tt) , fst q) , β-emb-pos r (snd q))

        {-
            Polynomial view: `Args cs C` is equivalent to
            `Σ (Shape) (λ s → recPos cs s → C)` where `Shape = Args cs ⊤`.
            We provide `convert` and `unconvert` as that equivalence, with
            `unconvert ∘ convert ≡ id` holding definitionally.
        -}
        convert : (cs : ConstrArity {ℓ}) {C : Type ℓ} → Args cs C →
                  Σ (Args cs (⊤ {ℓ})) (λ s → recPos cs s → C)
        convert Done         _          = (tt , λ ())
        convert (Nonrec A k) (a , args) =
            let (s , p) = convert (k a) args in ((a , s) , p)
        convert (Rec D cs)   (r , args) = β-emb D cs r (convert cs args)

        unconvert : (cs : ConstrArity {ℓ}) {C : Type ℓ} →
                    Σ (Args cs (⊤ {ℓ})) (λ s → recPos cs s → C) →
                    Args cs C
        unconvert Done         _              = tt
        unconvert (Nonrec A k) ((a , s) , p)  = (a , unconvert (k a) (s , p))
        unconvert (Rec D cs)   ((_ , s) , p)  =
            ((λ d → p (inl d)) , unconvert cs (s , λ z → p (inr z)))

        {-
            `unconvert ∘ convert = id` holds definitionally — pattern matching
            on `cs` lets `refl` work in every case (using Agda's η for
            functions and for `⊤`).
        -}
        unconvert-convert : {C : Type ℓ} (cs : ConstrArity {ℓ}) (args : Args cs C) →
                            unconvert cs (convert cs args) ≡ args
        unconvert-convert Done         _          = refl
        unconvert-convert (Nonrec A k) (a , args) = ap (λ z → (a , z)) (unconvert-convert (k a) args)
        unconvert-convert (Rec D cs)   (r , args) = ap (λ z → (r , z)) (unconvert-convert cs args)

        {-
            Pointwise refl: `β-emb-pos (λ d → p (inl d)) (λ z → p (inr z))`
            agrees with `p` at every input — by the constructor cases.
            (This is sum-η spelled out by hand. Factored so γ-fix and the
            triangle's `ap`-proof reference the same homotopy.)
        -}
        pwr-of : {D : Type ℓ} (cs : ConstrArity {ℓ}) {C : Type ℓ}
                 {s : Args cs (⊤ {ℓ})}
                 (p : recPos (Rec D cs) ((λ _ → tt) , s) → C) →
                 (x : D ⊎ recPos cs s) →
                 β-emb-pos (λ d → p (inl d)) (λ z → p (inr z)) x ≡ p x
        pwr-of cs p (inl d) = refl
        pwr-of cs p (inr z) = refl

        {-
            The "γ" path for the Rec case of `convert-unconvert`: bridges
            the β-emb-image to the original Σ-pair via the pointwise-refl
            funext. Factored to module scope so `triangle` references the
            same path that `convert-unconvert (Rec D cs)` produces.
        -}
        γ-fix : (D : Type ℓ) (cs : ConstrArity {ℓ}) {C : Type ℓ}
                (s : Args cs (⊤ {ℓ}))
                (p : recPos (Rec D cs) ((λ _ → tt) , s) → C) →
                β-emb D cs (λ d → p (inl d)) (s , λ z → p (inr z))
                ≡ (((λ _ → tt) , s) , p)
        γ-fix D cs s p = Σ-≡-intro refl (ext (pwr-of cs p))

        {-
            `convert ∘ unconvert = id` holds up to funext on positions
            (the shape part matches definitionally via η-on-⊤).
        -}
        convert-unconvert : {C : Type ℓ} (cs : ConstrArity {ℓ})
                            (sp : Σ (Args cs (⊤ {ℓ})) (λ s → recPos cs s → C)) →
                            convert cs (unconvert cs sp) ≡ sp
        convert-unconvert Done         (tt , p)         = Σ-≡-intro refl (ext (λ ()))
        convert-unconvert (Nonrec A k) ((a , s) , p)    =
            ap (λ q → ((a , fst q) , snd q)) (convert-unconvert (k a) (s , p))
        convert-unconvert (Rec D cs)   ((_ , s) , p)    =
              ap (β-emb D cs (λ d → p (inl d))) (convert-unconvert cs (s , λ z → p (inr z)))
            • γ-fix D cs s p

        {-
            Naturality of `unconvert` in the carrier: mapping a function
            over the positions and then unconverting agrees with
            unconverting first and mapping over the recursive children.
        -}
        unconvert-mapArgs : (cs : ConstrArity {ℓ}) {C D : Type ℓ} (h : C → D)
                            (sp : Σ (Args cs (⊤ {ℓ})) (λ s → recPos cs s → C)) →
                            unconvert cs (fst sp , h ∘ snd sp)
                              ≡ mapArgs cs h (unconvert cs sp)
        unconvert-mapArgs Done         h _              = refl
        unconvert-mapArgs (Nonrec A k) h ((a , s) , p)  =
            ap (λ z → (a , z)) (unconvert-mapArgs (k a) h (s , p))
        unconvert-mapArgs (Rec D cs)   h ((_ , s) , p)  =
            ap (λ z → ((λ d → h (p (inl d))) , z))
               (unconvert-mapArgs cs h (s , (λ z → p (inr z))))

        {-
            Lift convertIH along the polynomial view: turn per-constructor
            IH on `Args` into IH on the W-type (single sum function
            on positions).
        -}
        convertIH : (cs : ConstrArity {ℓ}) {C : Type ℓ} {motive : C → Type ℓ}
                    (args : Args cs C) →
                    IHs cs motive args →
                    (z : recPos cs (fst (convert cs args))) →
                    motive (snd (convert cs args) z)
        convertIH Done         _          _                  ()
        convertIH (Nonrec A k) (a , args) ih                 z       = convertIH (k a) args ih z
        convertIH (Rec D cs)   (r , args) (ih_h , ih_t) (inl d)      = ih_h d
        convertIH (Rec D cs)   (r , args) (ih_h , ih_t) (inr z)      = convertIH cs args ih_t z

        {-
            Triangle identity / half-adjoint coherence: the path produced by
            `unconvert-convert` at `unconvert cs sp` agrees with the image of
            `convert-unconvert cs sp` under `unconvert cs`.

            Proved by structural induction on `cs`. With the `β-emb` refactor
            above, `convert (Rec D cs) ∘ unconvert (Rec D cs)` lands in
            β-emb-image definitionally, so the `Rec` case's path through
            `convert-unconvert (Rec D cs)` has only two segments — β-step
            and γ-path — and the chain to `LHS` factors through the same
            composition (via function-η and Σ-η on the inner projections).
            The remaining work is `ap U γ-path ≡ refl`, proved below.
        -}
        triangle : {C : Type ℓ} (cs : ConstrArity {ℓ})
                   (sp : Σ (Args cs (⊤ {ℓ})) (λ s → recPos cs s → C)) →
                   unconvert-convert cs (unconvert cs sp)
                   ≡ ap (unconvert cs) (convert-unconvert cs sp)
        triangle Done         (tt , p)      = ! (ap-const (Σ-≡-intro refl (ext (λ ()))))
        triangle (Nonrec A k) ((a , s) , p) =
            ap (ap (λ z → (a , z))) (triangle (k a) (s , p))
            • ! (ap-∘ (convert-unconvert (k a) (s , p)))
            • ap-∘ (convert-unconvert (k a) (s , p))
        triangle {C} (Rec D cs)   ((shape0 , s) , p) =
              ap (ap (λ z → ((λ d → p (inl d)) , z)))
                 (triangle cs (s , λ z → p (inr z)))
            • ! (ap-∘ (convert-unconvert cs (s , λ z → p (inr z))))
            • ap-∘ {f = unconvert (Rec D cs)} {g = β-emb D cs (λ d → p (inl d))}
                   (convert-unconvert cs (s , λ z → p (inr z)))
            • ! •unitr
            • ap (ap (unconvert (Rec D cs)) β-step •_) (! ap-γ-refl)
            • ! (ap-• (unconvert (Rec D cs)) β-step γ-path)
          where
            β-step : β-emb D cs (λ d → p (inl d))
                       (convert cs (unconvert cs (s , λ z → p (inr z))))
                   ≡ β-emb D cs (λ d → p (inl d)) (s , λ z → p (inr z))
            β-step = ap (β-emb D cs (λ d → p (inl d)))
                        (convert-unconvert cs (s , λ z → p (inr z)))

            γ-path : β-emb D cs (λ d → p (inl d)) (s , λ z → p (inr z))
                   ≡ (((λ _ → tt) , s) , p)
            γ-path = γ-fix D cs s p

            {- Decomposition: ap-on-precomp-inl is pwr-on-inl ext → refl. -}
            ap-precomp-inl-refl :
                ap (λ v → λ d → v (inl d)) (ext (pwr-of cs p)) ≡ refl
            ap-precomp-inl-refl =
                precomp-ext inl (pwr-of cs p)
              • ! funext-refl

            ap-snd-side-refl :
                ap (λ v → unconvert cs (s , λ z → v (inr z))) (ext (pwr-of cs p))
                ≡ refl
            ap-snd-side-refl =
                ap-∘ (ext (pwr-of cs p))
              • ap (ap (unconvert cs))
                   ( ap-∘ (ext (pwr-of cs p))
                   • ap (ap (λ q → (s , q)))
                        ( precomp-ext inr (pwr-of cs p)
                        • ! funext-refl))

            {- J-style collapse for non-dependent Σ (product): when both
               components are propositionally refl, the Σ-≡-intro is refl. -}
            collapse-Σ-product : {A : Type ℓ} {B : Type ℓ}
                                 {a : A} {b : B}
                                 {x : a ≡ a} {y : b ≡ b}
                                 (q1 : x ≡ refl) (q2 : y ≡ refl) →
                                 Σ-≡-intro {B = λ _ → B} x (tptConst x b • y) ≡ refl
            collapse-Σ-product refl refl = refl

            ap-γ-refl : ap (unconvert (Rec D cs)) γ-path ≡ refl
            ap-γ-refl =
                ap (ap (unconvert (Rec D cs))) (Σ-≡-intro-refl (ext (pwr-of cs p)))
              • ! (ap-∘ {f = unconvert (Rec D cs)}
                        {g = λ v → (((λ _ → tt) , s) , v)} (ext (pwr-of cs p)))
              • ap-Σ-const (λ v → λ d → v (inl d))
                           (λ v → unconvert cs (s , λ z → v (inr z)))
                           (ext (pwr-of cs p))
              • collapse-Σ-product ap-precomp-inl-refl ap-snd-side-refl

        {-
            Applying an elim then converting the IH agrees with first converting
            (which packages rec slots as a sum) and then applying the elim
            pointwise at each position.
        -}
        convertIH-applyElim :
            (cs : ConstrArity {ℓ}) {C : Type ℓ} {motive : C → Type ℓ}
            (args : Args cs C) (elim : (x : C) → motive x) →
            (z : recPos cs (fst (convert cs args))) →
            convertIH cs args (mkIHs cs elim args) z
            ≡ elim (snd (convert cs args) z)
        convertIH-applyElim Done         _          _    ()
        convertIH-applyElim (Nonrec A k) (a , args) elim z       =
            convertIH-applyElim (k a) args elim z
        convertIH-applyElim (Rec D cs)   (r , args) elim (inl d) = refl
        convertIH-applyElim (Rec D cs)   (r , args) elim (inr z) =
            convertIH-applyElim cs args elim z

        {-
            Lemma 3.10: the polynomial read off the signature.
            Lift the per-constructor split to a signature-wide W-type encoding:
            A bundles a constructor label with its shape, and B reads off
            the positions.
        -}
        A : Type ℓ
        A = Σ Op (λ c → Args (arity c) (⊤ {ℓ}))

        B : A → Type ℓ
        B (c , s) = recPos (arity c) s

        wtypeSignature : Signature
        wtypeSignature = WTypeSignature A B

        {-
            Convert per-constructor arguments to W-type arguments. This is
            just a repackaging via `convert`.
        -}
        convertArgs : (c : Op) → (Ty : Type ℓ) → Args (arity c) Ty → Args (Signature.arity wtypeSignature tt) Ty
        convertArgs c Ty args =
            let (s , p) = convert (arity c) args in ((c , s) , p , tt)

        module _ {C : Type ℓ} (indAlg : IndAlg sig C) where
            open IndAlg indAlg

            {-
                The W-type constructor: read off shape and positions, rebuild
                the original args via `unconvert`, then call the original
                constructor.
            -}
            wtypeConstr : ⊤ {ℓ} → Args (Signature.arity wtypeSignature tt) C → C
            wtypeConstr _ ((c , s) , p , tt) = algebra c (unconvert (arity c) (s , p))

            {-
                Translate W-type minor premises back to original minor premises.
            -}
            origMPOfWtypeMP : (motive : C → Type ℓ) →
                Cases wtypeSignature C wtypeConstr motive →
                Cases sig C algebra motive
            origMPOfWtypeMP motive wmp c args ih =
                tpt (λ z → motive (algebra c z)) (unconvert-convert (arity c) args)
                    (wmp tt ((c , fst (convert (arity c) args))
                            , snd (convert (arity c) args)
                            , tt)
                         (convertIH (arity c) args ih , tt))

            wtypeInd : (motive : C → Type ℓ) →
                       Cases wtypeSignature C wtypeConstr motive →
                       (a : C) → motive a
            wtypeInd motive wmp = ind motive (origMPOfWtypeMP motive wmp)

            {-
                Beta for the W-type version. We use the original signature's beta
                and propagate it through the convert/unconvert isomorphism.
            -}
            wtypeBeta : BetaLaw wtypeSignature wtypeInd
            wtypeBeta motive wmp tt ((c , s) , p , tt) =
                let sp' = convert (arity c) (unconvert (arity c) (s , p))
                    target = wmp tt ((c , fst sp') , snd sp' , tt)
                                  ((λ z → wtypeInd motive wmp (snd sp' z)) , tt)
                in
                beta motive (origMPOfWtypeMP motive wmp) c (unconvert (arity c) (s , p))
                -- Step 1: align the IH using `convertIH-applyElim` + funext.
                • ap (tpt (λ z → motive (algebra c z))
                          (unconvert-convert (arity c) (unconvert (arity c) (s , p))))
                     (ap (wmp tt ((c , fst sp') , snd sp' , tt))
                         (Σ-≡-intro (ext (convertIH-applyElim (arity c)
                                                              (unconvert (arity c) (s , p))
                                                              (wtypeInd motive wmp)))
                                    refl))
                -- Step 2: replace `unconvert-convert _ (unconvert _ _)` with
                -- `ap (unconvert _) (convert-unconvert _ _)` via the triangle.
                • ap (λ q → tpt (λ z → motive (algebra c z)) q target)
                     (triangle (arity c) (s , p))
                -- Step 3: J-collapse the transport over `convert-unconvert _ _`.
                • tpt-along-q (convert-unconvert (arity c) (s , p))
              where
                {-
                    Key step. Given any path `q : sp' ≡ sp` between
                    `Σ (Shape (arity c)) (Pos (arity c) → C)`-pairs, J-induction
                    collapses the transport along `ap unconvert q` to identity.
                -}
                tpt-along-q :
                  {sp sp' : Σ (Args (arity c) (⊤ {ℓ}))
                              (λ s → recPos (arity c) s → C)}
                  (q : sp' ≡ sp) →
                  tpt (motive ∘ algebra c) (ap (unconvert (arity c)) q)
                      (wmp tt ((c , fst sp') , snd sp' , tt)
                           ((λ z → wtypeInd motive wmp (snd sp' z)) , tt))
                  ≡ wmp tt ((c , fst sp) , snd sp , tt)
                        ((λ z → wtypeInd motive wmp (snd sp z)) , tt)
                tpt-along-q refl = refl

            indAlgWtype : WTypeIndAlg A B C
            indAlgWtype .IndAlg.algebra = wtypeConstr
            indAlgWtype .IndAlg.ind = wtypeInd
            indAlgWtype .IndAlg.beta = wtypeBeta

            allIndAlgWTypeIndAlg : Σ (Type ℓ) (λ A → Σ (A → Type ℓ)
                (λ B → WTypeIndAlg A B C))
            allIndAlgWTypeIndAlg = (A , B , indAlgWtype)

        {-
            Fidelity of the embedding, fold level: the fold of the
            W-type inductive algebras agrees pointwise with the fold
            of the original ones.
        -}
        module _ {C D : Type ℓ} (iC : IndAlg sig C) (iD : IndAlg sig D) where
            foldW : C → D
            foldW = IndAlg.fold (indAlgWtype iC) (wtypeConstr iD)

            {-
                `foldW` is an algebra homomorphism for the *original*
                constructor algebras: unfold one constructor via the
                W-type β-rule, then push the mapping through
                `unconvert`'s naturality.
            -}
            wtypeFold-hom : (c : Op) (args : Args (arity c) C) →
                foldW (IndAlg.algebra iC c args)
                  ≡ IndAlg.algebra iD c (mapArgs (arity c) foldW args)
            wtypeFold-hom c args =
                  ap (foldW ∘ IndAlg.algebra iC c) (! (unconvert-convert (arity c) args))
                • IndAlg.fold-β (indAlgWtype iC) (wtypeConstr iD) tt
                      ((c , fst sp) , snd sp , tt)
                • ap (IndAlg.algebra iD c) (unconvert-mapArgs (arity c) foldW sp)
                • ap (IndAlg.algebra iD c ∘ mapArgs (arity c) foldW)
                     (unconvert-convert (arity c) args)
              where
                sp = convert (arity c) args

            {-
                Hence `foldW` agrees with the original fold: both are
                algebra homomorphisms out of the same h-initial
                algebra, and folds are unique (`fold-unique`).
            -}
            wtypeFoldAgree : (x : C) →
                foldW x ≡ IndAlg.fold iC (IndAlg.algebra iD) x
            wtypeFoldAgree = fold-unique iC (IndAlg.algebra iD) foldW wtypeFold-hom

        module _ {C D : Type ℓ} (config : Config sig C D) where
            open Config config

            configWTypeConfig : WTypeConfig A B C D
            configWTypeConfig = record
                { indAlgC = indAlgWtype indAlgC
                ; indAlgD = indAlgWtype indAlgD }

            -- Lemma 3.10 (Configurations Faithfully Embed into W-type
            -- Configurations): the embedding, with the polynomial (A , B).
            allConfigWTypeConfig : Σ (Type ℓ) (λ A → Σ (A → Type ℓ) (λ B → WTypeConfig A B C D))
            allConfigWTypeConfig = (A , B , configWTypeConfig)

            {-
                Lemma 3.10 (faithfulness)
                Fidelity of the embedding, repair level: the embedding
                does not change the repair equivalence. The forward and
                backward maps of `configToEquiv` for the W-type
                configuration equal those of the original
                configuration — `wtypeFoldAgree` on each side, lifted
                to a map equality by funext.
            -}
            wtypeConfigEquivAgree-f :
                _≃_.f (snd (configToEquiv configWTypeConfig))
                  ≡ _≃_.f (snd (configToEquiv config))
            wtypeConfigEquivAgree-f = ext (wtypeFoldAgree indAlgC indAlgD)

            wtypeConfigEquivAgree-g :
                _≃_.g (snd (configToEquiv configWTypeConfig))
                  ≡ _≃_.g (snd (configToEquiv config))
            wtypeConfigEquivAgree-g = ext (wtypeFoldAgree indAlgD indAlgC)
