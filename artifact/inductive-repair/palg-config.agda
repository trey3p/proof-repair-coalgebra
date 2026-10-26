{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import palg
open import inductive-repair.indspec
open import inductive-repair.config
open import inductive-repair.wtype-config
{-
    Algebra configurations: a pair of initial P-algebras for one
    polynomial. `indAlgToInit` upgrades a `WTypeIndAlg` to a full
    `InitAlgOn` (the uniqueness 2-cell `indHomPathUnq` is the hard
    part); `initToHalf` goes the other way; and
    `algConfigToAlgEquiv` shows an `AlgConfig` yields an algebra
    equivalence.
-}
module inductive-repair.palg-config  {l : Level} (A : Type l) (B : A → Type l) where

  {-
    Definition 3.13 (Algebra Configuration)
    An `AlgConfig C D` is an initial P-algebra on `C`
    and an initial P-algebra on `D`.
  -}
  record AlgConfig (C : Type l) (D : Type l) : Type (lsuc l) where
    field
      initAlgC : InitAlgOn A B C
      initAlgD : InitAlgOn A B D

  {-
    In this module, we assume that we have a `WTypeIndAlg` on `C`
    and from that create a initial P-algebra on `C`.
  -}
  module indAlgToInit {C : Type l} (indAlg : WTypeIndAlg {l} A B C) where
    open IndAlg indAlg

    sup : P A B C → C
    sup = λ (a , t) → algebra tt (a , t , tt)

    {-
      The minor premises needed to construct the initial map from `C` to `Ycar`
    -}
    mpα : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → Cases (WTypeSignature {l} A B) C algebra (λ _ → Ycar)
    mpα Ycar Ysup = λ c argsFunc ihArgsFunc → Ysup (fst argsFunc , fst ihArgsFunc)

    {-
      The initial map from `C → Ycar`.
    -}
    ind-hom : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → (c : C) → Ycar
    ind-hom Ycar Ysup = (ind (λ _ → Ycar) (mpα Ycar Ysup))

    {-
      Pointwise, `ind-hom` is actually a P-algebra morphism
      between `(C , sup)` and `(Ycar , Ysup)`.
    -}
    indIsHomPw : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → (x : P A B C) →
                (ind-hom Ycar Ysup ∘ sup) x ≡ (Ysup ∘ P-map (ind-hom Ycar Ysup)) x
    indIsHomPw Ycar Ysup x = beta (λ v → Ycar) (mpα Ycar Ysup) tt (fst x , snd x , tt)

    {-
      `ind-hom` is actually a P-algebra morphism
      between `(C , sup)` and `(Ycar , Ysup)`.
    -}
    indIsHom : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) →
                (ind-hom Ycar Ysup ∘ sup) ≡ (Ysup ∘ P-map (ind-hom Ycar Ysup))
    indIsHom Ycar Ysup = ext (indIsHomPw Ycar Ysup)

    {-
      The minor premises required to show the motive that
      every P-algebra morphism between `(C , sup)` and `(Ycar, Ysup)`
      is equal to `ind-hom` pointwise.
    -}
    indIsUnqMp : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → ((h , p) : AlgHom (C , sup) (Ycar , Ysup)) →
      Cases (WTypeSignature {l} A B) C algebra (λ y → h y ≡ ind-hom Ycar Ysup y)
    indIsUnqMp Ycar Ysup (h , p) = (λ c argsFunc@(args , (rec , tt)) (ihArgsFunc , tt) →
          happly p (args , rec) -- h (constrC argsFunc) = Ysup ∘ P(h) (args, rec)
          • ap Ysup (Σ-≡-intro refl (ext ihArgsFunc)) -- = Ysup (args , ihArgs)
          • ! (indIsHomPw Ycar Ysup (args , rec)) -- = indC argsFunc
        )

    {-
      The motive stating that every P-algebra morphism between
      `(C , sup)` and `(Ycar , Ysup)` is equal to `ind-hom` pointwise.
    -}
    indIsUnqMotive : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → (h : C → Ycar) → (y : C) → Type l
    indIsUnqMotive Ycar Ysup h = (λ y → h y ≡ ind-hom Ycar Ysup y)

    {-
      Every P-algebra morphism is equal between
      `(C , sup)` and `(Ycar , Ysup)` is equal to `ind-hom` pointwise.
    -}
    indIsUnqHomPw : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → ((h , p) : AlgHom (C , sup) (Ycar , Ysup)) →
      (x : C) → h x ≡ ind-hom Ycar Ysup x
    indIsUnqHomPw (Ycar) (Ysup) hom@(h , p) =
      (λ x → ind (indIsUnqMotive Ycar Ysup h) (indIsUnqMp Ycar Ysup hom) x)

    {-
      Every P-algebra morphism is equal between
      `(C , sup)` and `(Ycar , Ysup)` is equal to `ind-hom`.
    -}
    indIsUnqHom : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → ((h , p) :
      AlgHom (C , sup) (Ycar , Ysup)) → h ≡ ind-hom Ycar Ysup
    indIsUnqHom Ycar Ysup hom = ext (indIsUnqHomPw Ycar Ysup hom)

    {-
      Show that the proof that `h` is an algebra morphism,
      transported along the proof that `h = indC-hom`,
      is equal to the proof that `indC-hom` is an algebra morphism.
    -}
    indHomPathUnq :  (Ycar : Type l) (Ysup : P A B Ycar → Ycar) → ((h , p) : AlgHom (C , sup) (Ycar , Ysup)) →
      (tpt (λ f → isAlgHom (C , sup) (Ycar , Ysup) f) (indIsUnqHom Ycar Ysup ((h , p))) p) ≡ indIsHom Ycar Ysup
    indHomPathUnq Ycar Ysup hom@(h , p) =
      -- Replace the transport with two `ap`s
      tpt-path (λ f → f ∘ sup) (λ f → Ysup ∘ P-map f) (indIsUnqHom Ycar Ysup (h , p)) p
      -- Switch to showing everything pointwise
      • happly-inj (ext λ (x : P A B C) →
        let leftPath = ! (ap (λ f → f ∘ sup) (indIsUnqHom Ycar Ysup (h , p)))
            rightPath = ap (λ f → Ysup ∘ P-map f) (indIsUnqHom Ycar Ysup (h , p))
            ihArgsFunc = mkIHs
                  (WTypeArity {l} A B tt) (ind (indIsUnqMotive Ycar Ysup h)
                    (indIsUnqMp Ycar Ysup (h , p)))
                  (fst x , snd x , tt {l})
        in
        -- Distribute `happly` over all three paths
        happly-• leftPath (p • rightPath) x
        • ap (λ z → happly leftPath x • z) ((happly-• p rightPath) x)
        -- Push `happly` through everything in `leftPath` and then apply beta
        • ap (λ q → q • happly p x • happly rightPath x) (
          -- Push `happly` through the `!`
          happly-! (ap (λ f → f ∘ sup) (indIsUnqHom Ycar Ysup (h , p))) x
          • ap ! (
            -- Push `happly` through the `ap`
            happly-precomp {l} {l} (indIsUnqHom Ycar Ysup (h , p)) sup x
            -- Cancel the `happly` with the `ext` inside of `inIsUnqHom`
            • happlyExt (indIsUnqHomPw Ycar Ysup hom) (sup x)
            • beta (indIsUnqMotive Ycar Ysup h) (indIsUnqMp Ycar Ysup hom) tt (fst x , (snd x , tt))
          )
          • -- Distribute `!` across the paths
            !-comp (happly p x) (ap Ysup (Σ-≡-intro refl (ext (fst ihArgsFunc)))
              • ! (indIsHomPw Ycar Ysup x))
            • ap (λ z → z • ! (happly p x))
              (!-comp (ap Ysup (Σ-≡-intro refl (ext (fst ihArgsFunc)))) (! (indIsHomPw Ycar Ysup x)))
        )
        -- Reassociate to get `! (happly p x) closer to `happly p x`
        • •assoc {p = (! (! (indIsHomPw Ycar Ysup x))
                • ! (ap Ysup (Σ-≡-intro refl (ext (fst ihArgsFunc)))))}
              {q = ! (happly p x)} {r = happly p x • happly rightPath x}
        -- Associate and cancel out the two `happly p x`
        • ap (λ z → (! (! (indIsHomPw Ycar Ysup x))
                • ! (ap Ysup (Σ-≡-intro refl (ext (fst ihArgsFunc))))) • z)
            (! (•assoc {p = ! (happly p x)} {q = happly p x} {r = happly rightPath x})
              • ap (λ z → z • happly rightPath x) •invl
              • •unitl)
        -- Push `happly` through the right hand side and kill it
        • ap (λ z → (! (! (indIsHomPw Ycar Ysup x)) • ! (ap Ysup
              (Σ-≡-intro refl (ext (fst ihArgsFunc))))) • z)
            ( happly-ap-double-∘ {f = Ysup} {g = P-map} (ext (indIsUnqHomPw Ycar Ysup (h , p))) x)
        -- Replace the usage of `ihArgsFunc` with `indIsUnqHomPw`
        • ! (ap (λ p → (! (! (indIsHomPw Ycar Ysup _))
                  • ! (ap Ysup (Σ-≡-intro refl (ext (fst ihArgsFunc))))) • p)
            (ap (ap Ysup) (P-resp-is-ap-P-map (indIsUnqHomPw Ycar Ysup hom) x)))
        -- Reassociate and canel out two uses of `Ysup` with `indIsUnqHomPw`
        • •assoc • ap (λ p → (! (! (indIsHomPw Ycar Ysup _)) • p)) •invl • •unitr 
        -- Cancel out the double `!` and clear out the remaining difference with `happlyExt`
        • !! (indIsHomPw Ycar Ysup _) •  ! (happlyExt (indIsHomPw Ycar Ysup) _)
        )

    {-
      From a `WTypeIndAlg A B C`, we can create
      an initial P-algebra structure on `C`.
    -}
    {- The central element of the initiality proof: the inductive
       hom `(C, sup) → (Ycar, Ysup)`. Kept *transparent* so that
       `wIsInit Y .fst` (= `wIsInit-center`) reduces in downstream
       types — crucial for stating the `.snd` lemma cleanly. -}
    wIsInit-center : (Ycar : Type l) (Ysup : P A B Ycar → Ycar) →
                     AlgHom (C , sup) (Ycar , Ysup)
    wIsInit-center Ycar Ysup =
      ((λ x → ind-hom Ycar Ysup x) , indIsHom Ycar Ysup)

    {- The uniqueness proof is sealed in an `abstract` block so that
       downstream consumers (e.g. `isProp-isInitAlg`-based round-trip
       lemmas) do not force Agda to normalise the full
       `indHomPathUnq` term during type-checking — that
       normalisation blows up combinatorially. `wIsInit-snd-eq`
       exposes the computation rule of `wIsInit-uniq` as a named
       path, propagating opaquely outside the block. This lets
       `bridgeη-beta` reduce specific occurrences of `wIsInit-uniq`
       (which the reconstructed `initAlgToIndAlg.beta` depends on
       via `compMapEqId`) without re-triggering the blowup. -}
    abstract
      wIsInit-uniq : (Ycar : Type l) (Ysup : P A B Ycar → Ycar)
                     (hom : AlgHom (C , sup) (Ycar , Ysup)) →
                     hom ≡ wIsInit-center Ycar Ysup
      wIsInit-uniq Ycar Ysup (h , p) =
        Σ-≡-intro (indIsUnqHom Ycar Ysup (h , p))
                  (indHomPathUnq Ycar Ysup (h , p))

      wIsInit-snd-eq : (Ycar : Type l) (Ysup : P A B Ycar → Ycar)
                       (h : C → Ycar) (p : isAlgHom (C , sup) (Ycar , Ysup) h) →
                       wIsInit-uniq Ycar Ysup (h , p)
                         ≡ Σ-≡-intro (indIsUnqHom Ycar Ysup (h , p))
                                      (indHomPathUnq Ycar Ysup (h , p))
      wIsInit-snd-eq Ycar Ysup h p = refl

    wIsInit : isInitAlg (C , sup)
    wIsInit (Ycar , Ysup) .fst = wIsInit-center Ycar Ysup
    wIsInit (Ycar , Ysup) .snd hom = wIsInit-uniq Ycar Ysup hom

    wIndAlgToInit : InitAlgOn A B C
    wIndAlgToInit .InitAlgOn.sup    = sup
    wIndAlgToInit .InitAlgOn.isInit = wIsInit

  {-
    Every `WTypeConfig A B C D` can be turned into an `AlgConfig A B C D`.
  -}
  wToAlg : {C D : Type l} → WTypeConfig {l} A B C D → AlgConfig C D
  wToAlg config .AlgConfig.initAlgC = indAlgToInit.wIndAlgToInit (config .Config.indAlgC)
  wToAlg config .AlgConfig.initAlgD = indAlgToInit.wIndAlgToInit (config .Config.indAlgD)

  {-
    Strengthened soundness: the maps underlying an `AlgConfig`
    form an *algebra equivalence* (`palg.AlgEquiv`), not merely
    a type equivalence. This is the algebraic upgrade of
    `configToEquiv`: a configuration yields an algebra
    isomorphism — an equivalence whose maps are genuine
    P-algebra homomorphisms.

    The forward and backward maps are the unique homomorphisms
    between the two initial algebras (each from the other side's
    initiality). Both round-trips are the identity by
    `homEqInitId` — every endomorphism of an initial algebra is
    the identity. Projecting the underlying carrier maps
    recovers the bare type equivalence of `configToEquiv`.
  -}
  algConfigToAlgEquiv : {C D : Type l} (cfg : AlgConfig C D) →
                     AlgEquiv (C , InitAlgOn.sup (AlgConfig.initAlgC cfg))
                              (D , InitAlgOn.sup (AlgConfig.initAlgD cfg))
  algConfigToAlgEquiv {C} {D} cfg =
      fwd , ((bwd , left) , (bwd , right))
    where
      open AlgConfig cfg
      palgC : P-Alg {ℓ₃ = l} A B
      palgC = (C , InitAlgOn.sup initAlgC)
      palgD : P-Alg {ℓ₃ = l} A B
      palgD = (D , InitAlgOn.sup initAlgD)
      isInitC = InitAlgOn.isInit initAlgC
      isInitD = InitAlgOn.isInit initAlgD

      {- The unique homomorphism each way, from the opposite
         side's initiality. -}
      fwd : AlgHom palgC palgD
      fwd = isInitC palgD .fst
      bwd : AlgHom palgD palgC
      bwd = isInitD palgC .fst

      {- Both round-trips are endomorphisms of an initial
         algebra, hence the identity. -}
      left : AlgHom-∘ palgC palgD palgC fwd bwd ≡ id-hom palgC
      left = homEqInitId palgC isInitC (AlgHom-∘ palgC palgD palgC fwd bwd)
      right : AlgHom-∘ palgD palgC palgD bwd fwd ≡ id-hom palgD
      right = homEqInitId palgD isInitD (AlgHom-∘ palgD palgC palgD bwd fwd)

  {-
      Proposition 3.15 (Repair by Instantiation)
      Repair by instantiation, at the fold level: for any target
      algebra `Y`, the fold out of `C` is the fold out of `D`
      pre-composed with the repair map `φ`. Both sides are
      homomorphisms `(C, supC) → Y`, and the hom-space out of an
      initial algebra is contractible, so they agree. A program
      written against the universal property is repaired by
      swapping which initial algebra it is instantiated at.
  -}
  foldSwap : {C D : Type l} (cfg : AlgConfig C D) (Y : P-Alg {ℓ₃ = l} A B) →
             let foldC = fst (fst (InitAlgOn.isInit (AlgConfig.initAlgC cfg) Y))
                 foldD = fst (fst (InitAlgOn.isInit (AlgConfig.initAlgD cfg) Y))
                 φ     = fst (fst (algConfigToAlgEquiv cfg))
             in  foldC ≡ foldD ∘ φ
  foldSwap {C} {D} cfg Y =
      ! (ap fst (isInitC Y .snd foldD∘φ))
    where
      open AlgConfig cfg
      palgC = (C , InitAlgOn.sup initAlgC)
      palgD = (D , InitAlgOn.sup initAlgD)
      isInitC = InitAlgOn.isInit initAlgC
      isInitD = InitAlgOn.isInit initAlgD
      {- The right-hand side, as a homomorphism `(C, supC) → Y`. -}
      foldD∘φ : AlgHom palgC Y
      foldD∘φ = AlgHom-∘ palgC palgD Y (fst (algConfigToAlgEquiv cfg))
                                       (fst (isInitD Y))


  module initToHalf {C : Type l} (initAlg : InitAlgOn A B C) where
    open InitAlgOn initAlg

    algebra : ConstrAlgebra (WTypeSignature {l} A B) C
    algebra c (nonrec , rec , tt) = sup (nonrec , rec)

    module ind (motive : C → Type l) (mp : Cases (WTypeSignature {l} A B) C algebra motive) where
      {- The minor premises give a fibered P-algebra
        structured. We define its associated P-algebra. 
      -}
      assocAlg : P-Alg A B
      -- We define the carrier of the P-algebra to be the pair `(c : C) × motive c`
      assocAlg .fst = Σ C (λ c → motive c)
      -- We now construct a term of type `(c : C) × motive c` given arguments
      assocAlg .snd args .fst = sup (P-map (λ z → fst z) args)
      assocAlg .snd (nonrec , rec) .snd = mp tt (nonrec , (fst ∘ rec , tt))
        ((λ x → snd (rec x)) , tt)

      -- We get the unique map from `(C , sup)` to `assocAlg`
      initMap : AlgHom (C , sup) assocAlg
      initMap = isInit assocAlg .fst

      {-
        The map project out the first component of the 
        associated P-algebra is a P-algebra morphism.
      -}
      projMap : AlgHom assocAlg (C , sup)
      projMap .fst = fst
      projMap .snd = refl

      compMap : AlgHom (C , sup) (C , sup)
      compMap = AlgHom-∘ (C , sup) assocAlg (C , sup) initMap projMap

      compMapEqId : compMap ≡ id-hom (C , sup)
      compMapEqId = homEqInitId (C , sup) isInit compMap

      {-
        The initial map from `(C , sup)` to
        the associated P-algebra is a section of the projection map.
      -}
      initMapSection : (x : C) → (fst initMap) x .fst ≡ x
      initMapSection = happly (ap fst compMapEqId)

    {- The `ind` and `beta` fields of `initAlgToIndAlg` are sealed
       behind `abstract` wrappers (same purpose as the `wIsInit-uniq`
       seal above; the bodies stay transparent `private` definitions
       because a where-clause inside `abstract` cannot state its own
       local types). Without the seal, any conversion check between
       two `WTypeIndAlg`-valued terms eta-expands the record and the
       copattern projections reduce into these large proof bodies —
       comparing them pointwise (worse still, against metavariables)
       is the blowup that made `config-alg-equiv` intractable. Sealed,
       the projections stay neutral and record comparisons reduce to
       cheap argument comparisons. `algebra` stays transparent: the
       carrier bridge recovers `sup` definitionally through it. -}
    private
      ind-body : Induction (WTypeSignature {l} A B) algebra
      ind-body motive mp a =
        tpt (λ z → motive z) (initMapSection a) (snd ((fst initMap) a))
        where open ind motive mp

      beta-body : BetaLaw (WTypeSignature {l} A B) ind-body
      beta-body motive mp tt (a , t) =
        ap (λ q → tpt (λ z → motive z) q (snd (initMapFn (sup args)))) (! compMap_eq_initMapSection)
        • tpt-• motive (ap (λ r → fst r) (initMapPathArgs args))  (ap (sup ∘ (λ x → a , (λ z → x (t .fst z)))) compMapEqIdFn) (snd (initMapFn (sup args)))
        • ap (λ z → tpt motive (ap (sup ∘ (λ x → a , (λ z → x (t .fst z)))) compMapEqIdFn) z) (tpt-ap motive fst (initMapPathArgs args)  (snd (initMapFn (sup args))) • initMapToMP)
        • tpt-ap  motive (sup ∘ (λ x → a , (λ z → x (t .fst z)))) compMapEqIdFn (mp tt (a , ((λ r → fst r) ∘ (initMapFn ∘ t .fst)) , tt) ((λ x → (initMapFn ∘ t .fst) x .snd) , tt))
        • ap (λ q → tpt (λ g → motive (sup (a , g ∘ t .fst))) q
                (mp tt (a , ((λ r → fst r) ∘ (initMapFn ∘ t .fst) , tt))
                 ((λ x → (initMapFn ∘ t .fst) x .snd) , tt)))
             (! (Σ-≡-intro-fst compMapEqIdFn tpt_compMap_refl))
        • tpt-ap (λ g → motive (sup (a , g ∘ t .fst))) fst
            (Σ-≡-intro compMapEqIdFn tpt_compMap_refl)
            (mp tt (a , ((λ r → fst r) ∘ (initMapFn ∘ t .fst) , tt)) ((λ x → (initMapFn ∘ t .fst) x .snd) , tt))
        •  apd (λ p → motive (sup (a , fst p ∘ t .fst))) apd_abstraction (Σ-≡-intro compMapEqIdFn tpt_compMap_refl)
        where
        open ind motive mp
        -- Goal: ind motive mp (sup args) ≡ mp tt args (ind ∘ rec args).
        -- Unfold `ind` to a transport along `initMapSection`, push the
        -- homomorphism square `initMapPathArgs` through `apd`, and
        -- reconcile the two section paths (`compMap_eq_initMapSection`).

        supΣ = assocAlg .snd
        -- We get the underlying function from initMap.
        initMapFn : C → Σ C (motive)
        initMapFn = initMap .fst

        compMapEqIdFn = ap fst compMapEqId

        -- We get the proof that initMap is a homomorphism.
        -- The type of this is : `fst initMap ∘ sup ≡ snd assocAlg ∘ P-map (fst initMap)`
        initMapPath : isAlgHom (C , sup) assocAlg (initMap .fst)
        initMapPath = initMap .snd

        -- We get the current arguments from the argsFunc (a , t) and put them in the type of P A B C.
        args : P A B C
        args = (a , t .fst)

        -- We apply the initMapPath to the current arguments.
        initMapPathArgs : (args : P A B C) →  (initMapFn ∘ sup) args ≡ (supΣ ∘ P-map (initMapFn)) args
        initMapPathArgs args = happly initMapPath args

        initMapToMP : tpt (λ z → motive (z .fst)) (initMapPathArgs args) (snd ((fst initMap ∘ sup) args))
                      ≡ mp tt (a , ((fst ∘ (initMapFn ∘ t .fst) , tt))) ((λ x → (initMapFn ∘ t .fst) x . snd) , tt)
        initMapToMP = apd (λ z → motive (z .fst)) snd (initMapPathArgs args)

        -- apd_abstraction is defined over the total space of paths out of (fst ∘ initMapFn).
        -- For each (g , q) where q : fst ∘ initMapFn ≡ g, we use q pointwise
        -- to transport the IH snd (initMapFn (t.fst x)) to type motive (g (t.fst x)).
        apd_abstraction : (p : Σ (C → C) (λ g → fst ∘ initMapFn ≡ g)) → motive (sup (a , p .fst ∘ t .fst))
        apd_abstraction (g , q) = mp tt (a , (g ∘ t .fst , tt))
                        ((λ x → tpt motive (happly q (t .fst x)) (snd (initMapFn (t .fst x)))) , tt)

        -- tpt_compMap_refl witnesses that transporting refl along ap fst compMapEqId
        -- in the path-type fibration (λ g → fst ∘ initMapFn ≡ g) gives ap fst compMapEqId.
        -- Proved by J: at refl both sides are refl.
        tpt-right-path-refl : ∀ {A : Type l} {a b : A} (q : a ≡ b) → tpt (λ g → a ≡ g) q refl ≡ q
        tpt-right-path-refl refl = refl

        Σ-≡-intro-fst : ∀ {A : Type l} {B : A → Type l} {a a' : A} {b : B a} {b' : B a'}
          (p1 : a ≡ a') (p2 : tpt B p1 b ≡ b') → ap fst (Σ-≡-intro p1 p2) ≡ p1
        Σ-≡-intro-fst refl refl = refl

        tpt_compMap_refl : tpt (λ g → fst ∘ initMapFn ≡ g) compMapEqIdFn refl ≡ compMapEqIdFn
        tpt_compMap_refl = tpt-right-path-refl compMapEqIdFn

        compMap_eq_initMapSection : ap fst (initMapPathArgs args) • ap (sup ∘ λ x → a , λ z → x (t .fst z )) compMapEqIdFn ≡ initMapSection (sup args)
        compMap_eq_initMapSection = ap (λ z → z • ap (sup ∘ (λ x → a , (λ z → x (t .fst z)))) compMapEqIdFn) (
            ! (ap (λ z → happly ((ap (_∘_ (λ r → fst r)) (isInit assocAlg .fst .snd)) • z) args) •unitl
            • happly-• _ _ args
            • ap (λ z → z • happly (ap (_∘_ sup) (ext _)) args) (
              happly-ap-double-∘ {f = fst} {g = λ x → x} (initMap .snd) args
            )
            • ap (λ z → ap (λ r → fst r) (ap (λ z → z args) (initMap .snd)) • z) (
              happly-ap-double-∘ {f = sup} {g = λ x → x} (ext (λ v → refl)) args
              • ap (ap sup) (! (happly-ap (ext (λ v → refl)) args)
              • happlyExt (λ v → refl) args)
            )
            • •unitr
            • ap (λ z → ap (λ r → fst r) z) (! (happly-ap (isInit assocAlg .fst .snd) args)))
          )
          • ap (λ z → happly (compMap .snd) args • z) (
            ! (happly-ap-double-∘ {f = sup} {g = P-map ∘ fst} compMapEqId args
              • ! (ap-∘ {f = sup} {g = (λ z → (P-map ∘ (λ r → fst r)) z args)} compMapEqId) 
              • ap-∘ compMapEqId)
          )
          • ! (happly-• (compMap .snd) (ap (λ f → sup ∘ P-map (f .fst)) compMapEqId) args)
          • ap (λ z → happly z args)
          (!• (! (tpt-path (λ hom → fst hom ∘ sup) (λ hom → sup ∘ P-map (fst hom)) compMapEqId (compMap .snd))
          • apd (λ hom → isAlgHom (C , sup) (C , sup) (fst hom)) snd compMapEqId))
          • ap (λ q → happly q args) (ap-∘ compMapEqId)
          • happly-precomp {l} {l} (ap fst compMapEqId) sup args

    abstract
      initAlgToIndAlg-ind : Induction (WTypeSignature {l} A B) algebra
      initAlgToIndAlg-ind = ind-body

      initAlgToIndAlg-beta : BetaLaw (WTypeSignature {l} A B) initAlgToIndAlg-ind
      initAlgToIndAlg-beta = beta-body

    initAlgToIndAlg : WTypeIndAlg {l} A B C
    initAlgToIndAlg .IndAlg.algebra = algebra
    initAlgToIndAlg .IndAlg.ind = initAlgToIndAlg-ind
    initAlgToIndAlg .IndAlg.beta = initAlgToIndAlg-beta
