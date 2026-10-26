{-# OPTIONS --without-K --cubical-compatible  #-}

open import common
open import palg
open import inductive-repair.indspec
open import inductive-repair.config
open import inductive-repair.palg-config
open import inductive-repair.wtype-config hiding (A ; B)
open import inductive-repair.alg-iso
open import inductive-repair.bridge
open import inductive-repair.conversion

{-
   Theorem 3.11 (W-type Configurations are Unique Algebra Equivalences)
   proved as `wtypeConfigEqv` at the end of this module.

       WTypeConfig A B C D
         ≃
       Σ[ supC ] Σ[ supD ]
         (AlgEquiv (C , supC) (D , supD) × isInitAlg (C , supC))

   — a `Config` over the W-type signature is the same data as
   structure maps `supC`, `supD`, an algebra equivalence between
   them, and initiality of the source. Reduction chain: record η
   on `Config`, the carrier bridge of `inductive-repair.bridge`
   per side, record η on `AlgConfig`, and the algebra-level
   `fullAlgIso` below.
-}

module inductive-repair.config-alg-equiv where

   {-
        Definition 3.6 (remark): forgetting the homomorphism witnesses,
        an algebra equivalence is a type equivalence.
        The underlying type equivalence of a `palg` algebra
        equivalence: keep the carrier maps, derive the round-trips
        by projecting the bi-invertibility equations to the
        carrier (`ap fst`, then `happly`).
    -}
    algEquivToTypeEquiv : {l : Level} {A : Type l} {B : A → Type l}
                          {X Y : P-Alg {ℓ₃ = l} A B} →
                          AlgEquiv X Y → Carrier X ≃ Carrier Y
    algEquivToTypeEquiv (fwd , (ginv , ginv-eq) , (hinv , hinv-eq)) = record
      { f = fwd  .fst
      ; g = ginv .fst
      ; η = happly (ap fst ginv-eq)
      ; h = hinv .fst
      ; ε = happly (ap fst hinv-eq)
      }

    {-
        The `PAlgConfig` a `Config` converts to — named so it can
        appear in the type of `configToAlgIso` below.
    -}
    cfgPAlg : {l : Level} {C D : Type l} {sig : Signature {l}} →
              Config sig C D → PAlgConfig C D
    cfgPAlg {sig = sig} cfg = configToPalg (record { sig = sig ; config = cfg })

    {-
       The correspondence at the `Config sig C D` level: a
       configuration is exactly an algebra isomorphism together
       with initiality of the source (structure maps determined
       by the config). The two underlying maps follow.
    -}

    {-
        Forward (upgrade of `configToEquiv`): convert to
        P-algebras, then read off the algebra equivalence and the
        source's initiality.
    -}
    configToAlgIso :
        {l : Level} {C D : Type l} {sig : Signature {l}} (cfg : Config sig C D) →
        AlgEquiv (C , InitAlgOn.sup (AlgConfig.initAlgC (PAlgConfig.algConfig (cfgPAlg cfg))))
                 (D , InitAlgOn.sup (AlgConfig.initAlgD (PAlgConfig.algConfig (cfgPAlg cfg))))
          × isInitAlg (C , InitAlgOn.sup (AlgConfig.initAlgC (PAlgConfig.algConfig (cfgPAlg cfg))))
    configToAlgIso cfg =
        algConfigToAlgEquiv A B algConfig , InitAlgOn.isInit (AlgConfig.initAlgC algConfig)
      where open PAlgConfig (cfgPAlg cfg)

    {-
        Reverse (upgrade of `equivToConfig`): the source's
        initiality gives an `IndAlg` on `C` via
        `initToHalf.initAlgToIndAlg`, and `equivToConfig`
        transfers it to `D` along the carrier equivalence.
    -}
    algIsoToConfig :
        {l : Level} {C D : Type l} {A : Type l} {B : A → Type l}
        {supC : P A B C → C} {supD : P A B D → D} →
        AlgEquiv (C , supC) (D , supD) × isInitAlg (C , supC) →
        Config (WTypeSignature {l} A B) C D
    algIsoToConfig {C = C} {A = A} {B} {supC} (e , isInitC) =
        equivToConfig (initToHalf.initAlgToIndAlg A B initC) (algEquivToTypeEquiv e)
      where
        initC : InitAlgOn A B C
        initC = record { sup = supC ; isInit = isInitC }

    {-
       The algebra-level equivalence

            AlgConfig A B C D  ≃  Σ supC Σ supD
                                    (AlgEquiv (C,supC) (D,supD)
                                       × isInitAlg (C,supC))

       An `AlgConfig` is *exactly* a pair of structure maps
       together with an algebra isomorphism between them and
       initiality of the source — the structure maps are data, not
       existentials. Both round-trips are immediate because
       `isInitAlg` is a proposition (`isProp-isInitAlg`) and
       `AlgEquiv` out of an initial source is a proposition
       (`isProp-AlgEquiv`). The two maps reuse `algConfigToAlgEquiv`
       (forward) and `initTransfer` (which manufactures the target's
       initiality from the isomorphism).
    -}

    AlgInitEquiv : {l : Level} (A : Type l) (B : A → Type l) (C D : Type l) →
                 Type (lsuc l)
    AlgInitEquiv A B C D =
      Σ (P A B C → C) λ supC →
      Σ (P A B D → D) λ supD →
      AlgEquiv (C , supC) (D , supD) × isInitAlg (C , supC)

    {- The four components of `fullAlgIso` are pulled out as
       top-level definitions in a private parameterised module so
       the round-trip proofs `fai-to-from` / `fai-from-to` can sit
       inside an `abstract` block. Same shape as the
       `wIsInit-uniq` seal in `palg-config`: the *types* of the
       round-trips stay literal (`fai-from (fai-to cfg) ≡ cfg` etc.),
       but their bodies — which expand `isProp-isInitAlg` /
       `isProp-AlgEquiv` against substituted record literals — do
       not unfold when `to-from'` / `from-to'` below are elaborated. -}
    private
      module FAI {l : Level} {A : Type l} {B : A → Type l} {C D : Type l} where

        fai-to : AlgConfig A B C D → AlgInitEquiv A B C D
        fai-to cfg =
            InitAlgOn.sup initAlgC
          , InitAlgOn.sup initAlgD
          , (algConfigToAlgEquiv A B cfg , InitAlgOn.isInit initAlgC)
          where open AlgConfig cfg

        fai-from : AlgInitEquiv A B C D → AlgConfig A B C D
        fai-from (supC , supD , (e , ic)) = record
          { initAlgC = record { sup = supC ; isInit = ic }
          ; initAlgD = record { sup = supD ; isInit = initTransfer e ic } }

        abstract
          fai-to-from : (cfg : AlgConfig A B C D) → fai-from (fai-to cfg) ≡ cfg
          fai-to-from cfg =
              ap (λ z → record
                    { initAlgC = AlgConfig.initAlgC cfg
                    ; initAlgD = record
                        { sup = InitAlgOn.sup (AlgConfig.initAlgD cfg)
                        ; isInit = z } })
                 (isProp-isInitAlg (D , InitAlgOn.sup (AlgConfig.initAlgD cfg))
                    (initTransfer (algConfigToAlgEquiv A B cfg)
                                  (InitAlgOn.isInit (AlgConfig.initAlgC cfg)))
                    (InitAlgOn.isInit (AlgConfig.initAlgD cfg)))

          fai-from-to : (y : AlgInitEquiv A B C D) → fai-to (fai-from y) ≡ y
          fai-from-to (supC , supD , (e , ic)) =
              ap (λ z → supC , supD , (z , ic))
                 (isProp-AlgEquiv ic
                    (algConfigToAlgEquiv A B (fai-from (supC , supD , (e , ic))))
                    e)

    fullAlgIso : {l : Level} {A : Type l} {B : A → Type l} {C D : Type l} →
                 AlgConfig A B C D ≃ AlgInitEquiv A B C D
    fullAlgIso = record
      { f = FAI.fai-to     ; g = FAI.fai-from
      ; η = FAI.fai-to-from ; h = FAI.fai-from
      ; ε = FAI.fai-from-to }

    {-
       From `Config` to the algebra-isomorphism data and back

       Composing the (already-defined) `WTypeConfig → AlgConfig`
       conversion `wToAlg` with the equivalence `fullAlgIso` gives a
       total map `WTypeConfig A B C D → AlgInitEquiv A B C D`, and the
       reverse `AlgConfig → WTypeConfig` (build an `IndAlg` on each
       carrier from its initial-algebra structure via
       `initToHalf.initAlgToIndAlg`) composed with `fullAlgIso`'s
       inverse gives the map back. These are the two halves of the
       target correspondence at the `Config` (not `AlgConfig`) level.
    -}

    wConfigToAlgInitEquiv :
        {l : Level} {A : Type l} {B : A → Type l} {C D : Type l} →
        WTypeConfig {l} A B C D → AlgInitEquiv A B C D
    wConfigToAlgInitEquiv {A = A} {B} cfg = _≃_.f fullAlgIso (wToAlg A B cfg)

    algInitEquivToWConfig :
        {l : Level} {A : Type l} {B : A → Type l} {C D : Type l} →
        AlgInitEquiv A B C D → WTypeConfig {l} A B C D
    algInitEquivToWConfig {A = A} {B} d = record
      { indAlgC = initToHalf.initAlgToIndAlg A B (AlgConfig.initAlgC acfg)
      ; indAlgD = initToHalf.initAlgToIndAlg A B (AlgConfig.initAlgD acfg) }
      where acfg = _≃_.g fullAlgIso d

    {- The carrier-level bridge `WTypeIndAlg A B C ≃ InitAlgOn A B C`
       (and all the supporting `bridgeη-beta` machinery) lives in
       `inductive-repair.bridge`. It is opened above; we use its
       `bridgeFwd` / `bridgeBwd` / `bridgeε` / `bridgeη` / `bridgeEqv`
       directly below. -}

    {-
       The target theorem: WTypeConfig ≃ AlgInitEquiv

       Composes the carrier-level bridge equivalence (on each of `C`
       and `D`) with `fullAlgIso`. Equivalently: `Config` records and
       `AlgConfig` records each have two carrier-level fields, so the
       carrier bridge lifts to a `WTypeConfig ≃ AlgConfig`, and then
       `fullAlgIso` gives the rest.
    -}

    module _ {l : Level} {A : Type l} {B : A → Type l} {C D : Type l} where

      private
        mkW : WTypeIndAlg {l} A B C → WTypeIndAlg {l} A B D → WTypeConfig {l} A B C D
        mkW iC iD = record { indAlgC = iC ; indAlgD = iD }

        mkWFromAlg : AlgConfig A B C D → WTypeConfig {l} A B C D
        mkWFromAlg acfg = mkW (bridgeBwd (AlgConfig.initAlgC acfg))
                              (bridgeBwd (AlgConfig.initAlgD acfg))

        mkA : InitAlgOn A B C → InitAlgOn A B D → AlgConfig A B C D
        mkA pC pD = record { initAlgC = pC ; initAlgD = pD }

        to' : WTypeConfig {l} A B C D → AlgInitEquiv A B C D
        to' = wConfigToAlgInitEquiv

        from' : AlgInitEquiv A B C D → WTypeConfig {l} A B C D
        from' = algInitEquivToWConfig

        {- `from ∘ to`: first collapse `fullAlgIso.g ∘ fullAlgIso.f` via
           `fullAlgIso.η`, then discharge each component by `bridgeη`. -}
        to-from' : (cfg : WTypeConfig {l} A B C D) → from' (to' cfg) ≡ cfg
        to-from' cfg =
            ap mkWFromAlg (_≃_.η fullAlgIso (wToAlg A B cfg))
          • ap frame-C (bridgeη iC)
          • ap (mkW iC) (bridgeη iD)
          where
            iC = Config.indAlgC cfg
            iD = Config.indAlgD cfg
            frame-C = λ z → mkW z (bridgeBwd (bridgeFwd iD))

        {- `to ∘ from`: factors through `fullAlgIso`'s round-trip
           and `bridgeε` on each carrier. -}
        from-to' : (d : AlgInitEquiv A B C D) → to' (from' d) ≡ d
        from-to' d =
            ap (_≃_.f fullAlgIso)
               (ap frame-C (bridgeε pC) • ap (mkA pC) (bridgeε pD))
          • _≃_.ε fullAlgIso d
          where
            acfg = _≃_.g fullAlgIso d
            pC = AlgConfig.initAlgC acfg
            pD = AlgConfig.initAlgD acfg
            frame-C = λ z → mkA z (bridgeFwd (bridgeBwd pD))

      -- Theorem 3.11 (W-type Configurations are Unique Algebra Equivalences)
      wtypeConfigEqv : WTypeConfig {l} A B C D ≃ AlgInitEquiv A B C D
      wtypeConfigEqv = record
        { f = to' ; g = from' ; η = to-from' ; h = from' ; ε = from-to' }
