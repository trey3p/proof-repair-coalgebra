{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import palg
open import inductive-repair.indspec
open import inductive-repair.config
open import inductive-repair.palg-config
open import inductive-repair.wtype-config hiding (A ; B)
open import inductive-repair.alg-iso

{-
   `inductive-repair.bridge`: the carrier-level equivalence

     WTypeIndAlg A B C  ≃  InitAlgOn A B C

   and all supporting machinery (the `bridgeη-beta` Sojakova
   2-cell and its peripherals). Split out from `inductive-repair.conversion`
   so the heavy path-algebra proofs live in their own `.agdai`
   and don't recompile every time `conversion.agda` changes.

   Re-exports the carrier-level `bridgeEqv` and the per-component
   building blocks (`bridgeFwd`, `bridgeBwd`, `bridgeε`,
   `bridgeη-ind`, `bridgeη-beta`, `bridgeη`). `conversion.agda`
   uses these to assemble the full `WTypeConfig ≃ AlgInitEquiv`.
-}
module inductive-repair.bridge where

    {-
       The carrier-level bridge maps
    -}

    bridgeFwd : {l : Level} {A : Type l} {B : A → Type l} {C : Type l} →
                WTypeIndAlg {l} A B C → InitAlgOn A B C
    bridgeFwd {A = A} {B} ia = indAlgToInit.wIndAlgToInit A B ia

    bridgeBwd : {l : Level} {A : Type l} {B : A → Type l} {C : Type l} →
                InitAlgOn A B C → WTypeIndAlg {l} A B C
    bridgeBwd {A = A} {B} initAlg = initToHalf.initAlgToIndAlg A B initAlg

    {- `bridgeε`: the `InitAlgOn` round-trip. `sup` is recovered
       definitionally (function/Σ/⊤ η reduce
       `λ(a,t) → algebra tt (a,t,tt)` back to `sup ia`); `isInit`
       is a proposition. The reconstructed witness is kept opaque
       via the `abstract` block around `wIsInit` in `palg-config`. -}
    bridgeε : {l : Level} {A : Type l} {B : A → Type l} {C : Type l} →
              (ia : InitAlgOn A B C) → bridgeFwd (bridgeBwd ia) ≡ ia
    bridgeε {C = C} ia =
        ap (λ z → record { sup = InitAlgOn.sup ia ; isInit = z })
           (isProp-isInitAlg (C , InitAlgOn.sup ia)
                             (InitAlgOn.isInit (bridgeFwd (bridgeBwd ia)))
                             (InitAlgOn.isInit ia))

    {- The `algebra` field is preserved definitionally by the
       round-trip (Σ/⊤ η). -}
    bridgeη-algebra : {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
                      (ia : WTypeIndAlg {l} A B C) →
                      IndAlg.algebra (bridgeBwd (bridgeFwd ia))
                        ≡ IndAlg.algebra ia
    bridgeη-algebra ia = refl

    {- The `ind` field is recovered up to funext via `ind-unique`. -}
    bridgeη-ind : {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
                  (ia : WTypeIndAlg {l} A B C) →
                  IndAlg.ind (bridgeBwd (bridgeFwd ia)) ≡ IndAlg.ind ia
    bridgeη-ind ia =
        ! (ext (λ motive → ext (λ cases → ext (λ a →
            ind-unique ia
              (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
              (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
              motive cases a))))

    {-
       `bridgeη-beta`: the Sojakova β-coherence 2-cell

       The reduction chain (cf. comment block in
       `palg-config.indHomPathUnq` for the analogous algebraic
       2-cell):

         tpt (BetaLaw sig) ip β-recon
           ≡ β-orig                                          (4-Π funext)

         tpt (BetaLaw sig) ip β-recon m cs c args
           ≡ β-orig m cs c args                              (pointwise)

       which by `tpt-betalaw-pw` (J on `ip`) + `tpt-path'` reduces
       to the genuine 2-cell

         ! (ap L ip) • β-recon p • ap R ip  ≡  β-orig p

       where `L i = i m cs (algebra c args)` and
       `R i = cs c args (mkIHs (arity c) (i m cs) args)`.
       This discharge is `bridgeη-beta-core`, the path-algebra
       step. Both `ap L ip` and `ap R ip` peel via `happly-!`
       and `happlyExt` three times to expose `ind-unique`'s
       constructor case.
    -}

    {- Level-polymorphic `tpt-path`. Needed because the source is
       `Induction sig alg : Type (lsuc l)` and the target is
       `m (alg c args) : Type l`. -}
    tpt-path' : {l₁ l₂ : Level} {A : Type l₁} {B : Type l₂}
                (L R : A → B) {a a' : A} (q : a ≡ a') (e : L a ≡ R a) →
                tpt (λ x → L x ≡ R x) q e ≡ ! (ap L q) • e • ap R q
    tpt-path' L R refl e = ! •unitr • ! •unitl

    {- Build an `IndAlg`-path from a `(ind, beta)`-path when
       `algebra` matches definitionally. -}
    indAlg-≡-intro-fixed-alg :
        {l : Level} {sig : Signature {l}} {C : Type l}
        {alg : ConstrAlgebra sig C}
        {ind₁ ind₂ : Induction sig alg}
        {beta₁ : BetaLaw sig ind₁}
        {beta₂ : BetaLaw sig ind₂}
        (ip : ind₁ ≡ ind₂)
        (bp : tpt (λ i → BetaLaw sig i) ip beta₁ ≡ beta₂) →
        record { algebra = alg ; ind = ind₁ ; beta = beta₁ }
          ≡ record { algebra = alg ; ind = ind₂ ; beta = beta₂ }
    indAlg-≡-intro-fixed-alg refl refl = refl

    {- Pointwise reduction of `tpt` across all four Π's of
       `BetaLaw` at once, by J on `ip`. -}
    tpt-betalaw-pw :
        {l : Level} {sig : Signature {l}} {C : Type l}
        {alg : ConstrAlgebra sig C}
        {ind₁ ind₂ : Induction sig alg}
        (ip : ind₁ ≡ ind₂)
        (β : BetaLaw sig ind₁)
        (m : C → Type l) (cs : Cases sig C alg m)
        (c : Signature.Op sig)
        (args : Args (Signature.arity sig c) C) →
        tpt (λ i → BetaLaw sig i) ip β m cs c args
          ≡ tpt (λ i → i m cs (alg c args)
                       ≡ cs c args (mkIHs (Signature.arity sig c) (i m cs) args))
                ip
                (β m cs c args)
    tpt-betalaw-pw refl β m cs c args = refl

    {- The "L" and "R" functions inside `tpt-path'`: see comment block
       above. Kept at module scope so `bridgeη-beta-core` and
       `ap-L-bridgeη-ind` share the same names. -}
    private
      Lfn : {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
            (alg : ConstrAlgebra (WTypeSignature {l} A B) C)
            (m : C → Type l) (cs : Cases (WTypeSignature {l} A B) C alg m)
            (c : ⊤ {l}) (args : Args (WTypeArity {l} A B c) C) →
            Induction (WTypeSignature {l} A B) alg → m (alg c args)
      Lfn alg m cs c args i = i m cs (alg c args)

      Rfn : {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
            (alg : ConstrAlgebra (WTypeSignature {l} A B) C)
            (m : C → Type l) (cs : Cases (WTypeSignature {l} A B) C alg m)
            (c : ⊤ {l}) (args : Args (WTypeArity {l} A B c) C) →
            Induction (WTypeSignature {l} A B) alg → m (alg c args)
      Rfn {l} {A} {B} alg m cs c args i =
        cs c args (mkIHs (WTypeArity {l} A B c) (i m cs) args)

    {- Non-dependent Σ path: `ap2 _,_ p refl ≡ Σ-≡-intro p refl`. -}
    ap2-,-≡-Σ-intro :
        {l : Level} {X : Type l} {a a' : X} (p : a ≡ a') →
        ap2 _,_ p (refl {x = tt {l}}) ≡ Σ-≡-intro {B = λ _ → ⊤ {l}} p refl
    ap2-,-≡-Σ-intro refl = refl

    {- The β-rule of `ia.ind` on the unique-motive used inside
       `ind-unique`. Exposes `ind-unique`'s value at a constructor. -}
    ind-unique-β :
        {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
        (ia : WTypeIndAlg {l} A B C)
        (m : C → Type l)
        (cs : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) m)
        (c : ⊤ {l}) (args : Args (WTypeArity {l} A B c) C) →
        ind-unique ia
          (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
          (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
          m cs (IndAlg.algebra ia c args)
        ≡ IndAlg.beta ia m cs c args
          • ap (cs c args)
               (mkIHs-cong (WTypeArity {l} A B c)
                           (IndAlg.ind ia m cs)
                           (IndAlg.ind (bridgeBwd (bridgeFwd ia)) m cs)
                           args
                           (mkIHs (WTypeArity {l} A B c)
                                  (ind-unique ia
                                     (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
                                     (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                                     m cs)
                                  args))
          • ! (IndAlg.beta (bridgeBwd (bridgeFwd ia)) m cs c args)
    ind-unique-β {l} {A} {B} {C} ia m cs c args =
      IndAlg.beta ia motive' cases' c args
      where
        -- Bind the heavy subexpressions once, to avoid repeated
        -- elaboration of dependent record projections.
        recon = bridgeBwd (bridgeFwd ia)
        ind-orig = IndAlg.ind ia
        β-orig = IndAlg.beta ia
        ind-recon = IndAlg.ind recon
        β-recon = IndAlg.beta recon
        motive' : C → Type l
        motive' a = ind-orig m cs a ≡ ind-recon m cs a
        cases' : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) motive'
        cases' c' args' ih =
            β-orig m cs c' args'
          • ap (cs c' args')
               (mkIHs-cong (WTypeArity {l} A B c')
                           (ind-orig m cs) (ind-recon m cs) args' ih)
          • ! (β-recon m cs c' args')

    {- `ap Lfn` on `ext^3 (ind-unique …)` collapses via three
       `happlyExt`s and two `ap-∘`s to `ind-unique … m cs (alg c args)`. -}
    private
      ap-Lfn-ext3 :
          {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
          (ia : WTypeIndAlg {l} A B C)
          (m : C → Type l)
          (cs : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) m)
          (c : ⊤ {l}) (args : Args (WTypeArity {l} A B c) C) →
          ap (Lfn (IndAlg.algebra ia) m cs c args)
             (ext (λ m' → ext (λ cs' → ext (λ a' →
                ind-unique ia
                  (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
                  (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                  m' cs' a'))))
            ≡ ind-unique ia
                (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
                (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                m cs (IndAlg.algebra ia c args)
      ap-Lfn-ext3 {l} {A} {B} {C} ia m cs c args =
          ap-∘ {f = withCsAtArg} {g = atM} e3
        • ap (ap withCsAtArg) (! (happly-ap e3 m))
        • ap (ap withCsAtArg) (happlyExt _ m)
        • ap-∘ {f = withAtArg} {g = atCs} e2-m
        • ap (ap withAtArg) (! (happly-ap e2-m cs))
        • ap (ap withAtArg) (happlyExt _ cs)
        • ! (happly-ap e1-m-cs (alg c args))
        • happlyExt _ (alg c args)
        where
          alg = IndAlg.algebra ia
          ind-recon = IndAlg.ind (bridgeBwd (bridgeFwd ia))
          β-recon = IndAlg.beta (bridgeBwd (bridgeFwd ia))
          e3 = ext (λ m' → ext (λ cs' → ext (λ a' →
                  ind-unique ia ind-recon β-recon m' cs' a')))
          e2-m = ext (λ cs' → ext (λ a' →
                  ind-unique ia ind-recon β-recon m cs' a'))
          e1-m-cs = ext (λ a' → ind-unique ia ind-recon β-recon m cs a')
          -- Named composition fragments. Naming these once means
          -- Agda elaborates each lambda's (dependent) type a single
          -- time instead of once per occurrence in the `_•_` chain.
          atM = λ (i : Induction (WTypeSignature {l} A B) alg) → i m
          atCs = λ (k : Cases (WTypeSignature {l} A B) C alg m → (a : C) → m a) → k cs
          withCsAtArg = λ (y : Cases (WTypeSignature {l} A B) C alg m → (a : C) → m a) →
                          y cs (alg c args)
          withAtArg = λ (y : (a : C) → m a) → y (alg c args)

    ap-L-bridgeη-ind :
        {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
        (ia : WTypeIndAlg {l} A B C)
        (m : C → Type l)
        (cs : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) m)
        (c : ⊤ {l}) (args : Args (WTypeArity {l} A B c) C) →
        ap (Lfn (IndAlg.algebra ia) m cs c args) (bridgeη-ind ia)
          ≡ ! (ind-unique ia
                  (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
                  (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                  m cs (IndAlg.algebra ia c args))
    ap-L-bridgeη-ind ia m cs c args =
        ap-! (Lfn (IndAlg.algebra ia) m cs c args) _
      • ap ! (ap-Lfn-ext3 ia m cs c args)

    {- `ap (λ p → (p , tt)) p ≡ Σ-≡-intro p refl` for the non-dependent
       Σ with second component `⊤`. By J on `p`. -}
    private
      ap-pair-tt : {l : Level} {A : Type l} {a a' : A} (p : a ≡ a') →
                   ap (λ z → (z , tt {l})) p
                     ≡ Σ-≡-intro {B = λ _ → ⊤ {l}} p refl
      ap-pair-tt refl = refl

      {- Dependent precomposition by `_∘ t`. Same template as
         `common.precomp-ext` but with a dependent codomain so it
         applies to `(a : C) → m a`. -}
      precomp-ext-dep :
          {l : Level} {A B : Type l} {P : B → Type l}
          {f g : (b : B) → P b}
          (i : A → B) (e : (b : B) → f b ≡ g b) →
          ap (λ k → λ a → k (i a)) (ext e)
            ≡ ext (λ a → e (i a))
      precomp-ext-dep {A = A} {B} {P} {f} {g} i e =
            extHapply (ap (λ k → λ a → k (i a)) (ext e))
          • ap ext (ext pw)
        where
          pw : (x : A) →
               happly (ap (λ k → λ a → k (i a)) (ext e)) x ≡ e (i x)
          pw x =
              happly-ap (ap (λ k → λ a → k (i a)) (ext e)) x
            • ! (ap-∘ {f = λ (h : (a : A) → P (i a)) → h x}
                      {g = λ k → λ a → k (i a)} (ext e))
            • ! (happly-ap (ext e) (i x))
            • happlyExt e (i x)

    {- `ap Rfn` on `ext^3 (ind-unique …)` collapses to
       `ap (cs c args) (Σ-≡-intro (ext (λ d → ind-unique … (t d))) refl)`.
       Same overall shape as `ap-Lfn-ext3` but with two extra
       compositions (`precomp-ext-dep` for `_∘ t` and `ap-pair-tt`
       for the `(_, tt)` wrap). -}
    private
      ap-Rfn-ext3 :
          {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
          (ia : WTypeIndAlg {l} A B C)
          (m : C → Type l)
          (cs : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) m)
          (c : ⊤ {l}) (a₀ : A) (t : B a₀ → C) →
          ap (Rfn (IndAlg.algebra ia) m cs c (a₀ , t , tt))
             (ext (λ m' → ext (λ cs' → ext (λ a' →
                ind-unique ia
                  (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
                  (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                  m' cs' a'))))
            ≡ ap (cs c (a₀ , t , tt))
                 (Σ-≡-intro {B = λ _ → ⊤}
                   (ext (λ d → ind-unique ia
                                 (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
                                 (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                                 m cs (t d)))
                   refl)
      ap-Rfn-ext3 {l} {A} {B} {C} ia m cs c a₀ t =
            ap-∘ {f = wrapAtCsT} {g = atM} e3
          • ap (ap wrapAtCsT) (! (happly-ap e3 m))
          • ap (ap wrapAtCsT) (happlyExt _ m)
          • ap-∘ {f = wrapAtT} {g = atCs} e2-m
          • ap (ap wrapAtT) (! (happly-ap e2-m cs))
          • ap (ap wrapAtT) (happlyExt _ cs)
          • ap-∘ {f = wrapId} {g = precompT} e1-m-cs
          • ap (ap wrapId) (precomp-ext-dep t e-pw)
          • ap-∘ {f = cs c (a₀ , t , tt)} {g = pairTt} ext-tα
          • ap (ap (cs c (a₀ , t , tt))) (ap-pair-tt ext-tα)
        where
          ind-recon = IndAlg.ind (bridgeBwd (bridgeFwd ia))
          β-recon = IndAlg.beta (bridgeBwd (bridgeFwd ia))
          alg = IndAlg.algebra ia
          e3 = ext (λ m' → ext (λ cs' → ext (λ a' →
                  ind-unique ia ind-recon β-recon m' cs' a')))
          e2-m = ext (λ cs' → ext (λ a' →
                  ind-unique ia ind-recon β-recon m cs' a'))
          e1-m-cs = ext (λ a' → ind-unique ia ind-recon β-recon m cs a')
          e-pw = λ a' → ind-unique ia ind-recon β-recon m cs a'
          ext-tα = ext (λ d → ind-unique ia ind-recon β-recon m cs (t d))
          -- Named composition fragments. Each lambda's (dependent)
          -- type gets elaborated once instead of three times in the
          -- `_•_` chain below.
          atM = λ (i : Induction (WTypeSignature {l} A B) alg) → i m
          atCs = λ (k : Cases (WTypeSignature {l} A B) C alg m → (a : C) → m a) → k cs
          precompT = λ (k : (a : C) → m a) → λ (d : B a₀) → k (t d)
          pairTt = λ (z : (d : B a₀) → m (t d)) → (z , tt {l})
          wrapAtCsT = λ (y : Cases (WTypeSignature {l} A B) C alg m → (a : C) → m a) →
                        cs c (a₀ , t , tt) ((λ d → y cs (t d)) , tt)
          wrapAtT = λ (y : (a : C) → m a) →
                        cs c (a₀ , t , tt) ((λ d → y (t d)) , tt)
          wrapId = λ (y : (d : B a₀) → m (t d)) →
                        cs c (a₀ , t , tt) (y , tt)

    ap-R-bridgeη-ind :
        {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
        (ia : WTypeIndAlg {l} A B C)
        (m : C → Type l)
        (cs : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) m)
        (c : ⊤ {l}) (a₀ : A) (t : B a₀ → C) →
        ap (Rfn (IndAlg.algebra ia) m cs c (a₀ , t , tt))
           (bridgeη-ind ia)
          ≡ ! (ap (cs c (a₀ , t , tt))
                  (Σ-≡-intro {B = λ _ → ⊤ {l}}
                    (ext (λ d → ind-unique ia
                                  (IndAlg.ind (bridgeBwd (bridgeFwd ia)))
                                  (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                                  m cs (t d)))
                    refl))
    ap-R-bridgeη-ind ia m cs c a₀ t =
        ap-! (Rfn (IndAlg.algebra ia) m cs c (a₀ , t , tt)) _
      • ap ! (ap-Rfn-ext3 ia m cs c a₀ t)

    {- The path-algebra discharge of the Sojakova 2-cell. -}
    bridgeη-beta-core :
        {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
        (ia : WTypeIndAlg {l} A B C)
        (m : C → Type l)
        (cs : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) m)
        (c : ⊤ {l}) (args : Args (WTypeArity {l} A B c) C) →
          ! (ap (Lfn (IndAlg.algebra ia) m cs c args) (bridgeη-ind ia))
          • IndAlg.beta (bridgeBwd (bridgeFwd ia)) m cs c args
          • ap (Rfn (IndAlg.algebra ia) m cs c args) (bridgeη-ind ia)
            ≡ IndAlg.beta ia m cs c args
    bridgeη-beta-core {l} {A} {B} {C} ia m cs c (a₀ , t , tt) =
        ap frame-! (ap-L-bridgeη-ind ia m cs c (a₀ , t , tt))
      • ap frame-id (!! (ec constr))
      • ap frame-r (ap-R-bridgeη-ind ia m cs c a₀ t)
      • ap frame-ec ec-eq
      • •assoc {p = β-orig} {q = apR • ! β-recon} {r = β-recon • ! apR}
      • ap (β-orig •_) inner-collapse
      • •unitr
      where
        alg = IndAlg.algebra ia
        β-orig = IndAlg.beta ia m cs c (a₀ , t , tt)
        recon = bridgeBwd (bridgeFwd ia)
        ind-recon = IndAlg.ind recon
        β-recon = IndAlg.beta recon m cs c (a₀ , t , tt)
        ec : (a : C) → IndAlg.ind ia m cs a ≡ ind-recon m cs a
        ec = ind-unique ia ind-recon (IndAlg.beta recon) m cs
        constr = alg c (a₀ , t , tt)
        apR-ip = ap (Rfn alg m cs c (a₀ , t , tt)) (bridgeη-ind ia)
        ext-IHs : (λ d → IndAlg.ind ia m cs (t d))
                ≡ (λ d → ind-recon m cs (t d))
        ext-IHs = ext (λ d → ec (t d))
        Σ-IHs : ((λ d → IndAlg.ind ia m cs (t d)) , tt {l})
              ≡ ((λ d → ind-recon m cs (t d)) , tt)
        Σ-IHs = Σ-≡-intro {B = λ _ → ⊤} ext-IHs refl
        apR = ap (cs c (a₀ , t , tt)) Σ-IHs
        ec-eq : ec constr ≡ β-orig • apR • ! β-recon
        ec-eq = ind-unique-β ia m cs c (a₀ , t , tt)
              • ap frame-q (ap2-,-≡-Σ-intro ext-IHs)
          where
            frame-q = λ q → β-orig • ap (cs c (a₀ , t , tt)) q • ! β-recon
        -- Named frame lambdas for the body's `_•_` chain. Naming each
        -- lambda once means Agda elaborates its dependent path type
        -- a single time instead of at every `ap (λ z → …)` call site.
        frame-! = λ z → ! z • β-recon • apR-ip
        frame-id = λ z → z • β-recon • apR-ip
        frame-r = λ z → ec constr • β-recon • z
        frame-ec = λ z → z • β-recon • ! apR
        inner-collapse =
            •assoc {p = apR} {q = ! β-recon} {r = β-recon • ! apR}
          • ap (apR •_)
               ( ! (•assoc {p = ! β-recon} {q = β-recon} {r = ! apR})
               • ap (_• ! apR) •invl
               • •unitl)
          • •invr

    bridgeη-beta-pw :
        {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
        (ia : WTypeIndAlg {l} A B C)
        (m : C → Type l)
        (cs : Cases (WTypeSignature {l} A B) C (IndAlg.algebra ia) m)
        (c : ⊤ {l}) (args : Args (WTypeArity {l} A B c) C) →
        tpt (λ i → BetaLaw (WTypeSignature {l} A B) i)
            (bridgeη-ind ia)
            (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
            m cs c args
          ≡ IndAlg.beta ia m cs c args
    bridgeη-beta-pw {l} {A} {B} ia m cs c args =
        tpt-betalaw-pw {sig = WTypeSignature {l} A B} {alg = alg}
                       (bridgeη-ind ia) β-recon m cs c args
      • tpt-path' (Lfn alg m cs c args) (Rfn alg m cs c args)
                  (bridgeη-ind ia) (β-recon m cs c args)
      • bridgeη-beta-core ia m cs c args
      where
        alg = IndAlg.algebra ia
        β-recon = IndAlg.beta (bridgeBwd (bridgeFwd ia))

    bridgeη-beta : {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
                   (ia : WTypeIndAlg {l} A B C) →
                   tpt (λ i → BetaLaw (WTypeSignature {l} A B) i)
                       (bridgeη-ind ia)
                       (IndAlg.beta (bridgeBwd (bridgeFwd ia)))
                     ≡ IndAlg.beta ia
    bridgeη-beta ia =
      ext (λ motive →
      ext (λ cases →
      ext (λ c →
      ext (λ args → bridgeη-beta-pw ia motive cases c args))))

    {-
       Assembling `bridgeη` and the carrier-level ≃
    -}

    bridgeη : {l : Level} {A : Type l} {B : A → Type l} {C : Type l}
              (ia : WTypeIndAlg {l} A B C) → bridgeBwd (bridgeFwd ia) ≡ ia
    bridgeη ia = indAlg-≡-intro-fixed-alg (bridgeη-ind ia) (bridgeη-beta ia)

    bridgeEqv : {l : Level} {A : Type l} {B : A → Type l} {C : Type l} →
                WTypeIndAlg {l} A B C ≃ InitAlgOn A B C
    bridgeEqv = record
      { f = bridgeFwd ; g = bridgeBwd ; η = bridgeη
      ; h = bridgeBwd ; ε = bridgeε }
