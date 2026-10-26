{-# OPTIONS --cubical --guardedness --safe #-}

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import Agda.Primitive.Cubical using (I; i0; i1)
  renaming (primIMin to _∧_; primIMax to _∨_;
            primINeg to ~_; primTransp to transp)
open import coinductive-repair.mtype hiding (corec)
open import coinductive-repair.config

{-
    PUMPKIN Pi coherence conditions derived from a `CoConfig`,
    the coinductive mirror of `inductive-repair.coherence`:
    `destr_ok` (the destructor commuting square under the carrier
    equivalence), the per-side corecursor β-rules (`iota_ok`), and
    `corec_ok` (cross-side corecursor coherence) in `CoCoherence`;
    the strict two-dimensional `coind_ok` over an `HCoConfig` in
    `HCoCoherence`.
-}
module coinductive-repair.coherence {ℓ : Level} where
    open CoSignature
    open _≃_

    {- Arity-generic helpers, config-independent. -}

    {-
        `subst`-naturality through `mapOutputs`, built as a direct
        cubical transport ladder (avoiding `J`, which would not
        reduce on the non-constant family `λ a → Outputs (B a) Ty`).
    -}
    subst-mapOutputs-nat :
        {Ty1 Ty2 : Type ℓ} (f : Ty1 → Ty2)
        {A : Type ℓ} (B : A → DestrArity {ℓ})
        {a1 a2 : A} (p : a1 ≡ a2) (o : Outputs (B a1) Ty1) →
        subst (λ a → Outputs (B a) Ty2) p (mapOutputs (B a1) f o)
          ≡ mapOutputs (B a2) f
              (subst (λ a → Outputs (B a) Ty1) p o)
    subst-mapOutputs-nat {Ty1 = Ty1} {Ty2 = Ty2} f B {a1} {a2} p o k =
        transp (λ i → Outputs (B (p (i ∨ k))) Ty2) k
               (mapOutputs (B (p k)) f
                  (transp (λ i → Outputs (B (p (i ∧ k))) Ty1) (~ k) o))

    -- At `refl`, `subst-mapOutputs-nat` is the composite of the two
    -- `transportRefl` edges (via `transp-diag`).
    subst-mapOutputs-nat-refl :
        {Ty1 Ty2 : Type ℓ} (f : Ty1 → Ty2)
        {A : Type ℓ} (B : A → DestrArity {ℓ}) {a1 : A}
        (o : Outputs (B a1) Ty1) →
        subst-mapOutputs-nat f B (λ _ → a1) o
          ≡ transportRefl (mapOutputs (B a1) f o)
              ∙ sym (cong (mapOutputs (B a1) f) (transportRefl o))
    subst-mapOutputs-nat-refl f B {a1} o =
        transp-diag (cong (mapOutputs (B a1) f) (sym (transportRefl o)))

    {-
        Naturality of `OutputsRel` under post-composition by a
        relation-preserving function. If `f` preserves the
        relation (`lift : R1 → R2 ∘ (f × f)`), then
        `mapOutputs f` carries an `OutputsRel R1` to an
        `OutputsRel R2`.

        Recursion on the arity. The `Nonrec` case needs
        `subst-mapOutputs-nat` to align the IH's first argument
        with the goal's first argument.
    -}
    OutputsRel-map :
        (cs : DestrArity {ℓ})
        {Ty1 Ty2 : Type ℓ}
        {R1 : Ty1 → Ty1 → Type ℓ} {R2 : Ty2 → Ty2 → Type ℓ}
        (f : Ty1 → Ty2)
        (lift : ∀ {a b : Ty1} → R1 a b → R2 (f a) (f b))
        {o1 o2 : Outputs cs Ty1} →
        OutputsRel cs R1 o1 o2 →
        OutputsRel cs R2 (mapOutputs cs f o1) (mapOutputs cs f o2)
    OutputsRel-map Done         _ _    {_}      {_}      _              = tt
    OutputsRel-map (Nonrec A k) f lift {a1 , o1} {a2 , o2} (p , rest) =
        p ,
        subst (λ Z → OutputsRel (k a2) _ Z (mapOutputs (k a2) f o2))
              (sym (subst-mapOutputs-nat f k p o1))
              (OutputsRel-map (k a2) f lift rest)
    OutputsRel-map (Rec D cs)   f lift {r1 , o1} {r2 , o2} (rrel , rest) =
        (λ d → lift (rrel d)) , OutputsRel-map cs f lift rest

    {-
       Proposition 4.19 (Correctness Conditions), parts (1)–(3)
       Coherence for `CoConfig`
    -}

    module CoCoherence {sig : CoSignature {ℓ}} {C D : Type ℓ}
                       (cfg : CoConfig sig C D) where
      open CoConfig cfg
      open CoindCoalg coindCoalgC
        renaming (destr to destrC; corec to corecC;
                  corec-β to corecC-β; corec-η to corecC-η)
      open CoindCoalg coindCoalgD
        renaming (destr to destrD; corec to corecD;
                  corec-β to corecD-β; corec-η to corecD-η)

      -- By construction `fwd carrier-eqv` is `corecD destrC`.
      carrier-eqv : C ≃ D
      carrier-eqv = coConfigToEquiv cfg

      {-
          Proposition 4.19 (1)
          `destr_ok`: the per-destructor coalgebra-hom square for
          `fwd carrier-eqv` — exactly `corecD-β` on `destrC`.
      -}
      destr-ok : (op : Op sig) (c : C) →
                 destrD op (fwd carrier-eqv c)
                   ≡ mapOutputs (arity sig op)
                                (fwd carrier-eqv) (destrC op c)
      destr-ok = corecD-β destrC

      {-
          Proposition 4.19 (2)
          `iota_ok` per side: each carrier's corecursor β-rule,
          quantified over the source coalgebra.
      -}
      beta-ok-C :
          {C' : Type ℓ} (destrC' : DestrAlgebra sig C') →
          (op : Op sig) (c' : C') →
          destrC op (corecC destrC' c')
            ≡ mapOutputs (arity sig op)
                         (corecC destrC') (destrC' op c')
      beta-ok-C = corecC-β

      beta-ok-D :
          {D' : Type ℓ} (destrD' : DestrAlgebra sig D') →
          (op : Op sig) (d' : D') →
          destrD op (corecD destrD' d')
            ≡ mapOutputs (arity sig op)
                         (corecD destrD') (destrD' op d')
      beta-ok-D = corecD-β

      {-
          `fwd carrier-eqv ∘ corecC destrC'` is a coalgebra-hom
          `(C', destrC') → (D, destrD)`: chain `destr-ok`,
          `beta-ok-C`, and `mapOutputs-∘`.
      -}
      compose-is-hom-D :
          {C' : Type ℓ} (destrC' : DestrAlgebra sig C')
          (op : Op sig) (c' : C') →
          destrD op (fwd carrier-eqv (corecC destrC' c'))
            ≡ mapOutputs (arity sig op)
                         (λ x → fwd carrier-eqv (corecC destrC' x))
                         (destrC' op c')
      compose-is-hom-D destrC' op c' =
          destr-ok op (corecC destrC' c')
        ∙ cong (mapOutputs (arity sig op) (fwd carrier-eqv))
               (beta-ok-C destrC' op c')
        ∙ mapOutputs-∘ (arity sig op)
                       (corecC destrC') (fwd carrier-eqv)
                       (destrC' op c')

      {-
          Proposition 4.19 (3)
          `corec_ok`: cross-side corecursor coherence. The two
          coalgebra homs `fwd carrier-eqv ∘ corecC destrC'` and
          `corecD destrC'` are identified pointwise by `corecD-η`.
      -}
      corec-ok :
          {C' : Type ℓ} (destrC' : DestrAlgebra sig C')
          (c' : C') →
          fwd carrier-eqv (corecC destrC' c') ≡ corecD destrC' c'
      corec-ok destrC' =
          corecD-η destrC'
                   (λ c' → fwd carrier-eqv (corecC destrC' c'))
                   (compose-is-hom-D destrC')

      {-
          Image-lift of a relation on `C` to a relation on `D`
          via `fwd carrier-eqv`: two D-elements are related iff
          they have C-preimages whose R-witness fits between them.
      -}
      LiftRel : (R : C → C → Type ℓ) → D → D → Type ℓ
      LiftRel R d1 d2 =
          Σ C (λ c1 → Σ C (λ c2 →
              Σ (R c1 c2) (λ _ →
                  Σ (fwd carrier-eqv c1 ≡ d1) (λ _ →
                      fwd carrier-eqv c2 ≡ d2))))

      {-
          A C-side bisim transports to a D-side bisim: lift the
          witness through `mapOutputs (fwd carrier-eqv)` via
          `OutputsRel-map`, then `subst` along the `destr-ok`
          squares to land on the D-side destructor outputs.
      -}
      bisim-transport :
          (R : C → C → Type ℓ) → isBisim sig destrC R →
          isBisim sig destrD (LiftRel R)
      bisim-transport R isBis {d1} {d2} (c1 , c2 , r , p1 , p2) op =
          subst (λ outs → OutputsRel (arity sig op) (LiftRel R)
                            outs (destrD op d2))
                path-d1
                (subst (λ outs → OutputsRel (arity sig op) (LiftRel R)
                                   (mapOutputs (arity sig op)
                                               (fwd carrier-eqv)
                                               (destrC op c1))
                                   outs)
                       path-d2
                       lifted)
        where
          lift-witness : ∀ {a b : C} → R a b →
                         LiftRel R (fwd carrier-eqv a) (fwd carrier-eqv b)
          lift-witness {a} {b} r' = (a , b , r' , refl , refl)

          lifted : OutputsRel (arity sig op) (LiftRel R)
                     (mapOutputs (arity sig op) (fwd carrier-eqv)
                                 (destrC op c1))
                     (mapOutputs (arity sig op) (fwd carrier-eqv)
                                 (destrC op c2))
          lifted = OutputsRel-map (arity sig op) (fwd carrier-eqv)
                                  lift-witness (isBis r op)

          path-d1 : mapOutputs (arity sig op) (fwd carrier-eqv)
                               (destrC op c1)
                      ≡ destrD op d1
          path-d1 = sym (destr-ok op c1) ∙ cong (destrD op) p1

          path-d2 : mapOutputs (arity sig op) (fwd carrier-eqv)
                               (destrC op c2)
                      ≡ destrD op d2
          path-d2 = sym (destr-ok op c2) ∙ cong (destrD op) p2



    {-
       Proposition 4.19 (Correctness Conditions), part (4)
       Coherence for `HCoConfig` — the strict equational
       `coind_ok`. Two ways to construct a D-side path —
       `cong (fwd carrier-eqv)` of the C-side coind path, vs.
       the D-side coind on the transported bisim — are equal as
       2-cells. Not derivable at the `CoindCoalg` tier
       (`corec-η` is only function-level); the Σ-level
       uniqueness of `HCoindCoalg` supplies the 2-cell strength,
       and the proof goes through the derived 2-D coinduction
       principle `deriveCoind2D`.
    -}

    module HCoCoherence {sig : CoSignature {ℓ}} {C D : Type ℓ}
                        (hcfg : HCoConfig sig C D) where
      open HCoConfig hcfg

      -- Inherit the `CoConfig`-tier coherence (carrier equivalence,
      -- `destr-ok`, `beta-ok-{C,D}`, `corec-ok`, `LiftRel`,
      -- `bisim-transport`).
      open CoCoherence coConfig public

      open CoindCoalg coindCoalgC
        using ()
        renaming (destr to destrC; corec to corecC; corec-β to corecC-β)
      open CoindCoalg coindCoalgD
        using ()
        renaming (destr to destrD; corec to corecD; corec-β to corecD-β)
      open HCoindCoalg hCoindCoalgC
        using ()
        renaming (corec-uniq-Σ to corecC-uniq-Σ)
      open HCoindCoalg hCoindCoalgD
        using ()
        renaming (corec-uniq-Σ to corecD-uniq-Σ)

      {-
          `coind-ok` via the path-level coinduction principle
          `deriveCoind2D`: relate `cP r = cong fwd (deriveCoind C r)`
          and `dP r = deriveCoind D … (x,y,r,refl,refl)` by a 2-D
          relation `R₂` (the path-level `LiftRel`), prove the 2-D
          closure `R₂-closed`, and apply `deriveCoind2D`.
      -}
      module CoindOK
               (R : C → C → Type ℓ) (isBis : isBisim sig destrC R) where

        cP : ∀ {x y : C} → R x y →
             fwd carrier-eqv x ≡ fwd carrier-eqv y
        cP r = cong (fwd carrier-eqv) (deriveCoind coindCoalgC R isBis r)

        dP : ∀ {x y : C} (r : R x y) →
             fwd carrier-eqv x ≡ fwd carrier-eqv y
        dP {x} {y} r =
          deriveCoind coindCoalgD (LiftRel R) (bisim-transport R isBis)
                      (x , y , r , refl , refl)

        R₂ : {d d' : D} → d ≡ d' → d ≡ d' → Type ℓ
        R₂ {d} {d'} P Q =
          Σ C (λ x → Σ C (λ y → Σ (R x y) (λ r →
            Σ (fwd carrier-eqv x ≡ d) (λ ed →
            Σ (fwd carrier-eqv y ≡ d') (λ ed' →
              Σ (PathP (λ i → ed i ≡ ed' i) (cP r) P) (λ _ →
                  PathP (λ i → ed i ≡ ed' i) (dP r) Q))))))

        {-
            A bisimulation witness `realize`d as a path in `D`,
            with `Rec` children given by a child-path map
            (`cP` or `dP`). Both sides of the 2-D closure are
            routed through this, so per-arity the `Nonrec` heads
            coincide definitionally — trivialising the 2-D
            head-cell (the `M-shape-2-cell` analog). The `Nonrec`
            tail uses the `subst-mapOutputs-nat`-shifted recursive
            value (so the `OutputsRel2D` recursion aligns by a
            single `subst-filler`).
        -}
        realizeD : (cs : DestrArity)
                   (childpath : ∀ {a b : C} → R a b →
                                fwd carrier-eqv a ≡ fwd carrier-eqv b)
                   {co1 co2 : Outputs cs C} (w : OutputsRel cs R co1 co2) →
                   mapOutputs cs (fwd carrier-eqv) co1
                     ≡ mapOutputs cs (fwd carrier-eqv) co2
        realizeD Done         childpath w = refl
        realizeD (Nonrec A k) childpath {a1 , oo1} {a2 , oo2} (hp , rest) i =
            hp i ,
            toPathP {A = λ j → Outputs (k (hp j)) D}
                    (subst (λ z → z ≡ mapOutputs (k a2) (fwd carrier-eqv) oo2)
                           (sym (subst-mapOutputs-nat (fwd carrier-eqv) k hp oo1))
                           (realizeD (k a2) childpath rest)) i
        realizeD (Rec D' cs)  childpath {r1 , oo1} {r2 , oo2} (rrel , rest) i =
            (λ d → childpath (rrel d) i) , realizeD cs childpath rest i

        {-
            The 2-D `bisim-transport`: a C-side bisim witness `w`
            yields the 2-D bisimulation `OutputsRel2D` between its
            two realizations. Recursion on the arity: `Rec`
            children are `R₂ (cP …) (dP …)` with the trivial
            witness; `Nonrec` heads agree (`refl`) and the tail
            transports along the `subst-filler` round-trip. No
            postulate — the head-cell wall and the
            `fromPathP`/`toPathP` round-trip are both discharged.
        -}
        rel2D : (cs : DestrArity) {co1 co2 : Outputs cs C}
                (w : OutputsRel cs R co1 co2) →
                OutputsRel2D cs R₂ (realizeD cs cP w) (realizeD cs dP w)
        rel2D Done w = tt
        rel2D (Rec D' cs) {r1 , oo1} {r2 , oo2} (rrel , rest) =
            (λ d → r1 d , r2 d , rrel d , refl , refl , refl , refl)
            , rel2D cs rest
        rel2D (Nonrec A k) {a1 , oo1} {a2 , oo2} (hp , rest) = refl , tail
          where
            ER : Outputs (k a2) D
            ER = mapOutputs (k a2) (fwd carrier-eqv) oo2

            e : subst (λ a → Outputs (k a) D) hp
                      (mapOutputs (k a1) (fwd carrier-eqv) oo1)
                  ≡ mapOutputs (k a2) (fwd carrier-eqv)
                               (subst (λ a → Outputs (k a) C) hp oo1)
            e = subst-mapOutputs-nat (fwd carrier-eqv) k hp oo1

            Bf : Outputs (k a2) D → Type ℓ
            Bf z = z ≡ ER

            pc qc : mapOutputs (k a2) (fwd carrier-eqv)
                               (subst (λ a → Outputs (k a) C) hp oo1) ≡ ER
            pc = realizeD (k a2) cP rest
            qc = realizeD (k a2) dP rest

            Φ : (a1 ≡ a2) → Type ℓ
            Φ h = PathP (λ i → Outputs (k (h i)) D)
                        (mapOutputs (k a1) (fwd carrier-eqv) oo1)
                        (mapOutputs (k a2) (fwd carrier-eqv) oo2)

            csC = cong (λ r → snd r) (realizeD (Nonrec A k) cP (hp , rest))
            csD = cong (λ r → snd r) (realizeD (Nonrec A k) dP (hp , rest))

            eqC : fromPathP (subst Φ refl csC) ≡ subst Bf (sym e) pc
            eqC = cong fromPathP (substRefl Φ csC)
                ∙ fromPathP-toPathP {A = λ j → Outputs (k (hp j)) D}
                                    (subst Bf (sym e) pc)

            eqD : fromPathP csD ≡ subst Bf (sym e) qc
            eqD = fromPathP-toPathP {A = λ j → Outputs (k (hp j)) D}
                                    (subst Bf (sym e) qc)

            Ct : PathP (λ t → sym e t ≡ ER) pc (fromPathP (subst Φ refl csC))
            Ct = subst-filler Bf (sym e) pc ▷ sym eqC

            Dt : PathP (λ t → sym e t ≡ ER) qc (fromPathP csD)
            Dt = subst-filler Bf (sym e) qc ▷ sym eqD

            tail : OutputsRel2D (k a2) R₂
                     (fromPathP (subst Φ refl csC)) (fromPathP csD)
            tail = transport (λ t → OutputsRel2D (k a2) R₂ (Ct t) (Dt t))
                             (rel2D (k a2) rest)

        C-nat : (cs : DestrArity) {co1 co2 : Outputs cs C}
                (w : OutputsRel cs R co1 co2) →
                realizeD cs cP w
                  ≡ cong (mapOutputs cs (fwd carrier-eqv))
                         (realize cs coindCoalgC R isBis w)
        C-nat Done w = refl
        C-nat (Rec D' cs) {r1 , oo1} {r2 , oo2} (rrel , rest) j i =
            (λ d → cP (rrel d) i) , C-nat cs rest j i
        C-nat (Nonrec A k) {a1 , oo1} {a2 , oo2} (hp , rest) =
            J (λ a2' hp' → (oo2' : Outputs (k a2') C)
                           (rest' : OutputsRel (k a2') R
                                      (subst (λ a → Outputs (k a) C) hp' oo1) oo2') →
                 realizeD (Nonrec A k) cP (hp' , rest')
                   ≡ cong (mapOutputs (Nonrec A k) (fwd carrier-eqv))
                          (realize (Nonrec A k) coindCoalgC R isBis (hp' , rest')))
              baseC hp oo2 rest
          where
            baseC : (oo2' : Outputs (k a1) C)
                    (rest' : OutputsRel (k a1) R
                               (subst (λ a → Outputs (k a) C) refl oo1) oo2') →
                  realizeD (Nonrec A k) cP (refl , rest')
                    ≡ cong (mapOutputs (Nonrec A k) (fwd carrier-eqv))
                           (realize (Nonrec A k) coindCoalgC R isBis (refl , rest'))
            baseC oo2' rest' = cong (cong (a1 ,_)) tailEq
              where
                Mf : Outputs (k a1) C → Outputs (k a1) D
                Mf = mapOutputs (k a1) (fwd carrier-eqv)
                Mf2 = mapOutputs (k a1) (fwd carrier-eqv) oo2'
                e₀ = subst-mapOutputs-nat (fwd carrier-eqv) k refl oo1
                tr1 = transportRefl (mapOutputs (k a1) (fwd carrier-eqv) oo1)
                cmtR = cong Mf (transportRefl oo1)
                rD = realizeD (k a1) cP rest'
                rC = realize (k a1) coindCoalgC R isBis rest'

                tailEq :
                    toPathP {A = λ j → Outputs (k (refl j)) D}
                            (subst (λ z → z ≡ Mf2) (sym e₀) rD)
                      ≡ cong Mf (toPathP {A = λ j → Outputs (k (refl j)) C} rC)
                tailEq =
                    subst-slide tr1 (subst (λ z → z ≡ Mf2) (sym e₀) rD)
                  ∙ cong (sym tr1 ∙_) (subst-slide (sym e₀) rD)
                  ∙ cong (λ z → sym tr1 ∙ (z ∙ rD))
                         (subst-mapOutputs-nat-refl (fwd carrier-eqv) k oo1)
                  ∙ cong (sym tr1 ∙_) (∙assoc tr1 (sym cmtR) rD)
                  ∙ sym (∙assoc (sym tr1) tr1 (sym cmtR ∙ rD))
                  ∙ cong (_∙ (sym cmtR ∙ rD)) (lCancel tr1)
                  ∙ ∙-idl (sym cmtR ∙ rD)
                  ∙ cong (sym cmtR ∙_) (C-nat (k a1) rest')
                  ∙ sym (cong-∙ Mf (sym (transportRefl oo1)) rC)
                  ∙ cong (cong Mf) (sym (subst-slide (transportRefl oo1) rC))

        -- The lift-witness used by `dP`/`bisim-transport`.
        lw : ∀ {a b : C} → R a b →
             LiftRel R (fwd carrier-eqv a) (fwd carrier-eqv b)
        lw {a} {b} r' = a , b , r' , refl , refl

        {-
            D-naturality: the `subst`-form `realizeD cs dP` equals
            the config `realize` on the D-coalgebra of the
            `OutputsRel-map`-lifted witness. (`Rec` definitional;
            `Nonrec` collapses the head by `J`, then the tail is
            the recursion composed with `realize-subst-nat` — the
            `OutputsRel-map` `Nonrec` subst *is* the alignment, so
            no `transportRefl` bookkeeping is needed here.)
        -}
        D-nat : (cs : DestrArity) {co1 co2 : Outputs cs C}
                (w : OutputsRel cs R co1 co2) →
                realizeD cs dP w
                  ≡ realize cs coindCoalgD (LiftRel R) (bisim-transport R isBis)
                            (OutputsRel-map cs (fwd carrier-eqv) lw w)
        D-nat Done w = refl
        D-nat (Rec D' cs) {r1 , oo1} {r2 , oo2} (rrel , rest) j i =
            (λ d → dP (rrel d) i) , D-nat cs rest j i
        D-nat (Nonrec A k) {a1 , oo1} {a2 , oo2} (hp , rest) =
            J (λ a2' hp' → (oo2' : Outputs (k a2') C)
                           (rest' : OutputsRel (k a2') R
                                      (subst (λ a → Outputs (k a) C) hp' oo1) oo2') →
                 realizeD (Nonrec A k) dP (hp' , rest')
                   ≡ realize (Nonrec A k) coindCoalgD (LiftRel R) (bisim-transport R isBis)
                             (OutputsRel-map (Nonrec A k) (fwd carrier-eqv) lw (hp' , rest')))
              baseD hp oo2 rest
          where
            baseD : (oo2' : Outputs (k a1) C)
                    (rest' : OutputsRel (k a1) R
                               (subst (λ a → Outputs (k a) C) refl oo1) oo2') →
                  realizeD (Nonrec A k) dP (refl , rest')
                    ≡ realize (Nonrec A k) coindCoalgD (LiftRel R) (bisim-transport R isBis)
                              (OutputsRel-map (Nonrec A k) (fwd carrier-eqv) lw (refl , rest'))
            baseD oo2' rest' =
                cong (cong (a1 ,_))
                     (cong (toPathP {A = λ j → Outputs (k (refl j)) D}) argEqD)
              where
                e₀ = subst-mapOutputs-nat (fwd carrier-eqv) k refl oo1
                Mf2 = mapOutputs (k a1) (fwd carrier-eqv) oo2'
                orm = OutputsRel-map (k a1) (fwd carrier-eqv) lw rest'
                argEqD :
                    subst (λ z → z ≡ Mf2) (sym e₀) (realizeD (k a1) dP rest')
                      ≡ realize (k a1) coindCoalgD (LiftRel R) (bisim-transport R isBis)
                                (subst (λ Z → OutputsRel (k a1) (LiftRel R) Z Mf2)
                                       (sym e₀) orm)
                argEqD =
                    cong (subst (λ z → z ≡ Mf2) (sym e₀)) (D-nat (k a1) rest')
                  ∙ realize-subst-nat (k a1) coindCoalgD (LiftRel R)
                                      (bisim-transport R isBis) (sym e₀) orm

        {-
            The closure `R₂-closed`, reduced to its endpoint-clean
            core. The general `R₂` witness carries `fwd`-image
            endpoint paths `ed`/`ed'` and squares `αP`/`αQ`
            connecting `P`/`Q` to the canonical `cP r`/`dP r`; a
            single `transport` along `αP`/`αQ` discharges that
            endpoint flexibility, leaving `R₂-closed-core` — the
            2-D bisimulation condition for the canonical paths,
            i.e. the genuine 2-D `bisim-transport` (the
            `pos-2D-R-of` analog). [route (a), in progress]
        -}
        R₂-closed-core :
          (x y : C) (r : R x y) (op : Op sig) →
          OutputsRel2D (arity sig op) R₂
                       (cong (destrD op) (cP r)) (cong (destrD op) (dP r))
        R₂-closed-core x y r op =
            transport
              (λ i → OutputsRel2D (arity sig op) R₂ (Ceq (~ i)) (Deq (~ i)))
              (rel2D (arity sig op) (isBis r op))
          where
            module HDC = HDeriveCoind hCoindCoalgC R isBis
            module HDD = HDeriveCoind hCoindCoalgD (LiftRel R) (bisim-transport R isBis)

            -- The `destr-ok` naturality square along the C-coinduction.
            sqC : PathP (λ j → destr-ok op x j ≡ destr-ok op y j)
                        (cong (destrD op) (cP r))
                        (cong (mapOutputs (arity sig op) (fwd carrier-eqv))
                              (cong (destrC op) (deriveCoind coindCoalgC R isBis r)))
            sqC j i = destr-ok op (deriveCoind coindCoalgC R isBis r i) j

            Ceq : PathP (λ j → destr-ok op x j ≡ destr-ok op y j)
                        (cong (destrD op) (cP r))
                        (realizeD (arity sig op) cP (isBis r op))
            Ceq = sqC ▷
              ( cong (cong (mapOutputs (arity sig op) (fwd carrier-eqv)))
                     (HDC.coind-realize op r)
              ∙ sym (C-nat (arity sig op) (isBis r op)) )

            -- D-side: no `fwd`-naturality square; the `destr-ok`
            -- connection comes from `bisim-transport`'s two `subst`s
            -- (`coind-realize` D + `realize-subst-nat`/`-right` + `D-nat`),
            -- packaged as `transp-path` over `destr-ok`.
            dox = destr-ok op x
            doy = destr-ok op y
            rD  = realizeD (arity sig op) dP (isBis r op)
            pd1 = sym dox ∙ refl
            pd2 = sym doy ∙ refl
            lifted' = OutputsRel-map (arity sig op) (fwd carrier-eqv) lw
                                     (isBis r op)
            W'D = subst (λ Z → OutputsRel (arity sig op) (LiftRel R)
                                 (mapOutputs (arity sig op) (fwd carrier-eqv)
                                             (destrC op x)) Z)
                        pd2 lifted'

            cdEq : cong (destrD op) (dP r) ≡ dox ∙ (rD ∙ sym doy)
            cdEq =
                HDD.coind-realize op (lw r)
              ∙ sym (realize-subst-nat (arity sig op) coindCoalgD (LiftRel R)
                                       (bisim-transport R isBis) pd1 W'D)
              ∙ subst-slide pd1 (realize (arity sig op) coindCoalgD (LiftRel R)
                                         (bisim-transport R isBis) W'D)
              ∙ cong (sym pd1 ∙_)
                     (sym (realize-subst-nat-right (arity sig op) coindCoalgD
                             (LiftRel R) (bisim-transport R isBis) pd2 lifted'))
              ∙ cong (sym pd1 ∙_)
                     (subst-slide-right pd2
                        (realize (arity sig op) coindCoalgD (LiftRel R)
                                 (bisim-transport R isBis) lifted'))
              ∙ cong (λ z → sym pd1 ∙ (z ∙ pd2))
                     (sym (D-nat (arity sig op) (isBis r op)))
              ∙ cong (_∙ (rD ∙ pd2)) (cong sym (∙-idr (sym dox)))
              ∙ cong (λ z → dox ∙ (rD ∙ z)) (∙-idr (sym doy))

            Deq : PathP (λ j → destr-ok op x j ≡ destr-ok op y j)
                        (cong (destrD op) (dP r))
                        (realizeD (arity sig op) dP (isBis r op))
            Deq = toPathP {A = λ j → dox j ≡ doy j}
                    ( transp-path dox doy (cong (destrD op) (dP r))
                    ∙ cong (λ z → sym dox ∙ (z ∙ doy)) cdEq
                    ∙ cong (sym dox ∙_) (∙assoc dox (rD ∙ sym doy) doy)
                    ∙ cong (λ z → sym dox ∙ (dox ∙ z)) (∙assoc rD (sym doy) doy)
                    ∙ cong (λ z → sym dox ∙ (dox ∙ (rD ∙ z))) (lCancel doy)
                    ∙ cong (λ z → sym dox ∙ (dox ∙ z)) (∙-idr rD)
                    ∙ sym (∙assoc (sym dox) dox rD)
                    ∙ cong (_∙ rD) (lCancel dox)
                    ∙ ∙-idl rD )

        R₂-closed : isBisim2D sig destrD R₂
        R₂-closed {a} {b} {P} {Q} (x , y , r , ed , ed' , αP , αQ) op =
          transport
            (λ k → OutputsRel2D (arity sig op) R₂
                                (cong (destrD op) (αP k)) (cong (destrD op) (αQ k)))
            (R₂-closed-core x y r op)

        coind-ok : ∀ {x y : C} (r : R x y) → cP r ≡ dP r
        coind-ok {x} {y} r =
          deriveCoind2D hCoindCoalgD R₂ R₂-closed
                        (x , y , r , refl , refl , refl , refl)
      {-
          Proposition 4.19 (4)
          `coind-ok-strict` of PUMPKIN Pi in coinductive form —
          the strict-equation analog of `elim_ok`. Obtained from
          `CoindOK.coind-ok`, i.e. from the path-level coinduction
          principle `deriveCoind2D` applied to the 2-D relation
          `R₂`. Its only non-`deriveCoind2D` input is the closure
          `R₂-closed` (the `pos-2D-R-of` analog).
      -}
      coind-ok-strict :
          (R : C → C → Type ℓ) (isBis : isBisim sig destrC R) →
          ∀ {x y : C} (r : R x y) →
          cong (fwd carrier-eqv)
               (deriveCoind coindCoalgC R isBis r)
            ≡ deriveCoind coindCoalgD (LiftRel R)
                          (bisim-transport R isBis)
                          (x , y , r , refl , refl)
      coind-ok-strict R isBis r = CoindOK.coind-ok R isBis r

      {-
          `coind-ok-strict` fully discharged, with *no*
          postulates, whenever the new carrier `D` is an h-set —
          the case the theoretical note flags as provable. Paths
          in an h-set are unique, so the two derived paths are
          equal directly (this bypasses both `deriveCoind2D` and
          the `R₂-closed` closure).
      -}
      coind-ok-strict-isSet :
          isSet D →
          (R : C → C → Type ℓ) (isBis : isBisim sig destrC R) →
          ∀ {x y : C} (r : R x y) →
          cong (fwd carrier-eqv)
               (deriveCoind coindCoalgC R isBis r)
            ≡ deriveCoind coindCoalgD (LiftRel R)
                          (bisim-transport R isBis)
                          (x , y , r , refl , refl)
      coind-ok-strict-isSet setD R isBis {x} {y} r =
          setD _ _
               (cong (fwd carrier-eqv) (deriveCoind coindCoalgC R isBis r))
               (deriveCoind coindCoalgD (LiftRel R) (bisim-transport R isBis)
                            (x , y , r , refl , refl))
