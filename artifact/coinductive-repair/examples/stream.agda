{-# OPTIONS --cubical --guardedness --safe #-}

{-
   Two coinductive presentations of streams over `X` — `Stream`
   (hd/tl) and `Stream'` (bundled observer) — each a final
   coalgebra for the polynomial functor `P X (λ _ → ⊤)`. Repair
   between them is the swap of universal properties forced by
   finality, worked both directly and through a coinductive
   configuration (`streamCoConfig`).
-}

module coinductive-repair.examples.stream where

open import Agda.Primitive
  using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import Agda.Primitive.Cubical
  using (I; i0; i1)
  renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_;
            primTransp to transp)
open import coinductive-repair.mtype  hiding (_×_)
open import coinductive-repair.coalg  hiding (_×_)
open import coinductive-repair.config
  using (CoSignature; CoConfig; HCoConfig; CoindCoalg; DestrAlgebra;
         coConfigToEquiv; mapOutputs; deriveCoind)
  renaming (isBisim to sigIsBisim)
open import coinductive-repair.coconfig-coalg-equiv
  using (MTypeSignature; MTypeArity; coalgBridgeBwd; bridgeˢBwd)

private variable
  ℓ : Level

{- Local unit and pairs: ⊤ is the position type, `_×_` the bundled
   observation for Stream', both at level ℓ. -}

record ⊤ {ℓ : Level} : Type ℓ where
  constructor tt

record _×_ {ℓ : Level} (A B : Type ℓ) : Type ℓ where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_ public

data _⊎_ {ℓ : Level} (A B : Type ℓ) : Type ℓ where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

{- Stream / Stream' and their polynomial coalgebra structures. -}

module _ {X : Type ℓ} where

  -- Shared position type: each shape `x : X` admits exactly one
  -- position, corresponding to the tail observation.
  Obs : X → Type ℓ
  Obs _ = ⊤

  record Stream (X : Type ℓ) : Type ℓ where
    coinductive
    field
      hd : X
      tl : Stream X
  open Stream public

  record Stream' (X : Type ℓ) : Type ℓ where
    coinductive
    field
      obs : X × Stream' X
  open Stream' public

  cons : X → Stream X → Stream X
  hd (cons x s) = x
  tl (cons x s) = s

  cons' : X → Stream' X → Stream' X
  obs (cons' x s) = (x , s)

  streamComp : (s : Stream X) → cons (hd s) (tl s) ≡ s
  hd (streamComp s i) = hd s
  tl (streamComp s i) = tl s

  streamComp' : (s : Stream' X) → cons' (π₁ (obs s)) (π₂ (obs s)) ≡ s
  obs (streamComp' s i) = obs s

  {- 
    Example 4.2 (Stream Coalgebra); `outStream` is also used in Example 4.8
    Polynomial coalgebra structures: `outStream` / `outStream'`
    rewrite the destructors into the `Σ X (⊤ → _)` shape. -}

  outStream : Stream X → P X Obs (Stream X)
  outStream s = (hd s , λ _ → tl s)

  outStream' : Stream' X → P X Obs (Stream' X)
  outStream' s = (π₁ (obs s) , λ _ → π₂ (obs s))

  StreamCoalg : P-Coalg X Obs
  StreamCoalg = (Stream X , outStream)

  Stream'Coalg : P-Coalg X Obs
  Stream'Coalg = (Stream' X , outStream')

  {- Example 4.8 (Final Stream Coalgebra): `Stream-corec`.
     Corecursors: pull the source coalgebra apart with `CoalgOut`,
     rebuild by copattern matching. -}

  Stream-corec : (C : P-Coalg X Obs) → CoalgCarrier C → Stream X
  hd (Stream-corec C c) = fst (CoalgOut C c)
  tl (Stream-corec C c) = Stream-corec C (snd (CoalgOut C c) tt)

  Stream'-corec : (C : P-Coalg X Obs) → CoalgCarrier C → Stream' X
  obs (Stream'-corec C c) =
    fst (CoalgOut C c) , Stream'-corec C (snd (CoalgOut C c) tt)

  {-
    Example 4.13 (Coalgebraic Repair with Stream and Stream')
    `cons` written with the corecursor (the universal property).
     The seed coalgebra `consSeed` is stated once, against an
     abstract coalgebra `C`: the seed `inl (x , e)` emits `x` and
     steps to `inr e`, which then replays `e` through the
     structure map `CoalgOut C`. The carrier appears only through
     that structure map, so the defining data is shared verbatim
     by both sides; repair is the swap
     `Stream-corec ↦ Stream'-corec`, `StreamCoalg ↦ Stream'Coalg`
     — exactly the two pieces the configuration pairs up. -}
  consSeed : (C : P-Coalg X Obs) → P-Coalg X Obs
  consSeed C = ((X × E) ⊎ E , γ)
    where
      E = CoalgCarrier C
      γ : (X × E) ⊎ E → P X Obs ((X × E) ⊎ E)
      γ (inl (y , t)) = (y , λ _ → inr t)
      γ (inr t)       = (fst (CoalgOut C t) , λ _ → inr (snd (CoalgOut C t) tt))

  cons-M : X → Stream X → Stream X
  cons-M x s = Stream-corec (consSeed StreamCoalg) (inl (x , s))

  cons'-M : X → Stream' X → Stream' X
  cons'-M x s = Stream'-corec (consSeed Stream'Coalg) (inl (x , s))

  {- 
    Example 4.11 (Bisimulation on Streams)
    1-D coinduction on each carrier: a bisimulation (heads agree,
     tails related) is discharged into path equality by copattern
     matching. -}

  record StreamBis (R : Stream X → Stream X → Type ℓ)
                   (s t : Stream X) : Type ℓ where
    field
      bhd : hd s ≡ hd t
      btl : R (tl s) (tl t)
  open StreamBis public

  -- Example 4.11 (Bisimulation on Streams): `Stream-coind`.
  Stream-coind : (R : Stream X → Stream X → Type ℓ)
               → (∀ {s t} → R s t → StreamBis R s t)
               → ∀ {s t} → R s t → s ≡ t
  hd (Stream-coind R isBis r i) = bhd (isBis r) i
  tl (Stream-coind R isBis r i) =
    Stream-coind R isBis (btl (isBis r)) i

  record Stream'Bis (R : Stream' X → Stream' X → Type ℓ)
                    (s t : Stream' X) : Type ℓ where
    field
      bo₁ : π₁ (obs s) ≡ π₁ (obs t)
      bo₂ : R (π₂ (obs s)) (π₂ (obs t))
  open Stream'Bis public

  Stream'-coind : (R : Stream' X → Stream' X → Type ℓ)
                → (∀ {s t} → R s t → Stream'Bis R s t)
                → ∀ {s t} → R s t → s ≡ t
  obs (Stream'-coind R isBis r i) =
    bo₁ (isBis r) i , Stream'-coind R isBis (bo₂ (isBis r)) i

  {- 
    Example 4.13 (Coalgebraic Repair with Stream and Stream')
    `streamComp` written with the coinduction principle (the
     universal property for proofs): the bisimulation `etaR`
     relating streams with equal head and tail, with one-step
     closure `etaStep`, discharged at the reflexivity seed. Repair
     is the swap `Stream-coind ↦ Stream'-coind`, `hd`/`tl` for
     `obs`, the seed `(refl , refl)` untouched. -}
  etaR : Stream X → Stream X → Type ℓ
  etaR a b = (hd a ≡ hd b) × (tl a ≡ tl b)

  etaStep : ∀ {a b} → etaR a b → StreamBis etaR a b
  etaStep r = record { bhd = π₁ r
                     ; btl = ((λ i → hd (π₂ r i)) , (λ i → tl (π₂ r i))) }

  streamComp-M : (s : Stream X) → cons (hd s) (tl s) ≡ s
  streamComp-M s = Stream-coind etaR etaStep (refl , refl)

  etaR' : Stream' X → Stream' X → Type ℓ
  etaR' a b = (π₁ (obs a) ≡ π₁ (obs b)) × (π₂ (obs a) ≡ π₂ (obs b))

  etaStep' : ∀ {a b} → etaR' a b → Stream'Bis etaR' a b
  etaStep' r = record { bo₁ = π₁ r
                      ; bo₂ = ((λ i → π₁ (obs (π₂ r i)))
                             , (λ i → π₂ (obs (π₂ r i)))) }

  streamComp'-M : (s : Stream' X) → cons' (π₁ (obs s)) (π₂ (obs s)) ≡ s
  streamComp'-M s = Stream'-coind etaR' etaStep' (refl , refl)

{- Finality of Stream -}
  -- Example 4.5 (Stream Homomorphism)
  -- Example 4.8 (Final Stream Coalgebra): `Stream-corec C` is a
  -- homomorphism, definitionally.
  Stream-corec-isHom : (C : P-Coalg X Obs)
                     → isCoalgHom C StreamCoalg (Stream-corec C)
  Stream-corec-isHom C = refl

  module StreamUniq (C : P-Coalg X Obs)
                    (h : CoalgCarrier C → Stream X)
                    (h-hom : isCoalgHom C StreamCoalg h) where
    private
      D = CoalgCarrier C
      e = CoalgOut C
      co : D → Stream X
      co = Stream-corec C

      -- Pointwise homomorphism square: at i = 0 it is
      -- `(fst (e c), λ _ → h (snd (e c) tt))`, at i = 1 it is
      -- `outStream (h c) = (hd (h c), λ _ → tl (h c))`.
      h-pt : (c : D) → P-mor h (e c) ≡ outStream (h c)
      h-pt c i = h-hom i c

      h-hd : (c : D) → fst (e c) ≡ hd (h c)
      h-hd c i = fst (h-pt c i)

      h-tl : (c : D) → h (snd (e c) tt) ≡ tl (h c)
      h-tl c i = snd (h-pt c i) tt

    data Link : Stream X → Stream X → Type ℓ where
      link : (c : D) → Link (h c) (co c)

    isBis : ∀ {s t} → Link s t → StreamBis Link s t
    bhd (isBis (link c)) = sym (h-hd c)
    btl (isBis (link c)) =
      transport (λ i → Link (h-tl c i) (co (snd (e c) tt)))
                (link (snd (e c) tt))

    pwEq : (c : D) → h c ≡ co c
    pwEq c = Stream-coind Link isBis (link c)

    funEq : h ≡ co
    funEq = funExt pwEq

  -- Example 4.8 (Final Stream Coalgebra): `Stream` is final.
  Stream-isFinal : isFinal StreamCoalg
  Stream-isFinal C =
      (Stream-corec C , Stream-corec-isHom C)
    , λ h' h'-hom → sym (StreamUniq.funEq C h' h'-hom)

{- Finality of Stream' -}

  Stream'-corec-isHom : (C : P-Coalg X Obs)
                      → isCoalgHom C Stream'Coalg (Stream'-corec C)
  Stream'-corec-isHom C = refl

  module Stream'Uniq (C : P-Coalg X Obs)
                     (h : CoalgCarrier C → Stream' X)
                     (h-hom : isCoalgHom C Stream'Coalg h) where
    private
      D = CoalgCarrier C
      e = CoalgOut C
      co : D → Stream' X
      co = Stream'-corec C

      h-pt : (c : D) → P-mor h (e c) ≡ outStream' (h c)
      h-pt c i = h-hom i c

      h-π₁ : (c : D) → fst (e c) ≡ π₁ (obs (h c))
      h-π₁ c i = fst (h-pt c i)

      h-π₂ : (c : D) → h (snd (e c) tt) ≡ π₂ (obs (h c))
      h-π₂ c i = snd (h-pt c i) tt

    data Link : Stream' X → Stream' X → Type ℓ where
      link : (c : D) → Link (h c) (co c)

    isBis : ∀ {s t} → Link s t → Stream'Bis Link s t
    bo₁ (isBis (link c)) = sym (h-π₁ c)
    bo₂ (isBis (link c)) =
      transport (λ i → Link (h-π₂ c i) (co (snd (e c) tt)))
                (link (snd (e c) tt))

    pwEq : (c : D) → h c ≡ co c
    pwEq c = Stream'-coind Link isBis (link c)

    funEq : h ≡ co
    funEq = funExt pwEq

  Stream'-isFinal : isFinal Stream'Coalg
  Stream'-isFinal C =
      (Stream'-corec C , Stream'-corec-isHom C)
    , λ h' h'-hom → sym (Stream'Uniq.funEq C h' h'-hom)

  {- Coalgebraic repair between Stream and Stream': the coinductive
     dual of the `nat-bin-eqv` example. Finality for the one
     functor hands us a coalgebra isomorphism, and repair is the
     dual swap of corecursors — forced, not chosen. -}

  {- The isomorphism, as the two corecursors across the carriers
     (dual of `fromNat`/`toNat`). -}
  toStream' : Stream X → Stream' X
  toStream' = Stream'-corec StreamCoalg

  toStream : Stream' X → Stream X
  toStream = Stream-corec Stream'Coalg

  -- Example 4.5 (Stream Homomorphism)
  -- Both directions are coalgebra homs (squares are `refl`).
  toStream'-hom : isCoalgHom StreamCoalg Stream'Coalg toStream'
  toStream'-hom = Stream'-corec-isHom StreamCoalg

  toStream-hom : isCoalgHom Stream'Coalg StreamCoalg toStream
  toStream-hom = Stream-corec-isHom Stream'Coalg

  {- The round-trips are the identity: both the composite and `id`
     are coalgebra homs, so function-level uniqueness identifies
     them with the canonical self-corecursor. -}
  iso-leftInv : (s : Stream X) → toStream (toStream' s) ≡ s
  iso-leftInv s =
      StreamUniq.pwEq StreamCoalg (λ s' → toStream (toStream' s')) gf-hom s
    ∙ sym (StreamUniq.pwEq StreamCoalg (λ s' → s') refl s)
    where
      gf-hom : isCoalgHom StreamCoalg StreamCoalg (λ s' → toStream (toStream' s'))
      gf-hom = ∘-isCoalgHom {C₁ = StreamCoalg} {C₂ = Stream'Coalg} {C₃ = StreamCoalg}
                            {f = toStream'} {g = toStream}
                            toStream'-hom toStream-hom

  iso-rightInv : (s : Stream' X) → toStream' (toStream s) ≡ s
  iso-rightInv s =
      Stream'Uniq.pwEq Stream'Coalg (λ s' → toStream' (toStream s')) fg-hom s
    ∙ sym (Stream'Uniq.pwEq Stream'Coalg (λ s' → s') refl s)
    where
      fg-hom : isCoalgHom Stream'Coalg Stream'Coalg (λ s' → toStream' (toStream s'))
      fg-hom = ∘-isCoalgHom {C₁ = Stream'Coalg} {C₂ = StreamCoalg} {C₃ = Stream'Coalg}
                            {f = toStream} {g = toStream'}
                            toStream-hom toStream'-hom

  {- Section 4.3, after Proposition 4.19: `corecSwap'` is the
     Stream instance of `corec_ok`.
     Swap of universal properties: the corecursor into `Stream'`
     factors through the corecursor into `Stream` post-composed
     with the iso, forced by uniqueness. Repair of any corecursive
     program is exactly this swap. -}
  corecSwap' : (C : P-Coalg X Obs) (c : CoalgCarrier C)
             → Stream'-corec C c ≡ toStream' (Stream-corec C c)
  corecSwap' C c =
    sym (Stream'Uniq.pwEq C (λ c' → toStream' (Stream-corec C c')) hom c)
    where
      hom : isCoalgHom C Stream'Coalg (λ c' → toStream' (Stream-corec C c'))
      hom = ∘-isCoalgHom {C₁ = C} {C₂ = StreamCoalg} {C₃ = Stream'Coalg}
                         {f = Stream-corec C} {g = toStream'}
                         (Stream-corec-isHom C) toStream'-hom

  {- Repair coherence for `cons` (dual of `constr_ok`): the iso
     commutes with the constructor, on the nose. -}
  consCoh : (x : X) (s : Stream X)
          → toStream' (cons x s) ≡ cons' x (toStream' s)
  obs (consCoh x s i) = (x , toStream' s)

  {- Proof-level repair: the η law `streamComp` is repaired by
     swapping `cons` for `cons'` via `consCoh` and conjugating the
     same proof by the iso — no new coinduction. -}
  streamComp'-repaired : (s : Stream X)
                      → cons' (hd s) (toStream' (tl s)) ≡ toStream' s
  streamComp'-repaired s =
    sym (consCoh (hd s) (tl s)) ∙ cong toStream' (streamComp s)

  {- 
    Example 4.20 (Stream and Stream' Repair via Configurations)
    The same repair, packaged as a coinductive configuration
     (`CoConfig`) over the M-type signature for `(X , Obs)` — the
     syntactic object a repair algorithm walks. -}

  -- The shared signature: one destructor exposing a head and a
  -- ⊤-indexed recursive tail.
  StreamSig : CoSignature
  StreamSig = MTypeSignature X Obs

  -- Each presentation's coalgebra structure + finality proof
  -- becomes a `CoindCoalg`, via the bridge `coalgBridgeBwd`.
  streamCoindCoalg : CoindCoalg StreamSig (Stream X)
  streamCoindCoalg = coalgBridgeBwd (outStream , Stream-isFinal)

  stream'CoindCoalg : CoindCoalg StreamSig (Stream' X)
  stream'CoindCoalg = coalgBridgeBwd (outStream' , Stream'-isFinal)

  -- The configuration relating the two presentations.
  streamCoConfig : CoConfig StreamSig (Stream X) (Stream' X)
  streamCoConfig = record
    { coindCoalgC = streamCoindCoalg
    ; coindCoalgD = stream'CoindCoalg
    }

  {- Example 4.20 (`unfold`)
     A program written against a single configuration component:
     abstract in the `CoindCoalg`, it names neither `Stream` nor
     `Stream'`. -}
  unfold : {E : Type ℓ} → CoindCoalg StreamSig E
         → {S : Type ℓ} → DestrAlgebra StreamSig S → S → E
  unfold ind = CoindCoalg.corec ind

  {- Instantiating on the `Stream` side; the repair is the same
     program with the component swapped `coindCoalgC ↦ coindCoalgD`. -}
  unfoldStream  : {S : Type ℓ} → DestrAlgebra StreamSig S → S → Stream  X
  unfoldStream  = unfold streamCoindCoalg

  unfoldStream' : {S : Type ℓ} → DestrAlgebra StreamSig S → S → Stream' X
  unfoldStream' = unfold stream'CoindCoalg      -- repair: swap the component

  -- Exchanging the two components gives the reverse repair.
  streamCoConfigSwap : CoConfig StreamSig (Stream' X) (Stream X)
  streamCoConfigSwap = record
    { coindCoalgC = stream'CoindCoalg
    ; coindCoalgD = streamCoindCoalg
    }

  -- The repair map and its inverse: the equivalences the two
  -- configurations determine.
  streamRepair  : Stream  X ≃ Stream' X
  streamRepair  = coConfigToEquiv streamCoConfig

  streamRepair⁻ : Stream' X ≃ Stream  X
  streamRepair⁻ = coConfigToEquiv streamCoConfigSwap

  {- Example 4.20 (`consVia`, `consCfg`, `consCfg'`)
     The running programs repaired through the configuration.

     `consVia` writes `cons` against an abstract component: the
     seed coalgebra's `inl` branch is shared verbatim, and its
     `inr` branch re-reads a carrier element through the
     component's own destructor. Instantiating at the C-component
     gives `cons` on `Stream`; the repair is the same program
     instantiated at the swapped component (`corec_ok` in action). -}
  consVia : {E : Type ℓ} (ind : CoindCoalg StreamSig E) → X → E → E
  consVia {E} ind x e = unfold ind δ (inl (x , e))
    where
      δ : DestrAlgebra StreamSig ((X × E) ⊎ E)
      δ op (inl (y , t)) = y , (λ _ → inr t) , _
      δ op (inr t)       = mapOutputs (MTypeArity X Obs op) inr
                                      (CoindCoalg.destr ind op t)

  consCfg  : X → Stream  X → Stream  X
  consCfg  = consVia streamCoindCoalg
  consCfg' : X → Stream' X → Stream' X
  consCfg' = consVia stream'CoindCoalg   -- repair: swap the component

  {- Example 4.20 (`streamCompCfg`, `streamCompCfg'`)
     `streamComp` proved with the configuration's derived
     coinduction principle: the same relations `etaR`/`etaR'`,
     with the one-step closure re-expressed in the configuration's
     syntactic bisimulation format (`isBisim`). The `subst` in
     `OutputsRel`'s head clause is over a definitionally constant
     family and is cancelled by `transportRefl`. -}
  etaRIsBisim : sigIsBisim StreamSig (CoindCoalg.destr streamCoindCoalg) etaR
  etaRIsBisim {a} {b} r op =
      π₁ r , (λ d → cong hd q , cong tl q) , _
    where
      q : transport refl (tl a) ≡ tl b
      q = transportRefl (tl a) ∙ π₂ r

  -- Example 4.20: `streamComp` via the configuration's `deriveCoind`.
  streamCompCfg : (s : Stream X) → cons (hd s) (tl s) ≡ s
  streamCompCfg s =
    deriveCoind streamCoindCoalg etaR
      (λ {x} {y} r → etaRIsBisim {x} {y} r) (refl , refl)

  etaRIsBisim' : sigIsBisim StreamSig (CoindCoalg.destr stream'CoindCoalg) etaR'
  etaRIsBisim' {a} {b} r op =
      π₁ r , (λ d → cong (λ z → π₁ (obs z)) q , cong (λ z → π₂ (obs z)) q) , _
    where
      q : transport refl (π₂ (obs a)) ≡ π₂ (obs b)
      q = transportRefl (π₂ (obs a)) ∙ π₂ r

  streamCompCfg' : (s : Stream' X) → cons' (π₁ (obs s)) (π₂ (obs s)) ≡ s
  streamCompCfg' s =
    deriveCoind stream'CoindCoalg etaR'
      (λ {x} {y} r → etaRIsBisim' {x} {y} r) (refl , refl)

  {- Example 4.20 (`consCfg'-head`, `consCfg'-next`)
     The repaired terms genuinely compute: observing them reduces
     the configuration scaffolding away, leaving native `Stream'`
     data. Each equation holds by `refl` (definitionally), and the
     module is `--safe`, so no axiom stands between the repaired
     term and its normal form.

     For the repaired program `consCfg'` both sides mention only
     `Stream'`: the head observation is the pushed element `x`, and
     the head of the tail is `s`'s own head. -}
  consCfg'-head : (x : X) (s : Stream' X)
                → π₁ (obs (consCfg' x s)) ≡ x
  consCfg'-head x s = refl

  consCfg'-next : (x : X) (s : Stream' X)
                → π₁ (obs (π₂ (obs (consCfg' x s)))) ≡ π₁ (obs s)
  consCfg'-next x s = refl

  {- Even the full repair equivalence `streamRepair`, assembled
     through `coConfigToEquiv` and the finality bridges, reduces
     under observation: transporting a `Stream` and reading it back
     recovers the original observations. -}
  streamRepair-head : (s : Stream X)
                    → π₁ (obs (_≃_.fwd streamRepair s)) ≡ hd s
  streamRepair-head s = refl

  streamRepair-next : (s : Stream X)
                    → π₁ (obs (π₂ (obs (_≃_.fwd streamRepair s)))) ≡ hd (tl s)
  streamRepair-next s = refl

  {- Section 4.3, after Definition 4.15: Stream is a set when its
     element type is a set (`isSet-Stream`), hence homotopy-final.

     Homotopy-finality over an h-set.

     When the element type `X` is an h-set, `Stream X` is not just
     final but *homotopy*-final (`isHFinal`). The route:
     `Stream X` is a retract of the function space `Nat → X`, hence
     itself a set; the homomorphism witness `isCoalgHom C StreamCoalg h`
     is then a path in a set-valued function space, hence a
     proposition; so the function-level uniqueness of
     `Stream-isFinal` upgrades to Σ-level uniqueness. -}

  data Nat : Type ℓ where
    zeroN : Nat
    sucN  : Nat → Nat

  private
    index : Stream X → Nat → X
    index s zeroN    = hd s
    index s (sucN n) = index (tl s) n

    tabulate : (Nat → X) → Stream X
    hd (tabulate f) = f zeroN
    tl (tabulate f) = tabulate (λ n → f (sucN n))

    tabulate-index : (s : Stream X) → tabulate (index s) ≡ s
    hd (tabulate-index s i) = hd s
    tl (tabulate-index s i) = tabulate-index (tl s) i

  isSet-Stream : isSet X → isSet (Stream X)
  isSet-Stream setX =
    isSetRetract index tabulate tabulate-index (isSetΠ (λ _ → setX))

  -- `P X Obs (Stream X) = Σ X (λ _ → ⊤ → Stream X)` is a set, so the
  -- homomorphism witness — a path in `D → P X Obs (Stream X)` — is a
  -- proposition.
  isProp-StreamHom : isSet X → (C : P-Coalg X Obs)
                     (h : CoalgCarrier C → Stream X)
                   → isProp (isCoalgHom C StreamCoalg h)
  isProp-StreamHom setX C h =
    isSetΠ (λ _ → isSetΣconst setX (isSetΠ (λ _ → isSet-Stream setX)))
           (λ x → P-mor h (CoalgOut C x)) (λ x → outStream (h x))

  Stream-isHFinal : isSet X → isHFinal StreamCoalg
  Stream-isHFinal setX C =
      (Stream-corec C , Stream-corec-isHom C) , contract
    where
      contract : (g : CoalgHom C StreamCoalg)
               → (Stream-corec C , Stream-corec-isHom C) ≡ g
      contract (h' , w') i = funP i , wP i
        where
          funP : Stream-corec C ≡ h'
          funP = sym (StreamUniq.funEq C h' w')
          wP : PathP (λ j → isCoalgHom C StreamCoalg (funP j))
                     (Stream-corec-isHom C) w'
          wP = isProp→PathP
                 (λ j → isProp-StreamHom setX C (funP j))
                 (Stream-corec-isHom C) w'

  {- The same route for `Stream'`: it is a set because it is a
     retract of `Stream` (via the isomorphism above), so its
     hom-witnesses are propositions and finality upgrades to
     homotopy-finality. -}

  isSet-Stream' : isSet X → isSet (Stream' X)
  isSet-Stream' setX =
    isSetRetract toStream toStream' iso-rightInv (isSet-Stream setX)

  isProp-Stream'Hom : isSet X → (C : P-Coalg X Obs)
                      (h : CoalgCarrier C → Stream' X)
                    → isProp (isCoalgHom C Stream'Coalg h)
  isProp-Stream'Hom setX C h =
    isSetΠ (λ _ → isSetΣconst setX (isSetΠ (λ _ → isSet-Stream' setX)))
           (λ x → P-mor h (CoalgOut C x)) (λ x → outStream' (h x))

  Stream'-isHFinal : isSet X → isHFinal Stream'Coalg
  Stream'-isHFinal setX C =
      (Stream'-corec C , Stream'-corec-isHom C) , contract
    where
      contract : (g : CoalgHom C Stream'Coalg)
               → (Stream'-corec C , Stream'-corec-isHom C) ≡ g
      contract (h' , w') i = funP i , wP i
        where
          funP : Stream'-corec C ≡ h'
          funP = sym (Stream'Uniq.funEq C h' w')
          wP : PathP (λ j → isCoalgHom C Stream'Coalg (funP j))
                     (Stream'-corec-isHom C) w'
          wP = isProp→PathP
                 (λ j → isProp-Stream'Hom setX C (funP j))
                 (Stream'-corec-isHom C) w'

  {- Section 4.3, after Proposition 4.19 (`coind_ok` for Stream/Stream')
     The running pair over an h-set element type assembles into a
     *homotopy* coinductive configuration: both presentations are
     homotopy-final, and the strong bridge `bridgeˢBwd` packages
     each as an `HCoindCoalg`. This is the configuration over which
     `coind_ok` holds for the Stream/Stream' example. -}
  streamHCoConfig : isSet X → HCoConfig StreamSig (Stream X) (Stream' X)
  streamHCoConfig setX = record
    { hCoindCoalgC = bridgeˢBwd (outStream  , Stream-isHFinal  setX)
    ; hCoindCoalgD = bridgeˢBwd (outStream' , Stream'-isHFinal setX)
    }


