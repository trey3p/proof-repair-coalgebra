{- `-WnoUnsupportedIndexedMatch`: matches on `Fin` at compound indices
   (the operation labels) need injectivity of `succ`, which Cubical
   Agda cannot yet run; harmless here, as nothing on the cubical side
   imports this file. -}
{-# OPTIONS --without-K --cubical-compatible -WnoUnsupportedIndexedMatch #-}

open import common
open import palg
open import inductive-repair.indspec
open import inductive-repair.config
open import inductive-repair.repair-ops
open import inductive-repair.wtype-config hiding (A ; B ; Op ; arity)
open import inductive-repair.bridge

open Signature
open _≃_

{-
    Motivating example: Peano naturals `ℕ` vs. unique-representation
    binary naturals `Bin`.

    Both carriers are shown to be initial algebras for `P X = 1 + X`,
    the recursor/eliminator interface is derived from initiality alone
    (`recNat`, `indNatIndAlg` and their β-rules), and repair is the
    swap of universal properties. The explicit equivalence
    `nat-bin-eqv : ℕ ≃ Bin` realizes the unique algebra isomorphism,
    and `repair-Π` transports theorems across it.
-}
module inductive-repair.examples.nat {ℓ : Level} where

  {- Peano signature: `zero` (nullary) and `succ` (one recursive child). -}
  sig : Signature {ℓ}
  sig .Op = Fin (succ (succ zero))
  sig .arity zero       = Done
  sig .arity (suc zero) = Rec ⊤ Done

  algNat : ConstrAlgebra sig (ℕ {ℓ})
  algNat zero       _        = zero
  algNat (suc zero) (r , _)  = succ (r tt)

  indNat : Induction sig algNat
  indNat motive cases zero     = cases zero tt tt
  indNat motive cases (succ n) =
      cases (suc zero) ((λ _ → n) , tt)
                       ((λ _ → indNat motive cases n) , tt)

  betaNat : BetaLaw sig indNat
  betaNat motive cases zero       _ = refl
  betaNat motive cases (suc zero) _ = refl

  indAlgN : IndAlg sig (ℕ {ℓ})
  indAlgN = record { algebra = algNat ; ind = indNat ; beta = betaNat }

  {-
      Binary naturals. `Pos` is the positive binary numbers
      (`one`, `pb0 p` = 2p, `pb1 p` = 2p+1); `Bin` adds a separate
      zero, so representations are unique.
  -}
  data Pos : Type ℓ where
    one : Pos
    pb0 : Pos → Pos
    pb1 : Pos → Pos

  data Bin : Type ℓ where
    bzero : Bin
    bpos  : Pos → Bin

  pSucc : Pos → Pos
  pSucc one     = pb0 one
  pSucc (pb0 q) = pb1 q
  pSucc (pb1 q) = pb0 (pSucc q)

  binSucc : Bin → Bin
  binSucc bzero    = bpos one
  binSucc (bpos p) = bpos (pSucc p)

  binDouble : Bin → Bin
  binDouble bzero    = bzero
  binDouble (bpos p) = bpos (pb0 p)

  {- Conversions ℕ ↔ Bin. -}
  double : ℕ {ℓ} → ℕ {ℓ}
  double zero     = zero
  double (succ n) = succ (succ (double n))

  pToNat : Pos → ℕ {ℓ}
  pToNat one     = succ zero
  pToNat (pb0 p) = double (pToNat p)
  pToNat (pb1 p) = succ (double (pToNat p))

  toNat : Bin → ℕ {ℓ}
  toNat bzero    = zero
  toNat (bpos p) = pToNat p

  fromNat : ℕ {ℓ} → Bin
  fromNat zero     = bzero
  fromNat (succ n) = binSucc (fromNat n)

  {- Auxiliary lemmas for the round trips. -}
  binDouble-binSucc : (b : Bin) →
                      binDouble (binSucc b) ≡ binSucc (binSucc (binDouble b))
  binDouble-binSucc bzero    = refl
  binDouble-binSucc (bpos p) = refl

  fromNat-double : (n : ℕ {ℓ}) →
                   fromNat (double n) ≡ binDouble (fromNat n)
  fromNat-double zero     = refl
  fromNat-double (succ m) =
      ap (λ x → binSucc (binSucc x)) (fromNat-double m)
    • ! (binDouble-binSucc (fromNat m))

  fromNat-pToNat : (p : Pos) → fromNat (pToNat p) ≡ bpos p
  fromNat-pToNat one     = refl
  fromNat-pToNat (pb0 q) =
      fromNat-double (pToNat q) • ap binDouble (fromNat-pToNat q)
  fromNat-pToNat (pb1 q) =
      ap binSucc (fromNat-double (pToNat q) • ap binDouble (fromNat-pToNat q))

  pToNat-pSucc : (p : Pos) → pToNat (pSucc p) ≡ succ (pToNat p)
  pToNat-pSucc one     = refl
  pToNat-pSucc (pb0 q) = refl
  pToNat-pSucc (pb1 q) = ap double (pToNat-pSucc q)

  toNat-binSucc : (b : Bin) → toNat (binSucc b) ≡ succ (toNat b)
  toNat-binSucc bzero    = refl
  toNat-binSucc (bpos p) = pToNat-pSucc p

  {- Round-trip witnesses. -}
  fromNat-toNat : (b : Bin) → fromNat (toNat b) ≡ b
  fromNat-toNat bzero    = refl
  fromNat-toNat (bpos p) = fromNat-pToNat p

  toNat-fromNat : (n : ℕ {ℓ}) → toNat (fromNat n) ≡ n
  toNat-fromNat zero     = refl
  toNat-fromNat (succ m) =
      toNat-binSucc (fromNat m) • ap succ (toNat-fromNat m)

  {- 
    Example 3.12 (Motivating Example with Algebra Equivalence)
    The equivalence and the configuration built from it.
     -}
  nat-bin-eqv : ℕ {ℓ} ≃ Bin
  nat-bin-eqv .f = fromNat
  nat-bin-eqv .g = toNat
  nat-bin-eqv .η = toNat-fromNat
  nat-bin-eqv .h = toNat
  nat-bin-eqv .ε = fromNat-toNat

  natConfig : Config sig (ℕ {ℓ}) Bin
  natConfig = equivToConfig indAlgN nat-bin-eqv

  {-
      Example 3.3 (Nat Algebra)
      Example 3.8 (Motivating Example with Initial Algebras)
      ℕ and Bin as h-initial algebras for `P X = 1 + X`, taking
      `A = Bool`, `B true = ⊥`, `B false = ⊤`. Each carrier gets an
      `IndAlg` for the W-type signature; `bridgeFwd` upgrades it to a
      genuine `isInitAlg` (contractible hom-spaces).
  -}
  PolyB : Bool {ℓ} → Type ℓ
  PolyB true  = ⊥ {ℓ}
  PolyB false = ⊤ {ℓ}

  Wsig : Signature {ℓ}
  Wsig = WTypeSignature {ℓ} (Bool {ℓ}) PolyB

  {- Example 3.3 (Nat Algebra): the `1 + ℕ → ℕ` algebra in W-type shape. -}
  supℕ : ConstrAlgebra Wsig (ℕ {ℓ})
  supℕ _ (true  , (u , _)) = zero
  supℕ _ (false , (u , _)) = succ (u tt)

  indℕ : Induction Wsig supℕ
  indℕ motive cases zero     = cases tt (true  , ((λ ()) , tt)) ((λ ()) , tt)
  indℕ motive cases (succ m) =
      cases tt (false , ((λ _ → m) , tt)) ((λ _ → indℕ motive cases m) , tt)

  {-
      β: the successor shape reduces definitionally; at the zero shape
      the discarded child family over `⊥` is matched up to `ext (λ ())`.
  -}
  betaℕ : BetaLaw Wsig indℕ
  betaℕ motive cases _ (false , (u , tt)) = refl
  betaℕ motive cases _ (true  , (u , tt)) = ap Ψ pth
    where
      Ψ : Σ (⊥ {ℓ} → ℕ {ℓ}) (λ u' → (b : ⊥ {ℓ}) → motive (u' b)) →
          motive (supℕ tt (true , (u , tt)))
      Ψ (u' , ih') = cases tt (true , (u' , tt)) (ih' , tt)
      pth : ((λ ()) , (λ ())) ≡ (u , (λ b → indℕ motive cases (u b)))
      pth = Σ-≡-intro {B = λ u' → (b : ⊥ {ℓ}) → motive (u' b)}
                      (ext (λ ())) (ext (λ ()))

  wIndAlgℕ : WTypeIndAlg {ℓ} (Bool {ℓ}) PolyB (ℕ {ℓ})
  wIndAlgℕ = record { algebra = supℕ ; ind = indℕ ; beta = betaℕ }

  {- Example 3.8 (`NatInit`): ℕ is an initial algebra for `P X = 1 + X`. -}
  ℕ-InitAlgOn : InitAlgOn (Bool {ℓ}) PolyB (ℕ {ℓ})
  ℕ-InitAlgOn = bridgeFwd wIndAlgℕ

  ℕ-InitAlg : InitAlg {ℓ} {ℓ} {ℓ} (Bool {ℓ}) PolyB
  ℕ-InitAlg = (ℕ {ℓ} , InitAlgOn.sup ℕ-InitAlgOn) , InitAlgOn.isInit ℕ-InitAlgOn

  {- Example 3.3 (Nat Algebra): the native `1 + Bin → Bin` algebra. -}
  supBin : P (Bool {ℓ}) PolyB Bin → Bin
  supBin (true  , u) = bzero
  supBin (false , u) = binSucc (u tt)

  {-
      Initiality of Bin, inherited from ℕ through the equivalence:
      transport the `IndAlg`, bridge to `isInitAlg`, then move the
      result to the native `supBin` along `sup-tr≡native`.
  -}
  wIndAlgBin : WTypeIndAlg {ℓ} (Bool {ℓ}) PolyB Bin
  wIndAlgBin = transportIndAlg wIndAlgℕ nat-bin-eqv

  Bin-InitAlgOn-tr : InitAlgOn (Bool {ℓ}) PolyB Bin
  Bin-InitAlgOn-tr = bridgeFwd wIndAlgBin

  sup-tr≡native : InitAlgOn.sup Bin-InitAlgOn-tr ≡ supBin
  sup-tr≡native =
      ext (λ { (true  , u) → refl
             ; (false , u) → ap binSucc (fromNat-toNat (u tt)) })

  Bin-InitAlgOn : InitAlgOn (Bool {ℓ}) PolyB Bin
  Bin-InitAlgOn = record
    { sup    = supBin
    ; isInit = tpt (λ s → isInitAlg (Bin , s))
                   sup-tr≡native
                   (InitAlgOn.isInit Bin-InitAlgOn-tr)
    }

  -- Example 3.8 (`BinInit`): Bin is an initial algebra for `P X = 1 + X`.
  Bin-InitAlg : InitAlg {ℓ} {ℓ} {ℓ} (Bool {ℓ}) PolyB
  Bin-InitAlg = (Bin , supBin) , InitAlgOn.isInit Bin-InitAlgOn

  {-
      The universal properties of `(ℕ , supN)`, extracted from
      initiality alone: the recursor as the carrier of the unique
      map, the eliminator from the section it determines on the
      total space.
  -}
  supN : P (Bool {ℓ}) PolyB (ℕ {ℓ}) → ℕ {ℓ}
  supN = InitAlgOn.sup ℕ-InitAlgOn

  -- Recursion: the carrier of the unique morphism into `(D , supD)`.
  foldInit : {D : Type ℓ} → (P (Bool {ℓ}) PolyB D → D) → ℕ {ℓ} → D
  foldInit {D} supD = fst (fst (InitAlgOn.isInit ℕ-InitAlgOn (D , supD)))

  supN-CA : ConstrAlgebra Wsig (ℕ {ℓ})
  supN-CA _ (a , (u , tt)) = supN (a , u)

  {-
      Induction derived straight from initiality: build the
      total-space algebra `Σ ℕ motive`, take the unique map into it,
      and use that its first projection is a section (forced by
      uniqueness of endo-homs, `homEqInitId`).
  -}
  indInit : (motive : ℕ {ℓ} → Type ℓ) →
            Cases Wsig (ℕ {ℓ}) supN-CA motive →
            (n : ℕ {ℓ}) → motive n
  indInit motive mp n = tpt motive (section n) (snd (fst initMap n))
    where
      total : P-Alg (Bool {ℓ}) PolyB
      total = (Σ (ℕ {ℓ}) motive)
            , λ { (a , v) → supN (a , fst ∘ v)
                          , mp tt (a , (fst ∘ v , tt))
                                  ((λ x → snd (v x)) , tt) }

      initMap : AlgHom (ℕ {ℓ} , supN) total
      initMap = fst (InitAlgOn.isInit ℕ-InitAlgOn total)

      proj : AlgHom total (ℕ {ℓ} , supN)
      proj = fst , refl

      section : (k : ℕ {ℓ}) → fst (fst initMap k) ≡ k
      section = ext-fun
        (ap fst (homEqInitId (ℕ {ℓ} , supN)
                             (InitAlgOn.isInit ℕ-InitAlgOn)
                             (AlgHom-∘ (ℕ {ℓ} , supN) total (ℕ {ℓ} , supN)
                                       initMap proj)))

  {-
      Example 3.8 (Motivating Example with Initial Algebras)
      The paper-facing interface: `P X = 1 + X` spelled out as a
      point and an endo-map, with the recursor and eliminator the
      initial algebra provides.
  -}
  pointEndo : {D : Type ℓ} → D → (D → D) → P (Bool {ℓ}) PolyB D → D
  pointEndo z s (true  , _) = z
  pointEndo z s (false , u) = s (u tt)

  -- Example 3.8: the recursor `recNat`, derived from initiality.
  recNat : {D : Type ℓ} → D → (D → D) → ℕ {ℓ} → D
  recNat z s = foldInit (pointEndo z s)

  -- Computation rules: the homomorphism square of the unique map,
  -- read off at the two shapes.
  recNat-zero : {D : Type ℓ} {z : D} {s : D → D} →
                recNat z s zero ≡ z
  recNat-zero {D} {z} {s} =
      ext-fun (snd (fst (InitAlgOn.isInit ℕ-InitAlgOn (D , pointEndo z s))))
              (true , (λ ()))

  recNat-succ : {D : Type ℓ} {z : D} {s : D → D} {n : ℕ {ℓ}} →
                recNat z s (succ n) ≡ s (recNat z s n)
  recNat-succ {D} {z} {s} {n} =
      ext-fun (snd (fst (InitAlgOn.isInit ℕ-InitAlgOn (D , pointEndo z s))))
              (false , (λ _ → n))

  {-
      Example 3.5 (Nat Homomorphism)
      `fromNat` is an algebra homomorphism from the native
      `[zero, succ]` algebra (`pointEndo zero succ`) to the native
      `[bzero, binSucc]` algebra — the commuting square of the
      paper's motivating homomorphism example. Both shapes hold
      definitionally.
  -}
  fromNat-hom : isAlgHom (ℕ {ℓ} , pointEndo zero succ) (Bin , supBin) fromNat
  fromNat-hom = ext (λ { (true  , _) → refl
                       ; (false , _) → refl })

  {-
      Dependent eliminator with the familiar `zero`/`succ` methods,
      routed through `bridgeBwd : InitAlgOn → IndAlg` so that the
      β-rules can be read off `IndAlg.beta`.
  -}
  ℕ-IA : WTypeIndAlg {ℓ} (Bool {ℓ}) PolyB (ℕ {ℓ})
  ℕ-IA = bridgeBwd ℕ-InitAlgOn

  casesN : (Q : ℕ {ℓ} → Type ℓ) (qz : Q zero)
           (qs : (n : ℕ {ℓ}) → Q n → Q (succ n)) →
           Cases Wsig (ℕ {ℓ}) (IndAlg.algebra ℕ-IA) Q
  casesN Q qz qs tt (true  , (u , tt)) _          = qz
  casesN Q qz qs tt (false , (u , tt)) (ihf , tt) = qs (u tt) (ihf tt)

  indNatIndAlg : (Q : ℕ {ℓ} → Type ℓ) →
           Q zero → ((n : ℕ {ℓ}) → Q n → Q (succ n)) →
           (n : ℕ {ℓ}) → Q n
  indNatIndAlg Q qz qs = IndAlg.ind ℕ-IA Q (casesN Q qz qs)

  indNat-zero : {Q : ℕ {ℓ} → Type ℓ} {qz : Q zero}
                {qs : (n : ℕ {ℓ}) → Q n → Q (succ n)} →
                indNatIndAlg Q qz qs zero ≡ qz
  indNat-zero {Q} {qz} {qs} =
      IndAlg.beta ℕ-IA Q (casesN Q qz qs) tt (true , ((λ ()) , tt))

  indNat-succ : {Q : ℕ {ℓ} → Type ℓ} {qz : Q zero}
                {qs : (n : ℕ {ℓ}) → Q n → Q (succ n)} {n : ℕ {ℓ}} →
                indNatIndAlg Q qz qs (succ n) ≡ qs n (indNatIndAlg Q qz qs n)
  indNat-succ {Q} {qz} {qs} {n} =
      IndAlg.beta ℕ-IA Q (casesN Q qz qs) tt (false , ((λ _ → n) , tt))

  {- The programs, written in terms of the universal properties. -}

  isZeroNAlg : ℕ {ℓ} → Bool {ℓ}
  isZeroNAlg = recNat true (λ _ → false)

  _+N_ : ℕ {ℓ} → ℕ {ℓ} → ℕ {ℓ}
  m +N n = recNat n succ m

  -- `n +N zero ≡ n`: induction, with the recursor β-rules supplying
  -- the `+N` computation steps.
  zero-is-unitAlg : (n : ℕ {ℓ}) → n +N zero ≡ n
  zero-is-unitAlg = indNatIndAlg (λ n → n +N zero ≡ n)
                           (recNat-zero {z = zero} {s = succ})
                           (λ n ih → recNat-succ {z = zero} {s = succ} {n = n}
                                       • ap succ ih)

  {-
      Example 3.8 (repair): `recBin`, `indBin`, `isZeroBinAlg`, `zUnitB`.
      Repair = the same universal properties at Bin: `Bin` is initial
      for the same functor, so `recBin`/`indBin` are `recNat`/`indNat`
      verbatim with the initial algebra swapped.
  -}
  supB : P (Bool {ℓ}) PolyB Bin → Bin
  supB = InitAlgOn.sup Bin-InitAlgOn          -- definitionally `supBin`

  foldInitB : {D : Type ℓ} → (P (Bool {ℓ}) PolyB D → D) → Bin → D
  foldInitB {D} supD = fst (fst (InitAlgOn.isInit Bin-InitAlgOn (D , supD)))

  supB-CA : ConstrAlgebra Wsig Bin
  supB-CA _ (a , (u , tt)) = supB (a , u)

  indInitB : (motive : Bin → Type ℓ) →
             Cases Wsig Bin supB-CA motive →
             (b : Bin) → motive b
  indInitB motive mp b = tpt motive (section b) (snd (fst initMap b))
    where
      total : P-Alg (Bool {ℓ}) PolyB
      total = (Σ Bin motive)
            , λ { (a , v) → supB (a , fst ∘ v)
                          , mp tt (a , (fst ∘ v , tt))
                                  ((λ x → snd (v x)) , tt) }
      initMap : AlgHom (Bin , supB) total
      initMap = fst (InitAlgOn.isInit Bin-InitAlgOn total)
      proj : AlgHom total (Bin , supB)
      proj = fst , refl
      section : (k : Bin) → fst (fst initMap k) ≡ k
      section = ext-fun
        (ap fst (homEqInitId (Bin , supB)
                             (InitAlgOn.isInit Bin-InitAlgOn)
                             (AlgHom-∘ (Bin , supB) total (Bin , supB)
                                       initMap proj)))

  recBin : {D : Type ℓ} → D → (D → D) → Bin → D
  recBin z s = foldInitB (pointEndo z s)

  recBin-zero : {D : Type ℓ} {z : D} {s : D → D} →
                recBin z s bzero ≡ z
  recBin-zero {D} {z} {s} =
      ext-fun (snd (fst (InitAlgOn.isInit Bin-InitAlgOn (D , pointEndo z s))))
              (true , (λ ()))

  recBin-succ : {D : Type ℓ} {z : D} {s : D → D} {b : Bin} →
                recBin z s (binSucc b) ≡ s (recBin z s b)
  recBin-succ {D} {z} {s} {b} =
      ext-fun (snd (fst (InitAlgOn.isInit Bin-InitAlgOn (D , pointEndo z s))))
              (false , (λ _ → b))

  indBin : (Q : Bin → Type ℓ) →
           Q bzero → ((b : Bin) → Q b → Q (binSucc b)) →
           (b : Bin) → Q b
  indBin Q qz qs =
      indInitB Q (λ { tt (true  , _)        _          → qz
                    ; tt (false , (u , tt)) (ihf , tt) → qs (u tt) (ihf tt) })

  {- The repaired programs: same code, `*Nat ↦ *Bin`. -}

  isZeroBinAlg : Bin → Bool {ℓ}
  isZeroBinAlg = recBin true (λ _ → false)

  _+B_ : Bin → Bin → Bin
  m +B n = recBin n binSucc m

  zUnitB : (b : Bin) → b +B bzero ≡ b
  zUnitB = indBin (λ b → b +B bzero ≡ b)
                  (recBin-zero {z = bzero} {s = binSucc})
                  (λ b ih → recBin-succ {z = bzero} {s = binSucc} {b = b}
                              • ap binSucc ih)

  {-
      Example 3.12 (`recNatSwap`, `isZeroCoh`)
      Repair by instantiation, concretely: the recursor out of ℕ is
      the recursor out of Bin precomposed with the isomorphism —
      `foldSwap` instantiated at this example, proved directly by
      induction from the two pairs of computation rules.
  -}
  recNatSwap : {D : Type ℓ} {z : D} {s : D → D} →
               recNat z s ≡ recBin z s ∘ fromNat
  recNatSwap {D} {z} {s} = ext pw
    where
      pw : (n : ℕ {ℓ}) → recNat z s n ≡ recBin z s (fromNat n)
      pw zero     = recNat-zero {z = z} {s = s}
                  • ! (recBin-zero {z = z} {s = s})
      pw (succ m) = recNat-succ {z = z} {s = s} {n = m}
                  • ap s (pw m)
                  • ! (recBin-succ {z = z} {s = s} {b = fromNat m})

  {- Each old program equals the repaired program conjugated by the
     isomorphism, as one `happly` of the swap. -}
  isZeroCoh : (n : ℕ {ℓ}) → isZeroNAlg n ≡ isZeroBinAlg (fromNat n)
  isZeroCoh = happly (recNatSwap {z = true} {s = λ _ → false})

  {-
      Natively-defined `isZero` on each side, and its coherence
      across the isomorphism.
  -}
  isZeroN : ℕ {ℓ} → Bool {ℓ}
  isZeroN zero     = true
  isZeroN (succ _) = false

  isZeroB : Bin → Bool {ℓ}
  isZeroB bzero    = true
  isZeroB (bpos _) = false

  -- Successor on Bin always produces a `bpos`.
  isZeroB-binSucc : (b : Bin) → isZeroB (binSucc b) ≡ false
  isZeroB-binSucc bzero    = refl
  isZeroB-binSucc (bpos _) = refl

  isZero-coh : (n : ℕ {ℓ}) → isZeroN n ≡ isZeroB (fromNat n)
  isZero-coh zero     = refl
  isZero-coh (succ m) = ! (isZeroB-binSucc (fromNat m))

  {-
      Dependent repair: an ℕ-theorem transported to a Bin-theorem via
      `repair-Π` and the configuration. The framework's inverse map
      `g (snd (configToEquiv natConfig))` is propositionally `toNat`;
      we alias it for readability.
  -}
  toNat-eqv : Bin → ℕ {ℓ}
  toNat-eqv = g (snd (configToEquiv natConfig))

  fromNat-eqv : ℕ {ℓ} → Bin
  fromNat-eqv = f (snd (configToEquiv natConfig))

  zero-is-unit : (n : ℕ {ℓ}) → n + zero ≡ n
  zero-is-unit zero     = refl
  zero-is-unit (succ m) = ap succ (zero-is-unit m)

  {- Example 3.12 (`zUnitB`, ranging over `toNat b`)
     The repaired theorem, ranging over `Bin`; derived from
     `zero-is-unit` and `natConfig` alone. -}
  zero-is-unit-Bin :
      (b : Bin) → toNat-eqv b + zero ≡ toNat-eqv b
  zero-is-unit-Bin =
      repair-Π natConfig
          (λ n → n + zero ≡ n)
          zero-is-unit

  {- Example 3.12 (`zUnitCoh`)
     Coherence: the repaired theorem transports back to the original
     along the round-trip witness `η`. -}
  zero-is-unit-Bin-coh :
      (n : ℕ {ℓ}) →
      tpt (λ m → m + zero ≡ m)
          (η (snd (configToEquiv natConfig)) n)
          (zero-is-unit-Bin (fromNat-eqv n))
        ≡ zero-is-unit n
  zero-is-unit-Bin-coh =
      repair-Π-coh natConfig
          (λ n → n + zero ≡ n)
          zero-is-unit
