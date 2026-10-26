{- `-WnoUnsupportedIndexedMatch`: matches on `Fin n` / `Vec A n` at
   `succ`-headed indices need injectivity of `succ`, which Cubical
   Agda cannot yet run; harmless here, as nothing on the cubical side
   imports this file. -}
{-# OPTIONS --without-K --cubical-compatible -WnoUnsupportedIndexedMatch #-}

open import common
open import inductive-repair.indspec
open import inductive-repair.config
open import inductive-repair.coherence

open Signature
open _≃_

{-
    Repair between the indexed families `Vec A n` and
    `FinSet n A = Fin n → A`, *at each fixed index*: a function
    `finVecConfig : (n : ℕ) → Config …` producing one configuration
    per index. The indices themselves are never repaired — matching
    how the proof repair literature treats inductive families.

    The shared per-`n` signature has one operation whose only datum
    is a function `Fin n → A` (the n values to install). The `Vec`
    side interprets it as `tabulateV`; the `FinSet` side as the
    identity.
-}
module inductive-repair.examples.finvec {ℓ : Level} where

  data Vec (A : Type ℓ) : ℕ {ℓ} → Type ℓ where
    nil  : Vec A zero
    cons : ∀ n → A → Vec A n → Vec A (succ n)

  FinSet : ℕ {ℓ} → Type ℓ → Type ℓ
  FinSet n A = Fin n → A

  {-
      Fin-only helpers used by `reverse`.

      `last n   : Fin (succ n)` — the maximal element.
      `inject n : Fin n → Fin (succ n)` — embed at the same position.
      `mirror n : Fin n → Fin n` — reverse the index, position `k`
                  to position `n - 1 - k`.
  -}
  last : (n : ℕ {ℓ}) → Fin (succ n)
  last zero     = zero
  last (succ n) = suc (last n)

  inject : (n : ℕ {ℓ}) → Fin n → Fin (succ n)
  inject (succ n) zero    = zero
  inject (succ n) (suc i) = suc (inject n i)

  mirror : (n : ℕ {ℓ}) → Fin n → Fin n
  mirror (succ n) zero    = last n
  mirror (succ n) (suc i) = inject n (mirror n i)

  module _ (A : Type ℓ) where

    {-
        Per-`n` signature shared by `Vec A n` and `FinSet n A`:
        a single operation with one non-recursive `Fin n → A`
        argument. Both carriers are non-recursive in this framing —
        each is a "length-n tuple" — so the arity uses only `Nonrec`.
    -}
    sig : ℕ {ℓ} → Signature {ℓ}
    sig n .Op = ⊤
    sig n .arity _ = Nonrec (Fin n → A) (λ _ → Done)

    {- Tabulate / lookup, and their round-trips. -}

    tabulateV : (n : ℕ {ℓ}) → (Fin n → A) → Vec A n
    tabulateV zero     _ = nil
    tabulateV (succ n) f = cons n (f zero) (tabulateV n (f ∘ suc))

    lookupV : (n : ℕ {ℓ}) → Vec A n → Fin n → A
    lookupV (succ n) (cons _ a _) zero    = a
    lookupV (succ n) (cons _ _ v) (suc i) = lookupV n v i

    tabulate-lookup : (n : ℕ {ℓ}) (v : Vec A n) → tabulateV n (lookupV n v) ≡ v
    tabulate-lookup zero     nil          = refl
    tabulate-lookup (succ n) (cons _ a v) = ap (cons n a) (tabulate-lookup n v)

    lookup-tabulate : (n : ℕ {ℓ}) (f : Fin n → A) → lookupV n (tabulateV n f) ≡ f
    lookup-tabulate zero     _ = ext (λ ())
    lookup-tabulate (succ n) f = ext λ where
        zero    → refl
        (suc i) → happly (lookup-tabulate n (f ∘ suc)) i

    private
      ap-fork : (n : ℕ {ℓ}) {g₁ g₂ : Fin (succ n) → A} (p : g₁ ≡ g₂) →
                ap (λ g → cons n (g zero) (tabulateV n (g ∘ suc))) p
                  ≡ ap2 (cons n)
                        (ap (λ g → g zero) p)
                        (ap (λ g → tabulateV n (g ∘ suc)) p)
      ap-fork _ refl = refl

      ap2-refl-l : {X Y Z : Type ℓ} (P : X → Y → Z) {a : X} {c d : Y} (q : c ≡ d) →
                   ap2 P (refl {x = a}) q ≡ ap (P a) q
      ap2-refl-l P refl = refl

    {-
        Half-adjoint triangle for `(tabulateV n, lookupV n)`: the
        round-trip `tabulateV n ∘ lookupV n = id` is the image of
        `lookupV n ∘ tabulateV n = id` under `tabulateV n`. By
        induction on `n`.
    -}
    triangle : (n : ℕ {ℓ}) (f : Fin n → A) →
               ap (tabulateV n) (lookup-tabulate n f)
                 ≡ tabulate-lookup n (tabulateV n f)
    triangle zero     f = ap-const (lookup-tabulate zero f)
    triangle (succ n) f =
        ap-fork n (lookup-tabulate (succ n) f)
      • ap2-cong (cons n) zero-part suc-part
      • ap2-refl-l (cons n) (tabulate-lookup n (tabulateV n (f ∘ suc)))
      where
        zero-part : ap (λ g → g zero) (lookup-tabulate (succ n) f) ≡ refl
        zero-part = ! (happly-ap (lookup-tabulate (succ n) f) zero)
                  • happlyExt _ zero

        suc-part : ap (λ g → tabulateV n (g ∘ suc)) (lookup-tabulate (succ n) f)
                     ≡ tabulate-lookup n (tabulateV n (f ∘ suc))
        suc-part =
            ap-∘ (lookup-tabulate (succ n) f)
          • ap (ap (tabulateV n)) (precomp-ext suc _)
          • ap (ap (tabulateV n)) (! (extHapply (lookup-tabulate n (f ∘ suc))))
          • triangle n (f ∘ suc)

    {- Algebras, inductions, betas — per side. -}

    algVec : (n : ℕ {ℓ}) → ConstrAlgebra (sig n) (Vec A n)
    algVec n _ (f , _) = tabulateV n f

    indVec : (n : ℕ {ℓ}) → Induction (sig n) (algVec n)
    indVec n motive cases v =
        tpt motive (tabulate-lookup n v) (cases tt (lookupV n v , tt) tt)

    betaVec : (n : ℕ {ℓ}) → BetaLaw (sig n) (indVec n)
    betaVec n motive cases _ (f , _) =
        ! (ap (λ p → tpt motive p (cases tt (lookupV n (tabulateV n f) , tt) tt))
              (triangle n f))
      • tpt-ap motive (tabulateV n) (lookup-tabulate n f) _
      • apd (λ g → motive (tabulateV n g))
            (λ g → cases tt (g , tt) tt)
            (lookup-tabulate n f)

    algFin : (n : ℕ {ℓ}) → ConstrAlgebra (sig n) (FinSet n A)
    algFin n _ (f , _) = f

    indFin : (n : ℕ {ℓ}) → Induction (sig n) (algFin n)
    indFin n motive cases f = cases tt (f , tt) tt

    betaFin : (n : ℕ {ℓ}) → BetaLaw (sig n) (indFin n)
    betaFin n motive cases _ (f , _) = refl

    {- The per-`n` configuration. -}

    finVecConfig : (n : ℕ {ℓ}) → Config (sig n) (Vec A n) (FinSet n A)
    finVecConfig n .Config.indAlgC =
        record { algebra = algVec n ; ind = indVec n ; beta = betaVec n }
    finVecConfig n .Config.indAlgD =
        record { algebra = algFin n ; ind = indFin n ; beta = betaFin n }

    {-
        Repaired functions across the configuration: the Vec-side
        definition is structural, the FinSet-side definition is a
        direct combinator on `Fin n → A`, and the correspondence is
        the proof obligation a repair tool would emit — all at a
        fixed index `n` (or, for `head`/`last`, a fixed `succ n`).
    -}

    headV : (n : ℕ {ℓ}) → Vec A (succ n) → A
    headV _ (cons _ a _) = a

    headF : (n : ℕ {ℓ}) → FinSet (succ n) A → A
    headF _ f = f zero

    head-coh : (n : ℕ {ℓ}) (v : Vec A (succ n)) →
               headV n v ≡ headF n (lookupV (succ n) v)
    head-coh _ (cons _ _ _) = refl

    lastV : (n : ℕ {ℓ}) → Vec A (succ n) → A
    lastV zero     (cons _ a _) = a
    lastV (succ n) (cons _ _ v) = lastV n v

    lastF : (n : ℕ {ℓ}) → FinSet (succ n) A → A
    lastF n f = f (last n)

    last-coh : (n : ℕ {ℓ}) (v : Vec A (succ n)) →
               lastV n v ≡ lastF n (lookupV (succ n) v)
    last-coh zero     (cons _ _ _) = refl
    last-coh (succ n) (cons _ _ v) = last-coh n v

    {- For reverse, both sides take the per-position view — the
       FinSet side precomposes with `mirror n`, the Vec side
       tabulates the reversed lookup — so the correspondence is a
       one-step application of `lookup-tabulate`. -}

    reverseV : (n : ℕ {ℓ}) → Vec A n → Vec A n
    reverseV n v = tabulateV n (lookupV n v ∘ mirror n)

    reverseF : (n : ℕ {ℓ}) → FinSet n A → FinSet n A
    reverseF n f = f ∘ mirror n

    reverse-coh : (n : ℕ {ℓ}) (v : Vec A n) →
                  lookupV n (reverseV n v) ≡ reverseF n (lookupV n v)
    reverse-coh n v = lookup-tabulate n (lookupV n v ∘ mirror n)

    replicateV : (n : ℕ {ℓ}) → A → Vec A n
    replicateV zero     _ = nil
    replicateV (succ n) a = cons n a (replicateV n a)

    replicateF : (n : ℕ {ℓ}) → A → FinSet n A
    replicateF _ a _ = a

    replicate-coh : (n : ℕ {ℓ}) (a : A) →
                    lookupV n (replicateV n a) ≡ replicateF n a
    replicate-coh zero     a = ext (λ ())
    replicate-coh (succ n) a = ext λ where
        zero    → refl
        (suc i) → happly (replicate-coh n a) i

    {-
        The PUMPKIN Pi coherence conditions, instantiated for
        `finVecConfig n`. All are derived generically in
        `inductive-repair.coherence`; this is the call site.
    -}
    module CoherenceFV (n : ℕ {ℓ}) where
        open Coherence (finVecConfig n) public

        -- Single-operation constructor coherence: the tabulate of
        -- `f` on the Vec side and `f` itself on the FinSet side
        -- correspond under the carrier equivalence.
        constr-coh : (f : Fin n → A) →
                     algVec n tt (f , tt) ≡[ carrier-eqv ] algFin n tt (f , tt)
        constr-coh f = constr-ok tt refl

        -- `iota_ok` per side: the β-rules under their PUMPKIN Pi names.
        beta-coh-Vec : BetaLaw (sig n) (indVec n)
        beta-coh-Vec = beta-ok-C

        beta-coh-Fin : BetaLaw (sig n) (indFin n)
        beta-coh-Fin = beta-ok-D

        -- `elim_ok`: cross-side eliminator coherence.
        elim-coh : (PD : FinSet n A → Type ℓ)
                   (casesD : Cases (sig n) (FinSet n A) (algFin n) PD)
                   (c : Vec A n) →
                   indVec n (PD ∘ f carrier-eqv) (deriveCasesC PD casesD) c
                     ≡ indFin n PD casesD (f carrier-eqv c)
        elim-coh = elim-ok
