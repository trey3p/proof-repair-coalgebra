{-# OPTIONS --cubical --guardedness --safe #-}

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
  renaming (Set to Type)
open import Agda.Primitive.Cubical using (I; i0; i1; primHComp)
  renaming (primIMin to _∧_; primIMax to _∨_;
            primINeg to ~_; primTransp to transp)
open import coinductive-repair.mtype hiding (corec)

{-
    Configurations for proof repair, coinductive edition — the
    mirror of `inductive-repair.indspec` + `inductive-repair.config`
    dualized from constructor-in to destructor-out: `DestrArity` /
    `Outputs` / `mapOutputs` / `CoSignature` / `DestrAlgebra`,
    the coinductive type structure `CoindCoalg` (destr + corec +
    β + function-level η) and its Σ-uniqueness upgrade
    `HCoindCoalg`, bisimulations with the derived coinduction
    principles (`deriveCoind`, `deriveCoind2D`), and the
    configuration records `CoConfig` / `HCoConfig` with the
    equivalence `coConfigToEquiv`.
-}
module coinductive-repair.config {ℓ : Level} where


    {-
       Local unit (no library imports)
    -}

    record ⊤ : Type ℓ where
      constructor tt
    open ⊤ public


    {-
       Syntactic infrastructure (parallel to `inductive-repair.indspec`).
    -}

    {-
      Definition 4.16
        The output telescope of a single destructor — the same
        datatype as `ConstrArity`, with the direction of
        information flow flipped: `Done` terminates, `Nonrec A k`
        is a non-recursive output (continuation may depend on it),
        `Rec D cs` a `D`-indexed recursive output.
    -}
    data DestrArity : Type (lsuc ℓ) where
      Done   : DestrArity
      Nonrec : (A : Type ℓ) → (A → DestrArity) → DestrArity
      Rec    : (D : Type ℓ) → DestrArity → DestrArity

    {-
      Definition 4.16
        The outputs of a destructor of the given arity: a Σ-chain
        with `Ty` at the recursive positions.
    -}
    Outputs : DestrArity → Type ℓ → Type ℓ
    Outputs Done         _  = ⊤
    Outputs (Nonrec A k) Ty = Σ A (λ a → Outputs (k a) Ty)
    Outputs (Rec D cs)   Ty = Σ (D → Ty) (λ _ → Outputs cs Ty)

    {-
        Functorial action: postcompose every recursive output
        with `f`, keeping `Nonrec` data unchanged.
    -}
    mapOutputs : (cs : DestrArity) {Ty₁ Ty₂ : Type ℓ} →
                 (Ty₁ → Ty₂) → Outputs cs Ty₁ → Outputs cs Ty₂
    mapOutputs Done         _ _         = tt
    mapOutputs (Nonrec A k) f (a , o)   = (a , mapOutputs (k a) f o)
    mapOutputs (Rec D cs)   f (r , o)   = ((λ d → f (r d)) , mapOutputs cs f o)

    -- `mapOutputs` with the identity is the identity.
    mapOutputs-id : {Ty : Type ℓ} (cs : DestrArity) (o : Outputs cs Ty) →
                    mapOutputs cs (λ x → x) o ≡ o
    mapOutputs-id Done         _         = refl
    mapOutputs-id (Nonrec A k) (a , o) i = a , mapOutputs-id (k a) o i
    mapOutputs-id (Rec D cs)   (r , o) i = r , mapOutputs-id cs o i

    -- `mapOutputs` respects composition.
    mapOutputs-∘ : {Ty₁ Ty₂ Ty₃ : Type ℓ} (cs : DestrArity)
                   (f : Ty₁ → Ty₂) (g : Ty₂ → Ty₃) (o : Outputs cs Ty₁) →
                   mapOutputs cs g (mapOutputs cs f o)
                     ≡ mapOutputs cs (λ x → g (f x)) o
    mapOutputs-∘ Done         _ _ _         = refl
    mapOutputs-∘ (Nonrec A k) f g (a , o) i = a , mapOutputs-∘ (k a) f g o i
    mapOutputs-∘ (Rec D cs)   f g (r , o) i =
        (λ d → g (f (r d))) , mapOutputs-∘ cs f g o i


    {-
       Coinductive signatures and coalgebras
    -}

    {-
      Definition 4.16
        A signature for a single-sorted coinductive type: one
        operation per destructor label, tagged with its arity.
    -}
    record CoSignature : Type (lsuc ℓ) where
      field
        Op    : Type ℓ
        arity : Op → DestrArity
    open CoSignature

    {-
      Definition 4.16 (Destructor Algebra)
        A coalgebra for `sig` on `Ty` (dual of `ConstrAlgebra`):
        one destructor `Ty → Outputs (arity sig op) Ty` per
        operation. This is the per-destructor exposure a repair
        algorithm walks.
    -}
    DestrAlgebra : (sig : CoSignature) → (Ty : Type ℓ) → Type ℓ
    DestrAlgebra sig Ty =
        (op : Op sig) → Ty → Outputs (arity sig op) Ty


    {-
       Coinductive type structure `CoindCoalg`.
    -}

    {-
      Definition 4.17 (Coinductive Configuration): `CoindCoalg`
        A `CoindCoalg` for `sig` on `X`: the destructors `destr`,
        the corecursor `corec` from any source coalgebra, its
        per-destructor β-rule, and function-level uniqueness
        `corec-η`. Categorically, 1-finality; the coinduction
        principle is derived below, not carried as a field.
    -}
    record CoindCoalg (sig : CoSignature) (X : Type ℓ) : Type (lsuc ℓ) where
      field
        destr   : DestrAlgebra sig X
        corec   : {C : Type ℓ} → DestrAlgebra sig C → C → X
        corec-β : {C : Type ℓ} (destrC : DestrAlgebra sig C) →
                  (op : Op sig) (c : C) →
                  destr op (corec destrC c)
                    ≡ mapOutputs (arity sig op) (corec destrC) (destrC op c)
        corec-η : {C : Type ℓ} (destrC : DestrAlgebra sig C) (h : C → X) →
                  ((op : Op sig) (c : C) →
                   destr op (h c)
                     ≡ mapOutputs (arity sig op) h (destrC op c)) →
                  (c : C) → h c ≡ corec destrC c


    {-
       Bisimulations and the derived coinduction principle: a
       bisimulation is a relation closed under all destructors;
       `deriveCoind` discharges it into a path via the classical
       Rutten graph argument, using only `corec-η`.
    -}

    {-
        Per-arity bisim relation: `Nonrec` heads agree as paths
        (the first output is `subst`-transported along the head
        path to land in the second's fiber), `Rec` children are
        pointwise `R`-related.
    -}
    OutputsRel : (cs : DestrArity) {Ty : Type ℓ} (R : Ty → Ty → Type ℓ) →
                 Outputs cs Ty → Outputs cs Ty → Type ℓ
    OutputsRel Done         _ _          _          = ⊤
    OutputsRel (Nonrec A k) R (a1 , o1)  (a2 , o2)  =
        Σ (a1 ≡ a2)
          (λ p → OutputsRel (k a2) R
                    (subst (λ a → Outputs (k a) _) p o1) o2)
    OutputsRel (Rec D cs)   R (r1 , o1)  (r2 , o2)  =
        Σ ((d : D) → R (r1 d) (r2 d))
          (λ _ → OutputsRel cs R o1 o2)

    {-
        A bisimulation between `x` and `y` w.r.t. `destr`:
        per-destructor, the outputs at `x` and `y` are
        `R`-related.
    -}
    SigBisim : (sig : CoSignature) {X : Type ℓ} →
               DestrAlgebra sig X →
               (R : X → X → Type ℓ) → X → X → Type ℓ
    SigBisim sig destr R x y =
        (op : Op sig) →
        OutputsRel (arity sig op) R (destr op x) (destr op y)

    {-
        `R` is a syntactic bisim for `destr`: every related
        pair witnesses the per-destructor `SigBisim`.
    -}
    isBisim : (sig : CoSignature) {X : Type ℓ} →
              DestrAlgebra sig X →
              (R : X → X → Type ℓ) → Type ℓ
    isBisim sig destr R =
        ∀ {x y} → R x y → SigBisim sig destr R x y

    {-
        The Rutten graph type (triples `(x, y, r : R x y)`) and
        the realisation of an `OutputsRel` witness as graph
        outputs. `graphOutputs` picks the second element's
        `Nonrec` head, so the second projection becomes a strict
        coalgebra hom.
    -}
    Graph : (X : Type ℓ) (R : X → X → Type ℓ) → Type ℓ
    Graph X R = Σ X (λ x → Σ X (λ y → R x y))

    graphOutputs : (cs : DestrArity) {X : Type ℓ} {R : X → X → Type ℓ}
                   (o1 o2 : Outputs cs X) →
                   OutputsRel cs R o1 o2 → Outputs cs (Graph X R)
    graphOutputs Done         _ _ _                          = tt
    graphOutputs (Nonrec A k) (a1 , o1) (a2 , o2) (p , rest) =
        a2 ,
        graphOutputs (k a2)
          (subst (λ a → Outputs (k a) _) p o1) o2 rest
    graphOutputs (Rec D cs)   (r1 , o1) (r2 , o2) (rrel , rest) =
        (λ d → r1 d , r2 d , rrel d) ,
        graphOutputs cs o1 o2 rest

    {-
      Definition 4.17
        Derived coinduction: equip the graph carrier with a
        coalgebra structure; both projections are coalgebra homs
        into `X`, so by `corec-η` they agree with the corecursor
        and hence with each other. Packaged as a module so the
        2-cell coherences downstream can name the components;
        `deriveCoind` is the thin wrapper `coind` below.
    -}
    module DeriveCoind
        {sig : CoSignature} {X : Type ℓ} (ind : CoindCoalg sig X)
        (R : X → X → Type ℓ)
        (bisim : isBisim sig (CoindCoalg.destr ind) R) where
      open CoindCoalg ind

      proj1 : Graph X R → X
      proj1 (x' , _ , _) = x'

      proj2 : Graph X R → X
      proj2 (_ , y' , _) = y'

      graphCoalg : DestrAlgebra sig (Graph X R)
      graphCoalg op (x' , y' , r') =
          graphOutputs (arity sig op)
            (destr op x') (destr op y') (bisim r' op)

      {-
          `proj2` projects strictly: mapping `proj2` over
          `graphOutputs` recovers `o2`. Recursion-only;
          no path machinery needed.
      -}
      graph-proj2 : (cs : DestrArity) (o1 o2 : Outputs cs X) →
                    (rel : OutputsRel cs R o1 o2) →
                    mapOutputs cs proj2 (graphOutputs cs o1 o2 rel) ≡ o2
      graph-proj2 Done         _ _ _                            = refl
      graph-proj2 (Nonrec A k) (a1 , o1) (a2 , o2) (p , rest) i =
          a2 ,
          graph-proj2 (k a2)
            (subst (λ a → Outputs (k a) X) p o1) o2 rest i
      graph-proj2 (Rec D cs)   (r1 , o1) (r2 , o2) (rrel , rest) i =
          r2 , graph-proj2 cs o1 o2 rest i

      {-
          `proj1` recovers `o1` only after a `Nonrec`
          adjustment. In each `Nonrec` step, mapping
          `proj1` over `graphOutputs` produces
          `(a2, subst p o1.snd)` instead of `(a1, o1)` —
          we bridge with two paths: the IH (a Path with
          head fixed at `a2`), then a transport-back path
          along `sym p` for the head and the inverse
          `subst-filler` for the tail. Composed via `∙`.
      -}
      graph-proj1 : (cs : DestrArity) (o1 o2 : Outputs cs X) →
                    (rel : OutputsRel cs R o1 o2) →
                    mapOutputs cs proj1 (graphOutputs cs o1 o2 rel) ≡ o1
      graph-proj1 Done         _ _ _                          = refl
      graph-proj1 (Nonrec A k) (a1 , o1) (a2 , o2) (p , rest) =
          step1 ∙ step2
        where
          ih : mapOutputs (k a2) proj1
                 (graphOutputs (k a2)
                    (subst (λ a → Outputs (k a) X) p o1) o2 rest)
               ≡ subst (λ a → Outputs (k a) X) p o1
          ih = graph-proj1 (k a2)
                 (subst (λ a → Outputs (k a) X) p o1) o2 rest

          step1 : (a2 ,
                   mapOutputs (k a2) proj1
                     (graphOutputs (k a2)
                        (subst (λ a → Outputs (k a) X) p o1) o2 rest))
                  ≡ (a2 , subst (λ a → Outputs (k a) X) p o1)
          step1 i = a2 , ih i

          step2 : (a2 , subst (λ a → Outputs (k a) X) p o1) ≡ (a1 , o1)
          step2 i = p (~ i) ,
                    transp (λ j → Outputs (k (p ((~ i) ∧ j))) X) i o1
      graph-proj1 (Rec D cs)   (r1 , o1) (r2 , o2) (rrel , rest) i =
          r1 , graph-proj1 cs o1 o2 rest i

      proj2-hom : (op : Op sig) (g : Graph X R) →
                  destr op (proj2 g)
                    ≡ mapOutputs (arity sig op) proj2 (graphCoalg op g)
      proj2-hom op (x' , y' , r') =
          sym (graph-proj2 (arity sig op)
                 (destr op x') (destr op y') (bisim r' op))

      proj1-hom : (op : Op sig) (g : Graph X R) →
                  destr op (proj1 g)
                    ≡ mapOutputs (arity sig op) proj1 (graphCoalg op g)
      proj1-hom op (x' , y' , r') =
          sym (graph-proj1 (arity sig op)
                 (destr op x') (destr op y') (bisim r' op))

      proj1-eq : (g : Graph X R) → proj1 g ≡ corec graphCoalg g
      proj1-eq = corec-η graphCoalg proj1 proj1-hom

      proj2-eq : (g : Graph X R) → proj2 g ≡ corec graphCoalg g
      proj2-eq = corec-η graphCoalg proj2 proj2-hom

      coind : ∀ {x y} → R x y → x ≡ y
      coind {x = x} {y = y} r = proj1-eq (x , y , r) ∙ sym (proj2-eq (x , y , r))

    -- Definition 4.17 (`coind` is derivable from the `CoindCoalg` fields)
    deriveCoind :
        {sig : CoSignature} {X : Type ℓ} (ind : CoindCoalg sig X)
        (R : X → X → Type ℓ)
        (bisim : isBisim sig (CoindCoalg.destr ind) R) →
        ∀ {x y} → R x y → x ≡ y
    deriveCoind ind R bisim = DeriveCoind.coind ind R bisim

    {-
        A bisimulation witness `OutputsRel cs R o1 o2` realized as a
        path `o1 ≡ o2` in `Outputs cs X`: `Nonrec` heads use the
        witness's head-path, `Rec` children use `deriveCoind` on the
        witness's `R`-relation. This is the "canonical realization"
        through which both sides of `coind-ok-strict`'s 2-D closure
        are routed — chosen so that the per-arity `Nonrec` heads of
        the C-route and D-route coincide *definitionally* (both are
        the witness head-path), trivialising the 2-D head-cell.
    -}
    realize : (cs : DestrArity) {sig : CoSignature} {X : Type ℓ}
              (ind : CoindCoalg sig X)
              (R : X → X → Type ℓ)
              (bisim : isBisim sig (CoindCoalg.destr ind) R)
              {o1 o2 : Outputs cs X} → OutputsRel cs R o1 o2 → o1 ≡ o2
    realize Done         ind R bisim                       _            = refl
    realize (Nonrec A k) ind R bisim {a1 , oo1} {a2 , oo2} (hp , rest) i =
        hp i ,
        toPathP {A = λ j → Outputs (k (hp j)) _}
                (realize (k a2) ind R bisim rest) i
    realize (Rec D' cs)  ind R bisim {r1 , oo1} {r2 , oo2} (rrel , rest) i =
        (λ d → deriveCoind ind R bisim (rrel d) i) , realize cs ind R bisim rest i

    {-
        `realize` commutes with a `subst` on the witness's left
        endpoint: shifting the realized path's left end along `p`
        equals realizing the `p`-shifted witness. (`J` on `p`.)
    -}
    realize-subst-nat : (cs : DestrArity) {sig : CoSignature} {X : Type ℓ}
                        (ind : CoindCoalg sig X) (R : X → X → Type ℓ)
                        (bisim : isBisim sig (CoindCoalg.destr ind) R)
                        {o1 o1' o2 : Outputs cs X} (p : o1 ≡ o1')
                        (W : OutputsRel cs R o1 o2) →
                        subst (λ z → z ≡ o2) p (realize cs ind R bisim W)
                          ≡ realize cs ind R bisim
                                    (subst (λ Z → OutputsRel cs R Z o2) p W)
    realize-subst-nat cs ind R bisim {o1} {o1'} {o2} p W =
        J (λ _ p' → subst (λ z → z ≡ o2) p' (realize cs ind R bisim W)
                      ≡ realize cs ind R bisim
                                (subst (λ Z → OutputsRel cs R Z o2) p' W))
          (substRefl (λ z → z ≡ o2) (realize cs ind R bisim W)
            ∙ sym (cong (realize cs ind R bisim)
                        (substRefl (λ Z → OutputsRel cs R Z o2) W)))
          p

    -- Same, for a `subst` on the witness's right endpoint.
    realize-subst-nat-right : (cs : DestrArity) {sig : CoSignature} {X : Type ℓ}
                        (ind : CoindCoalg sig X) (R : X → X → Type ℓ)
                        (bisim : isBisim sig (CoindCoalg.destr ind) R)
                        {o1 o2 o2' : Outputs cs X} (p : o2 ≡ o2')
                        (W : OutputsRel cs R o1 o2) →
                        subst (λ z → o1 ≡ z) p (realize cs ind R bisim W)
                          ≡ realize cs ind R bisim
                                    (subst (λ Z → OutputsRel cs R o1 Z) p W)
    realize-subst-nat-right cs ind R bisim {o1} {o2} {o2'} p W =
        J (λ _ p' → subst (λ z → o1 ≡ z) p' (realize cs ind R bisim W)
                      ≡ realize cs ind R bisim
                                (subst (λ Z → OutputsRel cs R o1 Z) p' W))
          (substRefl (λ z → o1 ≡ z) (realize cs ind R bisim W)
            ∙ sym (cong (realize cs ind R bisim)
                        (substRefl (λ Z → OutputsRel cs R o1 Z) W)))
          p


    {-
       Two-dimensional coinduction — the path-level finality
       principle: a relation `R₂` on parallel paths that is a 2-D
       bisimulation collapses to a 2-cell `p ≡ q`. It carries the
       hypothesis `isBisim2D`; the hypothesis-free version would
       be unsound (it would collapse every loop space of `X`).
    -}

    {-
        Per-arity relation on parallel paths in `Outputs`, one
        dimension up from `OutputsRel`: a 2-cell between `Nonrec`
        head paths, `R₂` on `Rec` child-paths.
    -}
    OutputsRel2D : (cs : DestrArity) {X : Type ℓ}
                   (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
                   {o1 o2 : Outputs cs X} (po qo : o1 ≡ o2) → Type ℓ
    OutputsRel2D Done             R₂ po qo = ⊤
    OutputsRel2D (Nonrec A k) {X} R₂ {a1 , o1} {a2 , o2} po qo =
        Σ (cong fst po ≡ cong fst qo) (λ h2 →
           OutputsRel2D (k a2) R₂
             (fromPathP (subst (λ h → PathP (λ i → Outputs (k (h i)) X) o1 o2)
                               h2 (cong snd po)))
             (fromPathP (cong snd qo)))
    OutputsRel2D (Rec D cs)   R₂ {r1 , o1} {r2 , o2} po qo =
        Σ ((d : D) → R₂ (cong (λ o → fst o d) po) (cong (λ o → fst o d) qo))
          (λ _ → OutputsRel2D cs R₂ (cong snd po) (cong snd qo))

    {-
        The path-observations `cong (destr op) p` and
        `cong (destr op) q` are `OutputsRel2D`-related at each op.
    -}
    SigBisim2D : (sig : CoSignature) {X : Type ℓ} (destr : DestrAlgebra sig X)
                 (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
                 {a b : X} → a ≡ b → a ≡ b → Type ℓ
    SigBisim2D sig destr R₂ p q =
        (op : Op sig) →
        OutputsRel2D (arity sig op) R₂ (cong (destr op) p) (cong (destr op) q)

    isBisim2D : (sig : CoSignature) {X : Type ℓ} (destr : DestrAlgebra sig X)
                (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ) → Type ℓ
    isBisim2D sig destr R₂ =
        ∀ {a b} {p q : a ≡ b} → R₂ p q → SigBisim2D sig destr R₂ p q

    {-
        Deriving the 2-D coinduction principle from `corec-uniq-Σ`:
        build a coalgebra on the 2-D (bigon) graph, whose edge
        projections are coalgebra homs, and force them equal by the
        contractibility `corec-uniq-Σ` supplies.
    -}

    -- 2-D bigon graph carrier: an R₂-related pair of parallel paths.
    Graph2D : {X : Type ℓ} (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
            → Type ℓ
    Graph2D {X} R₂ =
      Σ X (λ a → Σ X (λ b → Σ (a ≡ b) (λ p → Σ (a ≡ b) (λ q → R₂ p q))))

    -- Build the bigon graph outputs from an `OutputsRel2D` witness
    -- (the 2-D analog of `graphOutputs`).
    graphOutputs2D :
        {X : Type ℓ} (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
        (cs : DestrArity) {o1 o2 : Outputs cs X}
        (po qo : o1 ≡ o2) → OutputsRel2D cs R₂ po qo
      → Outputs cs (Graph2D {X} R₂)
    graphOutputs2D R₂ Done po qo _ = tt
    graphOutputs2D {X = X} R₂ (Nonrec A k) {a1 , o1} {a2 , o2} po qo (h2 , rest2) =
        a2 ,
        graphOutputs2D R₂ (k a2)
          (fromPathP (subst (λ h → PathP (λ i → Outputs (k (h i)) X) o1 o2)
                            h2 (cong snd po)))
          (fromPathP (cong snd qo)) rest2
    graphOutputs2D R₂ (Rec D cs) {r1 , o1} {r2 , o2} po qo (rrel2 , rest2) =
        (λ d → r1 d , r2 d
             , cong (λ o → fst o d) po , cong (λ o → fst o d) qo
             , rrel2 d) ,
        graphOutputs2D R₂ cs (cong snd po) (cong snd qo) rest2

    -- The 2-D graph coalgebra: at each `op`, observe both parallel paths
    -- and package the `OutputsRel2D` closure as bigon-graph outputs.
    graphCoalg2D :
        {sig : CoSignature} {X : Type ℓ} (destr : DestrAlgebra sig X)
        (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
        (bisim2D : isBisim2D sig destr R₂)
      → DestrAlgebra sig (Graph2D {X} R₂)
    graphCoalg2D {sig = sig} destr R₂ bisim2D op (a , b , p , q , r) =
        graphOutputs2D R₂ (arity sig op)
          (cong (destr op) p) (cong (destr op) q) (bisim2D r op)

    -- The two edge projections: the k-slice of each parallel path.
    graph2D-p graph2D-q :
        {X : Type ℓ} (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
        (k : I) → Graph2D {X} R₂ → X
    graph2D-p R₂ k (a , b , p , q , r) = p k
    graph2D-q R₂ k (a , b , p , q , r) = q k

    {- Recovery lemma (q-side): mapping the q-projection over the
       bigon graph outputs recovers the k-slice of `qo`; the `Nonrec`
       case reconciles the heads by a fibre transport. -}
    recoverQ :
        {X : Type ℓ} {R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ}
        (cs : DestrArity) {o1 o2 : Outputs cs X} (po qo : o1 ≡ o2)
        (W : OutputsRel2D cs R₂ po qo) (k : I)
      → mapOutputs cs (graph2D-q R₂ k) (graphOutputs2D R₂ cs po qo W) ≡ qo k
    recoverQ Done po qo W k = refl
    recoverQ (Rec D cs) po qo (rrel2 , rest2) k i =
        qo k .fst , recoverQ cs (cong snd po) (cong snd qo) rest2 k i
    recoverQ {X = X} {R₂ = R₂} (Nonrec A k') {a1 , o1} {a2 , o2}
             po qo (h2 , rest2) k i =
        hp i , tailP i
      where
        B : A → Type _
        B a = Outputs (k' a) X
        hp : a2 ≡ qo k .fst
        hp i = qo (k ∨ ~ i) .fst
        qsub : transp (λ i → B (qo i .fst)) i0 o1 ≡ o2
        qsub = fromPathP (cong snd qo)
        IH : mapOutputs (k' a2) (graph2D-q R₂ k)
               (graphOutputs2D R₂ (k' a2)
                  (fromPathP (subst (λ h → PathP (λ i → B (h i)) o1 o2)
                                    h2 (cong snd po)))
                  qsub rest2)
             ≡ qsub k
        IH = recoverQ (k' a2) _ qsub rest2 k
        symPR : PathP (λ i → B (qo (k ∨ i) .fst)) (qo k .snd) (qsub k)
        symPR = (λ i → cong snd qo (k ∨ i)) ▷ (λ i → qsub (k ∨ ~ i))
        R : PathP (λ i → B (hp i)) (qsub k) (qo k .snd)
        R i = symPR (~ i)
        tailP : PathP (λ i → B (hp i))
                      (mapOutputs (k' a2) (graph2D-q R₂ k)
                        (graphOutputs2D R₂ (k' a2)
                          (fromPathP (subst (λ h → PathP (λ i → B (h i)) o1 o2)
                                            h2 (cong snd po)))
                          qsub rest2))
                      (qo k .snd)
        tailP = subst (λ z → PathP (λ i → B (hp i)) z (qo k .snd)) (sym IH) R

    {- Recovery lemma (p-side): like `recoverQ`, but the `Nonrec`
       case additionally undoes the `h2` re-basing of the `po` tail. -}
    recoverP :
        {X : Type ℓ} {R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ}
        (cs : DestrArity) {o1 o2 : Outputs cs X} (po qo : o1 ≡ o2)
        (W : OutputsRel2D cs R₂ po qo) (k : I)
      → mapOutputs cs (graph2D-p R₂ k) (graphOutputs2D R₂ cs po qo W) ≡ po k
    recoverP Done po qo W k = refl
    recoverP (Rec D cs) po qo (rrel2 , rest2) k i =
        po k .fst , recoverP cs (cong snd po) (cong snd qo) rest2 k i
    recoverP {X = X} {R₂ = R₂} (Nonrec A k') {a1 , o1} {a2 , o2}
             po qo (h2 , rest2) k i =
        hp i , tailP i
      where
        B : A → Type _
        B a = Outputs (k' a) X
        PSub : PathP (λ i → B (qo i .fst)) o1 o2
        PSub = subst (λ h → PathP (λ i → B (h i)) o1 o2) h2 (cong snd po)
        po-sub : transp (λ i → B (qo i .fst)) i0 o1 ≡ o2
        po-sub = fromPathP PSub
        SF : PathP (λ j → PathP (λ i → B (h2 j i)) o1 o2) (cong snd po) PSub
        SF = subst-filler (λ h → PathP (λ i → B (h i)) o1 o2) h2 (cong snd po)
        IH : mapOutputs (k' a2) (graph2D-p R₂ k)
               (graphOutputs2D R₂ (k' a2) po-sub (fromPathP (cong snd qo)) rest2)
             ≡ po-sub k
        IH = recoverP (k' a2) po-sub (fromPathP (cong snd qo)) rest2 k
        segA : a2 ≡ qo k .fst
        segA i = qo (k ∨ ~ i) .fst
        segB : qo k .fst ≡ po k .fst
        segB j = h2 (~ j) k
        hp : a2 ≡ po k .fst
        hp = compBase segA segB
        symRA : PathP (λ i → B (qo (k ∨ i) .fst)) (PSub k) (po-sub k)
        symRA = (λ i → PSub (k ∨ i)) ▷ (λ i → po-sub (k ∨ ~ i))
        RA : PathP (λ i → B (segA i)) (po-sub k) (PSub k)
        RA i = symRA (~ i)
        RB : PathP (λ j → B (segB j)) (PSub k) (po k .snd)
        RB j = SF (~ j) k
        R : PathP (λ i → B (hp i)) (po-sub k) (po k .snd)
        R = compPathP {A = A} {B = B} {bp = segA} {bq = segB} RA RB
        tailP : PathP (λ i → B (hp i))
                      (mapOutputs (k' a2) (graph2D-p R₂ k)
                        (graphOutputs2D R₂ (k' a2) po-sub
                          (fromPathP (cong snd qo)) rest2))
                      (po k .snd)
        tailP = subst (λ z → PathP (λ i → B (hp i)) z (po k .snd)) (sym IH) R

    {- The two edge projections are coalgebra homs from the 2-D graph
       coalgebra into `(X, destr)`, for each `k`. -}
    graph2D-p-hom :
        {sig : CoSignature} {X : Type ℓ} (destr : DestrAlgebra sig X)
        (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
        (bisim2D : isBisim2D sig destr R₂) (k : I)
        (op : Op sig) (g : Graph2D {X} R₂)
      → destr op (graph2D-p R₂ k g)
          ≡ mapOutputs (arity sig op) (graph2D-p R₂ k)
                       (graphCoalg2D destr R₂ bisim2D op g)
    graph2D-p-hom {sig = sig} destr R₂ bisim2D k op (a , b , p , q , r) =
        sym (recoverP (arity sig op) (cong (destr op) p) (cong (destr op) q)
                      (bisim2D r op) k)

    graph2D-q-hom :
        {sig : CoSignature} {X : Type ℓ} (destr : DestrAlgebra sig X)
        (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
        (bisim2D : isBisim2D sig destr R₂) (k : I)
        (op : Op sig) (g : Graph2D {X} R₂)
      → destr op (graph2D-q R₂ k g)
          ≡ mapOutputs (arity sig op) (graph2D-q R₂ k)
                       (graphCoalg2D destr R₂ bisim2D op g)
    graph2D-q-hom {sig = sig} destr R₂ bisim2D k op (a , b , p , q , r) =
        sym (recoverQ (arity sig op) (cong (destr op) p) (cong (destr op) q)
                      (bisim2D r op) k)

    {- Corner coincidence: at `k = i0`/`i1` the p- and q-recoveries
       agree (both project the same corner). -}
    recoverPQ-agree-0 :
        {X : Type ℓ} {R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ}
        (cs : DestrArity) {o1 o2 : Outputs cs X} (po qo : o1 ≡ o2)
        (W : OutputsRel2D cs R₂ po qo)
      → recoverP cs po qo W i0 ≡ recoverQ cs po qo W i0
    recoverPQ-agree-0 Done po qo W = refl
    recoverPQ-agree-0 (Rec D cs) po qo (rrel2 , rest2) j i =
        po i0 .fst , recoverPQ-agree-0 cs (cong snd po) (cong snd qo) rest2 j i
    recoverPQ-agree-0 {X = X} {R₂ = R₂} (Nonrec A k') {a1 , o1} {a2 , o2}
                      po qo (h2 , rest2) j i =
        compBase-refl segA j i , TAIL j i
      where
        B : A → Type _
        B a = Outputs (k' a) X
        segA : a2 ≡ a1
        segA i = qo (~ i) .fst
        PSub : PathP (λ i → B (qo i .fst)) o1 o2
        PSub = subst (λ h → PathP (λ i → B (h i)) o1 o2) h2 (cong snd po)
        po-sub : transp (λ i → B (qo i .fst)) i0 o1 ≡ o2
        po-sub = fromPathP PSub
        qsub : transp (λ i → B (qo i .fst)) i0 o1 ≡ o2
        qsub = fromPathP (cong snd qo)
        IHeq : recoverP (k' a2) po-sub qsub rest2 i0
                 ≡ recoverQ (k' a2) po-sub qsub rest2 i0
        IHeq = recoverPQ-agree-0 (k' a2) po-sub qsub rest2
        symRA symPRq : PathP (λ i → B (qo i .fst)) o1
                             (transp (λ i → B (qo i .fst)) i0 o1)
        symRA  = PSub          ▷ (λ i → po-sub (~ i))
        symPRq = (cong snd qo) ▷ (λ i → qsub (~ i))
        symRA≡symPRq : symRA ≡ symPRq
        symRA≡symPRq = ▷-sym-fromPathP PSub ∙ sym (▷-sym-fromPathP (cong snd qo))
        RA Rq : PathP (λ i → B (segA i))
                      (transp (λ i → B (qo i .fst)) i0 o1) o1
        RA i = symRA (~ i)
        Rq i = symPRq (~ i)
        RA≡Rq : PathP (λ _ → PathP (λ i → B (segA i)) (po-sub i0) o1) RA Rq
        RA≡Rq jj i = symRA≡symPRq jj (~ i)
        Rpath : PathP (λ l → PathP (λ i → B (compBase-refl segA l i)) (po-sub i0) o1)
                      (compPathP {A = A} {B = B} {bp = segA} {bq = λ _ → a1}
                                 RA (λ _ → o1))
                      Rq
        Rpath = compPathP-refl {A = A} {B = B} {bp = segA} RA ▷ RA≡Rq
        TAIL : (j₁ : I)
             → PathP (λ i → B (compBase-refl segA j₁ i))
                     (mapOutputs (k' a2) (graph2D-p R₂ i0)
                       (graphOutputs2D R₂ (k' a2) po-sub qsub rest2))
                     o1
        TAIL j₁ =
          subst (λ z → PathP (λ i → B (compBase-refl segA j₁ i)) z o1)
                (sym (IHeq j₁)) (Rpath j₁)

    recoverPQ-agree-1 :
        {X : Type ℓ} {R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ}
        (cs : DestrArity) {o1 o2 : Outputs cs X} (po qo : o1 ≡ o2)
        (W : OutputsRel2D cs R₂ po qo)
      → recoverP cs po qo W i1 ≡ recoverQ cs po qo W i1
    recoverPQ-agree-1 Done po qo W = refl
    recoverPQ-agree-1 (Rec D cs) po qo (rrel2 , rest2) j i =
        po i1 .fst , recoverPQ-agree-1 cs (cong snd po) (cong snd qo) rest2 j i
    recoverPQ-agree-1 {X = X} {R₂ = R₂} (Nonrec A k') {a1 , o1} {a2 , o2}
                      po qo (h2 , rest2) j i =
        compBase-refl segA j i , TAIL j i
      where
        B : A → Type _
        B a = Outputs (k' a) X
        segA : a2 ≡ a2
        segA i = qo (i1 ∨ ~ i) .fst
        PSub : PathP (λ i → B (qo i .fst)) o1 o2
        PSub = subst (λ h → PathP (λ i → B (h i)) o1 o2) h2 (cong snd po)
        po-sub : transp (λ i → B (qo i .fst)) i0 o1 ≡ o2
        po-sub = fromPathP PSub
        qsub : transp (λ i → B (qo i .fst)) i0 o1 ≡ o2
        qsub = fromPathP (cong snd qo)
        IHeq : recoverP (k' a2) po-sub qsub rest2 i1
                 ≡ recoverQ (k' a2) po-sub qsub rest2 i1
        IHeq = recoverPQ-agree-1 (k' a2) po-sub qsub rest2
        symRA symPRq : PathP (λ i → B (qo (i1 ∨ i) .fst)) o2 o2
        symRA  = (λ i → PSub (i1 ∨ i))        ▷ (λ i → po-sub (i1 ∨ ~ i))
        symPRq = (λ i → (cong snd qo) (i1 ∨ i)) ▷ (λ i → qsub (i1 ∨ ~ i))
        RA Rq : PathP (λ i → B (segA i)) o2 o2
        RA i = symRA (~ i)
        Rq i = symPRq (~ i)
        RA≡Rq : PathP (λ _ → PathP (λ i → B (segA i)) o2 o2) RA Rq
        RA≡Rq jj i = symRA (~ i)
        Rpath : PathP (λ l → PathP (λ i → B (compBase-refl segA l i)) o2 o2)
                      (compPathP {A = A} {B = B} {bp = segA} {bq = λ _ → a2}
                                 RA (λ _ → o2))
                      Rq
        Rpath = compPathP-refl {A = A} {B = B} {bp = segA} RA ▷ RA≡Rq
        TAIL : (j₁ : I)
             → PathP (λ i → B (compBase-refl segA j₁ i))
                     (mapOutputs (k' a2) (graph2D-p R₂ i1)
                       (graphOutputs2D R₂ (k' a2) po-sub qsub rest2))
                     o2
        TAIL j₁ =
          subst (λ z → PathP (λ i → B (compBase-refl segA j₁ i)) z o2)
                (sym (IHeq j₁)) (Rpath j₁)


    {-
        Definition 4.18 (Homotopy Coinductive Configuration): `HCoindCoalg`
        An `HCoindCoalg`: `corec` and `corec-β` together with
        Σ-level uniqueness of the coalg-hom space — i.e., the
        coalg-hom Σ-space into `X` is contractible, the
        syntactic-framework analog of `isHFinal`. `corec-η`
        is derived by projecting `corec-uniq-Σ` pointwise (so the
        η-path and the Σ-structure agree on the nose); the
        underlying `CoindCoalg` is exposed as `asCoindCoalg`.
    -}
    record HCoindCoalg (sig : CoSignature) (X : Type ℓ)
                     : Type (lsuc ℓ) where
      field
        destr   : DestrAlgebra sig X
        corec   : {C : Type ℓ} → DestrAlgebra sig C → C → X
        corec-β : {C : Type ℓ} (destrC : DestrAlgebra sig C) →
                  (op : Op sig) (c : C) →
                  destr op (corec destrC c)
                    ≡ mapOutputs (arity sig op) (corec destrC) (destrC op c)

        {-
            Σ-uniqueness of coalg-homs into `X`: `(h, h-hom)` is
            Σ-equal to `(corec, corec-β)`. Combined with `corec`
            and `corec-β` this is h-finality.
        -}
        corec-uniq-Σ :
            {C : Type ℓ} (destrC : DestrAlgebra sig C)
            (h : C → X)
            (h-hom : (op : Op sig) (c : C) →
                     destr op (h c)
                       ≡ mapOutputs (arity sig op) h (destrC op c)) →
            Σ (h ≡ corec destrC)
              (λ p →
                 PathP (λ i → (op : Op sig) (c : C) →
                              destr op (p i c)
                                ≡ mapOutputs (arity sig op)
                                             (p i) (destrC op c))
                       h-hom (corec-β destrC))

      -- Derived `corec-η`: pointwise projection of `corec-uniq-Σ`.
      corec-η :
          {C : Type ℓ} (destrC : DestrAlgebra sig C) (h : C → X) →
          ((op : Op sig) (c : C) →
           destr op (h c)
             ≡ mapOutputs (arity sig op) h (destrC op c)) →
          (c : C) → h c ≡ corec destrC c
      corec-η destrC h h-hom c i = fst (corec-uniq-Σ destrC h h-hom) i c

      {-
          The 2-cell square supplied by `corec-uniq-Σ`'s second
          component: the hom-witness `h-hom op c` connects to
          `corec-β destrC op c` over `cong (destr op)` of the
          η-path. This is the Σ-level strength that plain
          `corec-η` cannot give; it makes
          `cong (destr op) (deriveCoind …)` computable.
      -}
      destr-corec-η-sq :
          {C : Type ℓ} (destrC : DestrAlgebra sig C) (h : C → X)
          (h-hom : (op : Op sig) (c : C) →
                   destr op (h c)
                     ≡ mapOutputs (arity sig op) h (destrC op c))
          (op : Op sig) (c : C) →
          PathP (λ i → destr op (fst (corec-uniq-Σ destrC h h-hom) i c)
                         ≡ mapOutputs (arity sig op)
                                      (fst (corec-uniq-Σ destrC h h-hom) i)
                                      (destrC op c))
                (h-hom op c) (corec-β destrC op c)
      destr-corec-η-sq destrC h h-hom op c i =
          snd (corec-uniq-Σ destrC h h-hom) i op c

      {-
          The keystone square in `∙`-form (via `Square→∙`):
          `cong (destr op) (corec-η …)` as a computable composite.
      -}
      destr-corec-η :
          {C : Type ℓ} (destrC : DestrAlgebra sig C) (h : C → X)
          (h-hom : (op : Op sig) (c : C) →
                   destr op (h c)
                     ≡ mapOutputs (arity sig op) h (destrC op c))
          (op : Op sig) (c : C) →
          cong (destr op) (corec-η destrC h h-hom c) ∙ corec-β destrC op c
            ≡ h-hom op c
              ∙ (λ i → mapOutputs (arity sig op)
                                  (fst (corec-uniq-Σ destrC h h-hom) i)
                                  (destrC op c))
      destr-corec-η destrC h h-hom op c =
          Square→∙ (destr-corec-η-sq destrC h h-hom op c)

      {-
          Project down to a `CoindCoalg`, using the derived
          `corec-η` (consistent with `corec-uniq-Σ` by
          construction).
      -}
      asCoindCoalg : CoindCoalg sig X
      asCoindCoalg = record
        { destr   = destr
        ; corec   = corec
        ; corec-β = corec-β
        ; corec-η = corec-η
        }


    {-
       The destructor-β rule for the derived coinduction, over an
       `HCoindCoalg` (route (a) toward `coind-ok-strict`). The
       1-cell uniqueness in plain `CoindCoalg` cannot characterise
       `cong (destr op) (deriveCoind …)`; the Σ-level strength of
       `HCoindCoalg` can, via `destr-corec-η`.
    -}
    module HDeriveCoind
        {sig : CoSignature} {X : Type ℓ} (hind : HCoindCoalg sig X)
        (R : X → X → Type ℓ)
        (bisim : isBisim sig (HCoindCoalg.destr hind) R) where
      open HCoindCoalg hind
      module D = DeriveCoind asCoindCoalg R bisim

      {-
          The `bot` edge of `destr-corec-η` for one projection:
          the `mapOutputs`-cong of that projection's η-path.
      -}
      mapPath : (proj : Graph X R → X)
                (proj-hom : (op : Op sig) (g : Graph X R) →
                            destr op (proj g)
                              ≡ mapOutputs (arity sig op) proj (D.graphCoalg op g))
                (op : Op sig) (g : Graph X R) →
                mapOutputs (arity sig op) proj (D.graphCoalg op g)
                  ≡ mapOutputs (arity sig op) (corec D.graphCoalg) (D.graphCoalg op g)
      mapPath proj proj-hom op g i =
          mapOutputs (arity sig op)
                     (fst (corec-uniq-Σ D.graphCoalg proj proj-hom) i)
                     (D.graphCoalg op g)

      {-
          `cong (destr op) (coind r)` characterised: the two
          `corec-β` terms from the per-projection destructor-β
          cancel (`lCancel`), leaving the two projection
          hom-witnesses and `mapPath`s.
      -}
      coind-destr-β : (op : Op sig) {x y : X} (r : R x y) →
          cong (destr op) (D.coind r)
            ≡ (D.proj1-hom op (x , y , r) ∙ mapPath D.proj1 D.proj1-hom op (x , y , r))
              ∙ sym (D.proj2-hom op (x , y , r) ∙ mapPath D.proj2 D.proj2-hom op (x , y , r))
      coind-destr-β op {x} {y} r =
            cong-∙ (destr op) (D.proj1-eq gC) (sym (D.proj2-eq gC))
          ∙ cong (_∙ sym A₂) A₁≡
          ∙ cong ((B₁ ∙ sym cβ) ∙_) (cong sym A₂≡)
          ∙ cong ((B₁ ∙ sym cβ) ∙_) (symDist B₂ (sym cβ))
          ∙ ∙assoc B₁ (sym cβ) (cβ ∙ sym B₂)
          ∙ cong (B₁ ∙_) (sym (∙assoc (sym cβ) cβ (sym B₂)))
          ∙ cong (λ z → B₁ ∙ (z ∙ sym B₂)) (lCancel cβ)
          ∙ cong (B₁ ∙_) (∙-idl (sym B₂))
        where
          gC : Graph X R
          gC = x , y , r

          cβ : destr op (corec D.graphCoalg gC)
                 ≡ mapOutputs (arity sig op) (corec D.graphCoalg) (D.graphCoalg op gC)
          cβ = corec-β D.graphCoalg op gC

          A₁ = cong (destr op) (D.proj1-eq gC)
          A₂ = cong (destr op) (D.proj2-eq gC)
          B₁ = D.proj1-hom op gC ∙ mapPath D.proj1 D.proj1-hom op gC
          B₂ = D.proj2-hom op gC ∙ mapPath D.proj2 D.proj2-hom op gC

          A₁≡ : A₁ ≡ B₁ ∙ sym cβ
          A₁≡ = sym (∙-idr A₁)
              ∙ cong (A₁ ∙_) (sym (rCancel cβ))
              ∙ sym (∙assoc A₁ cβ (sym cβ))
              ∙ cong (_∙ sym cβ) (destr-corec-η D.graphCoalg D.proj1 D.proj1-hom op gC)

          A₂≡ : A₂ ≡ B₂ ∙ sym cβ
          A₂≡ = sym (∙-idr A₂)
              ∙ cong (A₂ ∙_) (sym (rCancel cβ))
              ∙ sym (∙assoc A₂ cβ (sym cβ))
              ∙ cong (_∙ sym cβ) (destr-corec-η D.graphCoalg D.proj2 D.proj2-hom op gC)

      {-
          The deriveCoind structural-β. Observing a coinduction
          path `coind r` through a destructor `destr op` yields
          exactly the bisimulation `bisim r op` *realized*
          (`realize`). This is first-order — no 2-D principle —
          hence the bootstrap for the strict `coind-ok` is not
          circular: via `coind-destr-β`, `cong (destr op)(coind r)`
          is `BB₁ ∙ sym BB₂` through the graph midpoint `Mid`, and
          the recursive `L` matches that to `realize` (at `Rec`
          children this is `corec-β`-definitional; the `Nonrec`
          telescope is discharged by `J` on the head + `subst-slide`).
      -}
      ηpath1 = fst (corec-uniq-Σ D.graphCoalg D.proj1 D.proj1-hom)
      ηpath2 = fst (corec-uniq-Σ D.graphCoalg D.proj2 D.proj2-hom)

      Mid : (cs : DestrArity) (o1 o2 : Outputs cs X)
            (w : OutputsRel cs R o1 o2) → Outputs cs X
      Mid cs o1 o2 w = mapOutputs cs (corec D.graphCoalg) (graphOutputs cs o1 o2 w)

      BB₁ : (cs : DestrArity) (o1 o2 : Outputs cs X) (w : OutputsRel cs R o1 o2)
          → o1 ≡ Mid cs o1 o2 w
      BB₁ cs o1 o2 w =
          sym (D.graph-proj1 cs o1 o2 w)
        ∙ (λ i → mapOutputs cs (ηpath1 i) (graphOutputs cs o1 o2 w))

      BB₂ : (cs : DestrArity) (o1 o2 : Outputs cs X) (w : OutputsRel cs R o1 o2)
          → o2 ≡ Mid cs o1 o2 w
      BB₂ cs o1 o2 w =
          sym (D.graph-proj2 cs o1 o2 w)
        ∙ (λ i → mapOutputs cs (ηpath2 i) (graphOutputs cs o1 o2 w))

      L : (cs : DestrArity) (o1 o2 : Outputs cs X) (w : OutputsRel cs R o1 o2)
        → BB₁ cs o1 o2 w ∙ sym (BB₂ cs o1 o2 w)
            ≡ realize cs asCoindCoalg R bisim w
      L Done o1 o2 w = rCancel (BB₁ Done o1 o2 w)
      L (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest) i j =
          fstEq2 i j , sndEq2 i j
        where
          B1 = BB₁ (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest)
          B2 = BB₂ (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest)
          lhs = B1 ∙ sym B2

          mp1R = λ i → mapOutputs (Rec D' cs) (ηpath1 i)
                         (graphOutputs (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest))
          mp2R = λ i → mapOutputs (Rec D' cs) (ηpath2 i)
                         (graphOutputs (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest))

          cong-snd-BB₁ : cong (λ o → snd o) B1 ≡ BB₁ cs oo1 oo2 rest
          cong-snd-BB₁ = cong-∙ (λ o → snd o)
                           (sym (D.graph-proj1 (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest)))
                           mp1R
          cong-snd-BB₂ : cong (λ o → snd o) B2 ≡ BB₂ cs oo1 oo2 rest
          cong-snd-BB₂ = cong-∙ (λ o → snd o)
                           (sym (D.graph-proj2 (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest)))
                           mp2R

          sndEq2 : cong (λ o → snd o) lhs ≡ realize cs asCoindCoalg R bisim rest
          sndEq2 = cong-∙ (λ o → snd o) B1 (sym B2)
                 ∙ cong₂ _∙_ cong-snd-BB₁ (cong sym cong-snd-BB₂)
                 ∙ L cs oo1 oo2 rest

          ptwise : (d : D') → cong (λ o → fst o d) lhs
                                ≡ deriveCoind asCoindCoalg R bisim (rrel d)
          ptwise d =
              cong-∙ (λ o → fst o d) B1 (sym B2)
            ∙ cong₂ _∙_
                (cong-∙ (λ o → fst o d)
                   (sym (D.graph-proj1 (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest)))
                   mp1R)
                (cong sym (cong-∙ (λ o → fst o d)
                   (sym (D.graph-proj2 (Rec D' cs) (r1 , oo1) (r2 , oo2) (rrel , rest)))
                   mp2R))
            ∙ cong₂ _∙_ (∙-idl (D.proj1-eq (r1 d , r2 d , rrel d)))
                        (cong sym (∙-idl (D.proj2-eq (r1 d , r2 d , rrel d))))

          fstEq2 : cong (λ o → fst o) lhs
                     ≡ (λ j d → deriveCoind asCoindCoalg R bisim (rrel d) j)
          fstEq2 i j d = ptwise d i j
      L (Nonrec A k) (a1 , oo1) (a2 , oo2) (hp , rest) =
          J (λ a2' hp' → (o2' : Outputs (k a2') X)
                         (rest' : OutputsRel (k a2') R (subst (λ a → Outputs (k a) X) hp' oo1) o2') →
                BB₁ (Nonrec A k) (a1 , oo1) (a2' , o2') (hp' , rest')
                  ∙ sym (BB₂ (Nonrec A k) (a1 , oo1) (a2' , o2') (hp' , rest'))
                  ≡ realize (Nonrec A k) asCoindCoalg R bisim (hp' , rest'))
            base hp oo2 rest
        where
          base : (o2' : Outputs (k a1) X)
                 (rest' : OutputsRel (k a1) R (subst (λ a → Outputs (k a) X) refl oo1) o2') →
               BB₁ (Nonrec A k) (a1 , oo1) (a1 , o2') (refl , rest')
                 ∙ sym (BB₂ (Nonrec A k) (a1 , oo1) (a1 , o2') (refl , rest'))
                 ≡ realize (Nonrec A k) asCoindCoalg R bisim (refl , rest')
          base o2' rest' =
              cong₂ _∙_ BB₁refl (cong sym BB₂refl)
            ∙ sym (cong-∙ (a1 ,_) (sym sr ∙ B1') (sym B2'))
            ∙ cong (cong (a1 ,_))
                (∙assoc (sym sr) B1' (sym B2')
                  ∙ cong (sym sr ∙_) (L (k a1) oo1' o2' rest'))
            ∙ step4
            where
              oo1' : Outputs (k a1) X
              oo1' = subst (λ a → Outputs (k a) X) refl oo1

              sr : oo1' ≡ oo1
              sr = substRefl (λ a → Outputs (k a) X) oo1

              gp1' = D.graph-proj1 (k a1) oo1' o2' rest'
              gp2' = D.graph-proj2 (k a1) oo1' o2' rest'
              mp1' = λ i → mapOutputs (k a1) (ηpath1 i) (graphOutputs (k a1) oo1' o2' rest')
              mp2' = λ i → mapOutputs (k a1) (ηpath2 i) (graphOutputs (k a1) oo1' o2' rest')

              B1' = BB₁ (k a1) oo1' o2' rest'
              B2' = BB₂ (k a1) oo1' o2' rest'

              BB₂refl : BB₂ (Nonrec A k) (a1 , oo1) (a1 , o2') (refl , rest')
                          ≡ cong (a1 ,_) B2'
              BB₂refl = sym (cong-∙ (a1 ,_) (sym gp2') mp2')

              BB₁refl : BB₁ (Nonrec A k) (a1 , oo1) (a1 , o2') (refl , rest')
                          ≡ cong (a1 ,_) (sym sr ∙ B1')
              BB₁refl =
                  cong (_∙ cong (a1 ,_) mp1') (cong sym (sym (cong-∙ (a1 ,_) gp1' sr)))
                ∙ sym (cong-∙ (a1 ,_) (sym (gp1' ∙ sr)) mp1')
                ∙ cong (cong (a1 ,_))
                    (cong (_∙ mp1') (symDist gp1' sr)
                      ∙ ∙assoc (sym sr) (sym gp1') mp1')

              step4 : cong (a1 ,_) (sym sr ∙ realize (k a1) asCoindCoalg R bisim rest')
                        ≡ realize (Nonrec A k) asCoindCoalg R bisim (refl , rest')
              step4 = cong (cong (a1 ,_))
                        (sym (subst-slide sr (realize (k a1) asCoindCoalg R bisim rest')))

      coind-realize : (op : Op sig) {x y : X} (r : R x y)
                    → cong (destr op) (D.coind r)
                        ≡ realize (arity sig op) asCoindCoalg R bisim (bisim r op)
      coind-realize op {x} {y} r =
          coind-destr-β op r
        ∙ L (arity sig op) (destr op x) (destr op y) (bisim r op)


    {-
        The 2-D coinduction principle, derived from `corec-uniq-Σ`:
        the edge projections `graph2D-p/q` are coalgebra homs into
        `X`, `corec-uniq-Σ` sends each to the corecursor, and the
        2-cell `p ≡ q` is a `primHComp` coning along those σ-paths,
        with corners closed by `σ-corner-0/1`.
    -}
    module DeriveCoind2D
        {sig : CoSignature} {X : Type ℓ} (hind : HCoindCoalg sig X)
        (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
        (bisim2D : isBisim2D sig (HCoindCoalg.destr hind) R₂) where
      open HCoindCoalg hind

      gc : DestrAlgebra sig (Graph2D R₂)
      gc = graphCoalg2D destr R₂ bisim2D

      co : Graph2D R₂ → X
      co = corec gc

      σ-p : (k : I) → graph2D-p R₂ k ≡ co
      σ-p k = fst (corec-uniq-Σ gc (graph2D-p R₂ k)
                                (graph2D-p-hom destr R₂ bisim2D k))
      σ-q : (k : I) → graph2D-q R₂ k ≡ co
      σ-q k = fst (corec-uniq-Σ gc (graph2D-q R₂ k)
                                (graph2D-q-hom destr R₂ bisim2D k))

      -- Corner coherence, at the *witness* level: the p/q hom-witnesses
      -- coincide at `i0`/`i1`, hence so do their σ-paths — definitionally
      -- at the endpoints.
      σ-corner-0 : σ-p i0 ≡ σ-q i0
      σ-corner-0 jj = fst (corec-uniq-Σ gc (graph2D-p R₂ i0) (homEq jj))
        where
          homEq : (jj : I) (op : Op sig) (g : Graph2D R₂)
                → destr op (graph2D-p R₂ i0 g)
                    ≡ mapOutputs (arity sig op) (graph2D-p R₂ i0) (gc op g)
          homEq jj op (a , b , p , q , r) =
            sym (recoverPQ-agree-0 (arity sig op) (cong (destr op) p)
                                   (cong (destr op) q) (bisim2D r op) jj)
      σ-corner-1 : σ-p i1 ≡ σ-q i1
      σ-corner-1 jj = fst (corec-uniq-Σ gc (graph2D-p R₂ i1) (homEq jj))
        where
          homEq : (jj : I) (op : Op sig) (g : Graph2D R₂)
                → destr op (graph2D-p R₂ i1 g)
                    ≡ mapOutputs (arity sig op) (graph2D-p R₂ i1) (gc op g)
          homEq jj op (a , b , p , q , r) =
            sym (recoverPQ-agree-1 (arity sig op) (cong (destr op) p)
                                   (cong (destr op) q) (bisim2D r op) jj)

      -- The square of functions coning to `co`; corners meet definitionally.
      funSq : (i k : I) → Graph2D R₂ → X
      funSq i k =
        primHComp (λ l → λ where
                    (i = i0) → σ-p k (~ l)
                    (i = i1) → σ-q k (~ l)
                    (k = i0) → σ-corner-0 i (~ l)
                    (k = i1) → σ-corner-1 i (~ l))
                  co

      result : ∀ {a b} {p q : a ≡ b} → R₂ p q → p ≡ q
      result {a} {b} {p} {q} r i k = funSq i k (a , b , p , q , r)

    -- Proposition 4.19 (proof of `coind_ok`): the 2-D coinduction
    -- principle, derived from `corec-uniq-Σ` (no longer postulated).
    deriveCoind2D :
        {sig : CoSignature} {X : Type ℓ} (hind : HCoindCoalg sig X)
        (R₂ : {a b : X} → a ≡ b → a ≡ b → Type ℓ)
        (bisim2D : isBisim2D sig (HCoindCoalg.destr hind) R₂)
      → ∀ {a b} {p q : a ≡ b} → R₂ p q → p ≡ q
    deriveCoind2D hind R₂ bisim2D = DeriveCoind2D.result hind R₂ bisim2D

    {-
       Configurations (records, parallel to `inductive-repair.config`)
       -}

    {-
      Definition 4.17 (Coinductive Configuration)
        A `CoConfig`: two `CoindCoalg`s for the common signature,
        `C` the old carrier and `D` the new one.
    -}
    record CoConfig (sig : CoSignature) (C D : Type ℓ)
                    : Type (lsuc ℓ) where
      field
        coindCoalgC : CoindCoalg sig C
        coindCoalgD : CoindCoalg sig D

    {-
      Definition 4.18 (Homotopy Coinductive Configuration)
        An `HCoConfig`: two `HCoindCoalg`s. The strict-equation
        `coind_ok` lives over this tier; it projects down to a
        `CoConfig` by dropping the Σ-uniqueness fields.
    -}
    record HCoConfig (sig : CoSignature) (C D : Type ℓ)
                     : Type (lsuc ℓ) where
      field
        hCoindCoalgC : HCoindCoalg sig C
        hCoindCoalgD : HCoindCoalg sig D

      coindCoalgC : CoindCoalg sig C
      coindCoalgC = HCoindCoalg.asCoindCoalg hCoindCoalgC

      coindCoalgD : CoindCoalg sig D
      coindCoalgD = HCoindCoalg.asCoindCoalg hCoindCoalgD

      coConfig : CoConfig sig C D
      coConfig = record { coindCoalgC = coindCoalgC ; coindCoalgD = coindCoalgD }

    {-
       Equivalences from configurations
    -}

    open _≃_

    {-
        A `CoConfig` yields an equivalence `C ≃ D`: the maps are
        the two cross-corecursors, and each round-trip is a
        coalgebra-hom identified with the identity by `corec-η`.
    -}
    coConfigToEquiv : {sig : CoSignature} {C D : Type ℓ} →
                      CoConfig sig C D → C ≃ D
    coConfigToEquiv {sig = sig} {C = C} {D = D} cfg = record
        { fwd      = f-fun
        ; bwd-L    = g-fun
        ; leftInv  = η-pf
        ; bwd-R    = g-fun
        ; rightInv = ε-pf
        }
      where
        open CoConfig cfg
        open CoindCoalg coindCoalgC
          renaming (destr to destrC; corec to corecC;
                    corec-β to corecC-β; corec-η to corecC-η)
        open CoindCoalg coindCoalgD
          renaming (destr to destrD; corec to corecD;
                    corec-β to corecD-β; corec-η to corecD-η)

        f-fun : C → D
        f-fun = corecD destrC

        g-fun : D → C
        g-fun = corecC destrD

        -- `g ∘ f` is a coalgebra-hom of `(C, destrC)`: chain the
        -- two β-rules and collapse with `mapOutputs-∘`.
        compose-is-hom :
            (op : Op sig) (c : C) →
            destrC op (g-fun (f-fun c))
              ≡ mapOutputs (arity sig op)
                           (λ c' → g-fun (f-fun c')) (destrC op c)
        compose-is-hom op c =
            corecC-β destrD op (f-fun c)
          ∙ cong (mapOutputs (arity sig op) g-fun) (corecD-β destrC op c)
          ∙ mapOutputs-∘ (arity sig op) f-fun g-fun (destrC op c)

        -- `id` is a coalgebra-hom by `mapOutputs-id`.
        id-is-hom :
            (op : Op sig) (c : C) →
            destrC op c
              ≡ mapOutputs (arity sig op) (λ c' → c') (destrC op c)
        id-is-hom op c = sym (mapOutputs-id (arity sig op) (destrC op c))

        η-pf : (c : C) → g-fun (f-fun c) ≡ c
        η-pf c =
            corecC-η destrC (λ c' → g-fun (f-fun c'))
                     compose-is-hom c
          ∙ sym (corecC-η destrC (λ c' → c') id-is-hom c)

        -- Symmetric round-trip on the D side, identical
        -- structure with the roles of C and D swapped.
        compose-is-hom-D :
            (op : Op sig) (d : D) →
            destrD op (f-fun (g-fun d))
              ≡ mapOutputs (arity sig op)
                           (λ d' → f-fun (g-fun d')) (destrD op d)
        compose-is-hom-D op d =
            corecD-β destrC op (g-fun d)
          ∙ cong (mapOutputs (arity sig op) f-fun) (corecC-β destrD op d)
          ∙ mapOutputs-∘ (arity sig op) g-fun f-fun (destrD op d)

        id-is-hom-D :
            (op : Op sig) (d : D) →
            destrD op d
              ≡ mapOutputs (arity sig op) (λ d' → d') (destrD op d)
        id-is-hom-D op d = sym (mapOutputs-id (arity sig op) (destrD op d))

        ε-pf : (d : D) → f-fun (g-fun d) ≡ d
        ε-pf d =
            corecD-η destrD (λ d' → f-fun (g-fun d'))
                     compose-is-hom-D d
          ∙ sym (corecD-η destrD (λ d' → d') id-is-hom-D d)



