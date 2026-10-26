{-# OPTIONS --cubical --guardedness #-}

{- Index of the artifact: imports every module referenced in the paper. -}
module everything where

-- Shared basics
import common
import palg

-- Inductive repair
import inductive-repair.indspec
import inductive-repair.indalg-prop
import inductive-repair.config
import inductive-repair.coherence
import inductive-repair.wtype-config
import inductive-repair.palg-config
import inductive-repair.palg-coherence
import inductive-repair.conversion
import inductive-repair.alg-iso
import inductive-repair.bridge
import inductive-repair.config-alg-equiv
import inductive-repair.repair-ops
import inductive-repair.examples.nat
import inductive-repair.examples.finvec

-- Coinductive repair (cubical)
import coinductive-repair.cubical-common
import coinductive-repair.mtype
import coinductive-repair.coalg
import coinductive-repair.config
import coinductive-repair.coherence
import coinductive-repair.coconfig-coalg-equiv
import coinductive-repair.mtype-config
import coinductive-repair.examples.stream
