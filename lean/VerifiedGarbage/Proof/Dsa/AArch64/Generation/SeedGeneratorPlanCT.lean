module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
public import Mathlib.Tactic.Push
public import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
/-! # Public accepted primes determine the generator-search plan -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeometryGeneratorWork.lean`, which only this module imported.
section

/-! # Geometry of the generator's parent and arithmetic workspaces -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeometryGenerator.lean`, which only this module imported.
section

/-! # Concrete generator plan over the saved p and exponent buffers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/ContextGenerator.lean`, which only this module imported.
section

/-! # Saved p and exponent bytes supply the complete generator search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure SeedGeneratorPublic where
  seed : SeedPublic
  value : Nat
  domain : VG.Proof.Dsa.Generation.PDomain seed.context.geo.pLen value

def SeedGeneratorPublic.qValue (p : SeedGeneratorPublic) : Nat :=
  Spec.Dsa.qCandidate (8 * p.seed.context.geo.qLen) p.seed.seed.bytes

def SeedGeneratorBefore (pLen qLen : Nat) (p : SeedGeneratorPublic) (s : State) : Prop :=
  SeedPrimeBefore pLen qLen p.seed s ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.seed.context.geo.B exponent) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue)

end VG.Proof.Dsa.AArch64.Generation
