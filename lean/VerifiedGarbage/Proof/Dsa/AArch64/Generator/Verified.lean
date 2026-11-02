module

import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Correct
import VerifiedGarbage.Proof.Dsa.AArch64.Generator.CT
import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Satisfiable
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Depth
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Public
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchCTState
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Public
public meta import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-! # `vg_dsa_generator_{bits}` on AArch64 is verified

For each Miller–Rabin round implementation, whose Montgomery multiplication
the stage's arithmetic inlines. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64

/-- The stage's code with the round implementation `v`'s arithmetic. -/
abbrev stageCode (v : RoundImpl) (pLen : Nat) : Prog isa :=
  Impl.Dsa.AArch64.Generator.code v.mont.mm pLen

theorem verified (v : RoundImpl) {pLen : Nat} (hb : Supported pLen) :
    Verified target (stageCode v pLen) (contract pLen) :=
  ⟨correct v.mont hb, code_ct v.mont hb, satisfiable hb⟩

/-- The stages with the round implementation `v`, as parameter generation
calls them. -/
def generatorStage (v : RoundImpl) : VG.Proof.Dsa.AArch64.Generation.GeneratorStage where
  name pLen := s!"vg_dsa_generator_{8 * (Impl.Dsa.AArch64.Generator.layout pLen).pLen}" ++ v.suffix
  code := stageCode v
  verified _ hb := verified v hb
  depth := code_depth v

end VG.Proof.Dsa.AArch64.Generator
