module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace

/-! Reuse DSA's verified public exponentiation for generator construction. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout

def generatorFields (len : Nat) : List Instr :=
  [movi .x3 VG.Impl.Dsa.Generation.Layout.p, .add .x .x3 .x0 .x3, .str .x .x3 .x0 Field.p.offset,
   movi .x3 VG.Impl.Dsa.Generation.Layout.exponent, .add .x .x3 .x0 .x3, .str .x .x3 .x0 Field.x.offset,
   movi .x3 len, .str .x .x3 .x0 Field.pLen.offset]

def generatorModulus (len : Nat) : Prog isa :=
  seqs [.block SignVerify.parent, .block (generatorFields len),
    SignVerify.child pWorkspace ⟨.input .p, .pLen⟩]

def generatorPower (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Core.publicPow mul pWorkspace ⟨.input .g, .pLen⟩ ⟨.input .x, .pLen⟩
    ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩

def generatorPowerFresh (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  .seq (generatorModulus len) (generatorPower mul)

end VG.Impl.Dsa.AArch64.Generation
