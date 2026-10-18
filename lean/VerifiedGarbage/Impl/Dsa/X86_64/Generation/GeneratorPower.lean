module

public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Impl.Dsa.Generation.Layout

/-! # Reuse DSA's public exponentiation for generator construction -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout

def generatorFields (len : Nat) : List Instr :=
  [.mov .rax (.reg .rdi), .alu .add .rax (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p)),
   .store (Core.field .p) .rax,
   .mov .rax (.reg .rdi), .alu .add .rax (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent)),
   .store (Core.field .x) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 len)), .store (Core.field .pLen) .rax]

def generatorModulus (len : Nat) : Prog isa :=
  seqs [.block SignVerify.parent, .block (generatorFields len),
    SignVerify.child pWorkspace ⟨.input .p, .pLen⟩]

/-- Field g holds the current h input, x holds the saved (p−1)/q exponent. -/
def generatorPower (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Core.publicPow sq mul pWorkspace ⟨.input .g, .pLen⟩ ⟨.input .x, .pLen⟩
    ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩

/-- A valid h candidate does not depend on a previous parent workspace. -/
def generatorPowerFresh (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (len : Nat) : Prog isa :=
  .seq (generatorModulus len) (generatorPower sq mul)

end VG.Impl.Dsa.X86_64.Generation
