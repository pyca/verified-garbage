module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import

/-! # Workspace entry to the native-word import -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Import
open VG VG.X86

def args (count out : Nat) : List Instr :=
  [.mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 (out + 4 * (count - 1)))),
    .mov .ecx (.imm (BitVec.ofNat 32 count))]

def load (count out : Nat) : Prog isa := .seq (.block (args count out)) code

end VG.Impl.RsaKeyGen.X86.Import
