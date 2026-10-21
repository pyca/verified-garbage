module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Sieve
public import VerifiedGarbage.Impl.Mont.X86

/-! # A candidate sieve owns its frame and recovers the workspace without a saved register -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateSieve
open VG VG.X86 VG.Impl.Mont.X86

def setup : List Instr := [.alu .add .edi (.imm 256)]
def restore : List Instr := [.mov .edi (.mem (at_ .esp 0)), .alu .sub .edi (.imm 256)]
def body (w : Nat) : Prog isa :=
  .seq (.block setup) (.seq (Sieve.body Sieve.stackSlots w) (.block restore))
def code (w : Nat) : Prog isa := .frame (.alloc 20) (body w) (.free 20)

end VG.Impl.RsaKeyGen.X86.CandidateSieve
