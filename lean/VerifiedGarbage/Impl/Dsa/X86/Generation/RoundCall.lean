module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Witness

/-! Call any shared prepared-round variant on the retained compact workspace. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def roundArguments : List Instr :=
  [.mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.arithmetic)),
    .store (at_ .esp 0) .eax, .mov .eax (.imm 1536), .store (at_ .esp 4) .eax]

def roundCall (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 8) (.seq (.block roundArguments) (.call name code)) (.free 8)

def sampleRound (name : String) (code : Prog isa) (n len : Nat) : Prog isa :=
  .seq (sampleWitness n len) (.seq (encodeWitness n) (roundCall name code))

end VG.Impl.Dsa.X86.Generation
