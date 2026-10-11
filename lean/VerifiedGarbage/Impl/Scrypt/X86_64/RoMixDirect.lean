module

public import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix

/-! ROMix filling V directly: copy X to V[0] once, then write each BlockMix
result to the next V slot, except the final result which goes back to b. -/

@[expose] public section

namespace VG.Impl.Scrypt.X86_64
open VG.X86_64

def fillInit : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
    .shift .shr .rcx 4]) copyLoop

def fillArgs : List Instr :=
  [.mov .rdi (.reg .rbp), .mov .rsi (.reg .r14), .shift .shr .rsi 7,
   .mov .rcx (.reg .rsi), .mov .rdx (.reg .rbp), .alu .add .rdx (.reg .r14),
   .mov .r8 (.reg .r13), .alu .cmp .r15 (.imm 1)]

def fillSelect : Prog isa :=
  .ite .e (.block [.mov .rdx (.reg .rbx)]) (.block [])

def fillStep (bm : Prog isa) : Prog isa :=
  .seq (.seq (.block fillArgs) fillSelect) <|
  .seq (.call "vg_scrypt_blockmix" bm)
    (.block [.alu .add .rbp (.reg .r14), .alu .sub .r15 (.imm 1)])

def fillWith (bm : Prog isa) : Prog isa := .seq fillInit (.loop (fillStep bm) .ne)

def roMixDirectWith (bm : Prog isa) : Prog isa :=
  .seq (.block rmPrologue) <| .seq nLoop <| .seq (.block rmSetup) <|
  .seq (fillWith bm) <| .seq (.block rmMid) <|
  .seq (.loop (step3 bm) .ne) (.block rmEpilogue)

def roMixDirect : Prog isa := roMixDirectWith blockMixFused
end VG.Impl.Scrypt.X86_64
