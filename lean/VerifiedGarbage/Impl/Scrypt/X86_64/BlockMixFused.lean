import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix

/-! Scalar BlockMix retaining its twelve register words and four scratch words
across Salsa invocations. Loop metadata lives in scratch[16, 48); scratch[48, 56)
is a temporary, and scratch[64, 112) retains the caller's saved registers. -/
namespace VG.Impl.Scrypt.X86_64
open VG.X86_64

def fusedSetup : List Instr :=
  [.store (at_ .r13 16) .rbx, .store (at_ .r13 24) .rbp,
   .store (at_ .r13 32) .r12, .store (at_ .r13 40) .r14,
   .mov .rsi (.reg .r13), .mov .rdi (.reg .r15)] ++ load

/-- XOR the retained X with the next input and save the feed-forward words. -/
def fusedXorWord (k : Nat) : List Instr :=
  if k < 12 then
    [.alu32 .xor (wreg k) (.mem (at_ .rax (4 * k))), .store32 (at_ .rdi (4 * k)) (wreg k)]
  else
    [.mov32 .rcx (.mem (at_ .rsi (slotOff k))), .alu32 .xor .rcx (.mem (at_ .rax (4 * k))),
     .store32 (at_ .rdi (4 * k)) .rcx, .store32 (at_ .rsi (slotOff k)) .rcx]

def fusedXor : List Instr :=
  (List.range 12).flatMap fusedXorWord ++ [.store (at_ .rsi 48) .rcx] ++
  (List.range 4).flatMap (fun k => fusedXorWord (12 + k)) ++ [.mov .rcx (.mem (at_ .rsi 48))]

def fusedFinishWord (k : Nat) : List Instr :=
  finishWord k ++ if k < 12 then [] else [.store32 (at_ .rsi (slotOff k)) .rax]

def fusedCore : Prog isa :=
  .seq (.block fusedXor) <| .seq (rounds 4) (.block ((List.range 16).flatMap fusedFinishWord))

def fusedHead (offset : Nat) (odd : Bool) : List Instr :=
  [.mov .rax (.mem (at_ .rsi 16)), .alu .add .rax (.imm (BitVec.ofNat 32 offset)),
    .mov .rdi (.mem (at_ .rsi (if odd then 32 else 24)))]

def fusedHalf (offset : Nat) (odd : Bool) : Prog isa :=
  .seq (.block (fusedHead offset odd)) fusedCore

def fusedAdvance (off inc : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rsi off)), .alu .add .rax (.imm (BitVec.ofNat 32 inc)),
   .store (at_ .rsi off) .rax]

def fusedTail : List Instr :=
  fusedAdvance 16 128 ++ fusedAdvance 24 64 ++ fusedAdvance 32 64 ++
    [.mov .rax (.mem (at_ .rsi 40)), .alu .sub .rax (.imm 1), .store (at_ .rsi 40) .rax]

def fusedBody : Prog isa :=
  .seq (fusedHalf 0 false) <| .seq (fusedHalf 64 true) (.block fusedTail)

def blockMixFused : Prog isa :=
  .seq (.block (bmPrologue ++ fusedSetup)) <|
  .seq (.loop fusedBody .ne) (.block (bmSaved.map fun (r, d) => .mov r (.mem (at_ .rsi d))))
end VG.Impl.Scrypt.X86_64
