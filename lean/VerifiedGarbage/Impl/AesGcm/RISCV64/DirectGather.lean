module

public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args

/-! # Bitsliced AES-GCM gather seal directly into the destination

Keep the descriptor cursor in s8 and the number of descriptors remaining at
the otherwise unused received-tag slot. The ciphertext forms one contiguous
GHASH input even when a descriptor ends in the middle of a counter block.
-/

@[expose] public section

namespace VG.Impl.AesGcm.RISCV64.DirectGather

open VG.RISCV64

def setup : List Instr :=
  [mov .s8 .a6, .store .d .a7 .s0 rO, .load .d .t0 .t1 0,
     .store .d .t0 .s0 dataO, .load .d .s11 .t1 8, .li .t0 0, .store .d .t0 .s0 dstO]

def entry : List Instr := oneEntryAt 32 16 ++ setup

/-- Set the partial keystream offset and the distance from this piece to its
output. Advance the descriptor cursor and the running byte count before CTR. -/
def pieceArgs : List Instr :=
  Impl.Words.RISCV64.loadLE64 .s4 .t3 .t4 .s8 0 ++
  Impl.Words.RISCV64.loadLE64 .s5 .t3 .t4 .s8 8 ++
  [.addi .s8 .s8 16,
   .load .d .t0 .s0 dstO, .logicImm .and .s6 .t0 15,
   .load .d .s9 .s0 dataO, .add .s9 .s9 .t0, .sub .s9 .s9 .s4,
   .add .t0 .t0 .s5, .store .d .t0 .s0 dstO]

def pieces : Prog isa :=
  .seq (.block [.load .d .t1 .s0 rO])
    (.ite (.zero .t1) (.block [])
      (.loop (.seq (.block pieceArgs) (.seq (cryptB true true)
        (.block [.load .d .t1 .s0 rO, .addi .t1 .t1 (-1), .store .d .t1 .s0 rO])))
        (.nonzero .t1)))

def body : Prog isa :=
  .seq (.block entry) (.seq oneAad (.seq (.block (bkLoad 24)) (.seq pieces
    (.seq (oneTagB true 0)
      (.block ([.addSp .t1 0, .load .d .s9 .t1 16] ++ tagOut ++ restore))))))

def sealGather : Prog isa := Impl.StackScratch.RISCV64.withStackScratchArgs 2608 4 body

end VG.Impl.AesGcm.RISCV64.DirectGather
