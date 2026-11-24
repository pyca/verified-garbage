module

public import VerifiedGarbage.Impl.AesGcm.Arm.FrameArgs
public import VerifiedGarbage.Impl.StackScratch.Arm

/-! # Direct gather seal for A32 and Thumb-2

Keep one GCM counter stream across the descriptors. A piece can start in
the unused bytes of the preceding keystream block. Whole blocks use the
out-of-place CTR entry, and GHASH reads the resulting contiguous ciphertext.
-/

@[expose] public section

namespace VG.Impl.AesGcm.Arm.DirectGather

open VG.Arm

/-- The private frame takes the one-shot layout for AAD, output and tag,
followed by the two descriptor arguments. Copy each stack word once. -/
def frameArgs : List Instr :=
  orderedFrameArgs 2608 7 fun slot => ([0, 1, 4, 5, 6, 2, 3] : List Nat)[slot]!

def setup : List Instr :=
  [.ldrSp .r7 20, .ldrSp .r0 24, .str .r0 .r11 rO,
   .mov .r0 (imm 0), .str .r0 .r11 (rO + 4)]

def pieceArgs : List Instr :=
  [.ldr .r4 .r7 0, .ldr .r5 .r7 4, addI .r7 .r7 8,
   .ldr .r0 .r11 (rO + 4), .ldrSp .r2 8, .dp .add .r2 .r2 (.reg .r0),
   .dp .and .r6 .r0 (imm 15),
   .dp .add .r0 .r0 (.reg .r5), .str .r0 .r11 (rO + 4),
   .cmp .r5 (imm 0)]

/-- Consume an existing keystream suffix, advancing both plaintext and
ciphertext pointers. An empty piece must skip the do-while byte loop. -/
def partialHead : Prog isa :=
  .seq minLen (.seq (.block [.cmp .r3 (imm 0)]) (.ite .eq (.block [])
    (.seq (.block [addI .r1 .r10 64, .dp .add .r1 .r1 (.reg .r6),
        .dp .sub .r5 .r5 (.reg .r3)])
      (xorLoopG true))))

def head : Prog isa :=
  .seq (.ite .eq (.block []) partialHead) (.block [.mov .r6 (.reg .r2)])

def piece : Prog isa := .seq head cryptTo

/-- Empty descriptors may carry arbitrary source addresses and the destination
cursor may wrap after the final byte. They perform no memory access. -/
def nonempty : Prog isa :=
  .ite .eq (.block []) (.seq (.block [.cmp .r6 (imm 0)]) piece)

def advance : List Instr :=
  [.ldr .r0 .r11 rO, .subs .r0 .r0 (imm 1), .str .r0 .r11 rO]

def pieces : Prog isa :=
  .seq (.block [.ldr .r0 .r11 rO, .cmp .r0 (imm 0)]) (.ite .eq (.block [])
    (.loop (.seq (.block pieceArgs) (.seq nonempty (.block advance))) .ne))

def body : Prog isa :=
  .seq (.block (oneEntry 28)) (.seq oneAad (.seq (.block setup)
    (.seq pieces (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))))

def sealGather : Prog isa := .frame (.alloc 2608) (.seq (.block frameArgs) body) (.free 2608)

end VG.Impl.AesGcm.Arm.DirectGather
