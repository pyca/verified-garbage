module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks

/-! # Encrypting POWER8 gather fragments directly to their destination -/

@[expose] public section
namespace VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.PPC64LE

/-- While processing pieces, r21 is the next output byte, r27 the output base,
r19 the descriptor cursor, and r18 the number of descriptors left. -/
def next : List Instr :=
  [.load .d .r24 .r19 0, .load .d .r25 .r19 8, .addi .r19 .r19 16, .subi .r18 .r18 1]

def head : Prog isa :=
  .seq minLen
    (.seq (.block [.addi .r3 .r30 64, .add .r3 .r3 .r26, mov .r4 .r24, mov .r7 .r21,
      .add .r21 .r21 .r5, .add .r24 .r24 .r5, .sub .r25 .r25 .r5]) (xorLoopWith true))

/-- r26 is the (possibly wrapping) difference between the destination and
source pointers. The AES batches read each block at r6 and store at r6+r26. -/
def whole : Prog isa :=
  .seq (.block [.lsr .d .r7 .r25 4])
    (.ite (.zero .d .r7) (.block [])
      (.seq (.block ([mov .r6 .r24, .sub .r26 .r21 .r24, .lsl .r11 .r7 4, .add .r21 .r21 .r11,
        .add .r24 .r24 .r11, .sub .r25 .r25 .r11] ++ ctrArgs 48))
        (Impl.Aes.PPC64LE.Crypto.ctrData .r26)))

def piece : Prog isa :=
  .ite (.zero .d .r25) (.block [])
    (.seq (.block [.sub .r26 .r21 .r27, .li .r0 15, .logic .and .r26 .r26 .r0])
    (.seq (.ite (.zero .d .r26) (.block []) head)
    (.seq whole
    (.seq (.block [mov .r26 .r21, .add .r21 .r21 .r25]) (cryptTailWith true)))))

/-- Round the first descriptor down to a multiple of eight blocks, and
advance its cursors past the bytes going to the fused helper. -/
def takeBulk : List Instr :=
  [.lsr .d .r8 .r25 7, .lsl .r11 .r8 7, .lsl .r8 .r8 3, mov .r10 .r8,
   mov .r7 .r24, mov .r9 .r21, .add .r24 .r24 .r11, .add .r21 .r21 .r11, .sub .r25 .r25 .r11]

def bulkRegs : List Instr :=
  [mov .r3 .r29, mov .r4 .r28, .addi .r5 .r30 48, .addi .r6 .r30 16, .addi .r0 .r31 448, .addSp .r12 0]

def bulkPrepare : Prog isa :=
  .seq (.block takeBulk)
    (.seq (.block [.store .d .r11 .r31 112])
    (.seq (.block bulkRegs) (.block [.store .d .r0 .r12 96])))

def bulkRun : Prog isa := .seq bulkPrepare (.call "vg_aes_gcm_encrypt_blocks_split" SplitBlocks.encrypt)

/-- Only a complete number of fused eight-block batches enters the bulk call.
Its short copy fallback consequently receives zero source blocks. W+112
records the number of ciphertext bytes already authenticated. -/
def bulk : Prog isa :=
  .seq (.block [.lsr .d .r12 .r25 9]) (.ite (.zero .d .r12) (.block []) bulkRun)

def pieces : Prog isa :=
  .ite (.zero .d .r18) (.block [])
    (.loop (.seq (.block (next ++ [.sub .r11 .r21 .r27]))
      (.seq (.ite (.zero .d .r11) bulk (.block [])) piece)) (.nonzero .d .r18))

def finish : Prog isa :=
  .seq (.block [.load .d .r11 .r31 112, .add .r24 .r27 .r11, .sub .r25 .r23 .r11, .li .r26 0])
    (.seq (absorb 16)
    (.seq (.block [.li .r0 15, .logic .and .r26 .r23 .r0])
    (.seq (flush 16)
    (.seq (.block [mov .r24 .r22, mov .r26 .r23]) (tag 0)))))

def body : Prog isa :=
  .seq (.block (oneEntry 120))
    (.seq oneAad
    (.seq (.block [mov .r19 .r27, mov .r18 .r23, .addSp .r12 0, .load .d .r27 .r12 96,
      .load .d .r23 .r12 104, .load .d .r20 .r12 112, mov .r21 .r27, .li .r0 0, .store .d .r0 .r31 112])
    (.seq pieces (.seq finish (.seq (.block tagOut) (.block restore))))))

def code : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchArgs 1280 3 body

end VG.Impl.AesGcm.PPC64LE.DirectGather
