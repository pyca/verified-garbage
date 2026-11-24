module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.DirectGather
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args

/-! # Contiguous POWER AES-GCM seal for identical or disjoint buffers -/

@[expose] public section
namespace VG.Impl.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.Scrub.PPC64LE VG.Impl.StackScratch.PPC64LE

/-- The two pointers arrive in r9 and r10, the common length and tag on stack. -/
def entry : List Instr :=
  [.addSp .r12 0, .load .d .r12 .r12 112] ++ save .r12 ++
    [mov .r29 .r3, mov .r28 .r4, .addi .r30 .r31 16, mov .r24 .r5, mov .r25 .r6,
     mov .r18 .r6, mov .r21 .r7, mov .r22 .r8, mov .r19 .r9, mov .r27 .r10,
     .addSp .r12 0, .load .d .r23 .r12 96, .load .d .r20 .r12 104]
def fusedArgs : List Instr :=
  [mov .r3 .r29, mov .r4 .r28, .addi .r5 .r30 48, .addi .r6 .r30 16,
     mov .r7 .r19, .lsr .d .r8 .r23 7, .lsl .r8 .r8 3, mov .r9 .r27, .addi .r10 .r31 448]

def fused : Prog isa := .seq (.block fusedArgs)
    (.call "vg_aes_gcm_encrypt_blocks_buffers" SplitBlocks.encryptBuffers)
def afterBulk : List Instr :=
  [.li .r0 127, .logic .and .r25 .r23 .r0, .sub .r11 .r23 .r25,
    .add .r24 .r19 .r11, .add .r18 .r27 .r11]
/-- Encrypt the complete 16-byte blocks followed by a possible partial block.
The contiguous caller has no subsequent descriptor to advance to. -/
def cryptRest : Prog isa := .seq DirectGather.whole
  (.seq (.block [mov .r26 .r21]) (cryptTailWith true))

def remaining : Prog isa :=
  .seq (.block [mov .r21 .r18, mov .r19 .r25])
    (.seq cryptRest (.seq (.block [mov .r24 .r18, mov .r25 .r19, .li .r26 0])
      (.seq (absorb 16) (.seq (.block [.li .r0 15, .logic .and .r26 .r19 .r0]) (flush 16)))))
def payload : Prog isa :=
  .seq (.block [.lsr .d .r12 .r23 9])
    (.seq (.ite (.zero .d .r12) (.block [mov .r24 .r19, mov .r18 .r27, mov .r25 .r23])
      (.seq fused (.block afterBulk)))
      (.seq (.ite (.zero .d .r25) (.block []) remaining)
        (.seq (.block [mov .r24 .r22, mov .r26 .r23]) (tag 0))))
/-- The nonce words loaded by `j012` are still live in r3 through r5. -/
def initState12 : List Instr :=
  [.store .w .r3 .r30 48, .store .w .r4 .r30 52, .store .w .r5 .r30 56,
   .lis .r6 0x0200, .store .w .r6 .r30 60, .li .r8 0, .store .d .r8 .r30 16, .store .d .r8 .r30 24]

def nonceC : Prog isa :=
  .seq (.block [.subi .r6 .r25 12])
    (.ite (.zero .d .r6) (.block (j012 ++ initState12)) (.seq j0hash (.block initState)))
def takeWord (size : VG.PPC64LE.Size) (shift : Nat) : Prog isa :=
  .seq (.block [.lsr .d .r11 .r5 shift]) (.ite (.zero .d .r11) (.block [])
    (.block [.load size .r7 .r3 0,.store size .r7 .r4 0,.addi .r3 .r3 size.bytes,
        .addi .r4 .r4 size.bytes,.subi .r5 .r5 size.bytes]))
def aadCopy : Prog isa := .seq (takeWord .d 3) (.seq (takeWord .w 2)
  (.ite (.zero .d .r5) (.block []) copyLoop))
def aadCopyArgs : List Instr := [mov .r3 .r21, .addi .r4 .r31 tO, mov .r5 .r22]
def aadSmall : Prog isa := .ite (.zero .d .r22) (.block [])
  (.seq (.block ([.li .r0 0, .store .d .r0 .r31 tO, .store .d .r0 .r31 (tO+8)] ++ aadCopyArgs))
    (.seq aadCopy (ghash1 16 .r31 tO)))
def aadLong : Prog isa :=
  .seq (.block [mov .r24 .r21, mov .r25 .r22, .li .r26 0])
    (.seq (absorb 16) (.seq (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) (flush 16)))
def aadC : Prog isa := .seq (.block [.lsr .d .r11 .r22 4]) (.ite (.zero .d .r11) aadSmall aadLong)
def body : Prog isa := .seq (.block entry)
  (.seq nonceC (.seq aadC (.seq payload (.seq (.block tagOut) (.block restore)))))
def code : Prog isa :=
  scrubAll 0 1280 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (.frame (.alloc 1280) (.seq (.block (setArgsAt 1280 2 128)) body) (.free 1280))

end VG.Impl.AesGcm.PPC64LE.Contiguous
