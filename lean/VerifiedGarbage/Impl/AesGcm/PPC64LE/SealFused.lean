module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks

/-! # One-pass POWER8 AES-GCM seal

The whole-block helper shares the existing 2560-byte workspace: its 64-byte
header starts at W+448 and its 2048-byte kernel area at W+512. The final
partial block and tag reuse the existing code. The entry and return are
shared with the original one-shot implementation.
-/

@[expose] public section
namespace VG.Impl.AesGcm.PPC64LE.SealFused
open VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (mov)

def blockArgs : List Instr :=
  [mov .r3 .r29,mov .r4 .r28,.addi .r5 .r30 48,.addi .r6 .r30 16,
   mov .r7 .r27,.lsr .d .r8 .r23 4,.addi .r9 .r31 448]

def tailSetup : List Instr :=
  [.li .r0 15,.logic .and .r25 .r23 .r0,.sub .r12 .r23 .r25,.add .r24 .r27 .r12,.li .r26 0]

def fastBody : Prog isa :=
  .seq (.seq (.block blockArgs) (.call "vg_aes_gcm_encrypt_blocks" Blocks.encrypt))
    (.seq (.seq (.block tailSetup) cryptTail) (.seq (absorb 16) (finTag 0)))

def body : Prog isa :=
  .seq (.block [.lsr .d .r12 .r23 9])
    (.ite (.zero .d .r12) (.seq oneCrypt (oneTag 0)) fastBody)

def withBody (sealBody : Prog isa) : Prog isa :=
  sealWith sealBody

def «seal» : Prog isa := withBody body

end VG.Impl.AesGcm.PPC64LE.SealFused
