module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks

/-! # POWER8 one-shot seal with a source prefix

The source pointer and byte length survive nonce/AAD processing in the unused
slots at W+112 and W+120. Copy only their final partial block; the whole-block
helper reads the complete source blocks directly. The existing nonce, AAD,
partial-text, tag, and return code is shared with in-place seal.
-/

@[expose] public section
namespace VG.Impl.AesGcm.PPC64LE.SealSplit
open VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (mov)

-- Convert the twelve-argument scratch signature to the shared seal entry.
-- A 112-byte frame provides the outgoing tag and scratch argument slots.
def loadWork : List Instr := [.addSp .r12 0,.load .d .r11 .r12 232]

def sourceSaved : List (Reg × Nat) := [(.r9,112),(.r10,120)]

def config : List Instr :=
 [.load .d .r9 .r12 208,.load .d .r10 .r12 216,
  .load .d .r0 .r12 224,.store .d .r0 .r12 96,.store .d .r11 .r12 104]

def prelude : List Instr := loadWork ++
 sourceSaved.map (fun (r,o) => .store .d r .r11 o) ++ config

def sourceArgs : List Instr := [.load .d .r7 .r31 112,.load .d .r8 .r31 120]

def partialArgs : List Instr :=
 [.li .r0 15,.logic .and .r5 .r8 .r0,.sub .r11 .r8 .r5,
  .add .r3 .r7 .r11,.add .r4 .r27 .r11]

def partialCopy : Prog isa := .seq (.block partialArgs)
 (.ite (.zero .d .r5) (.block []) copyLoop)

def blockArgs : List Instr :=
 [mov .r3 .r29,mov .r4 .r28,.addi .r5 .r30 48,.addi .r6 .r30 16,
  .lsr .d .r8 .r8 4,mov .r9 .r27,.lsr .d .r10 .r23 4,
  .addi .r0 .r31 448,.addSp .r12 0,.store .d .r0 .r12 96]

def whole : Prog isa := .seq (.block blockArgs)
 (.call "vg_aes_gcm_encrypt_blocks_split" SplitBlocks.encrypt)

def nonempty : Prog isa := .seq (.block sourceArgs) (.seq partialCopy
 (.seq whole (.seq (.block SealFused.tailSetup)
 (.seq cryptTail (.seq (absorb 16) (finTag 0))))))

def body : Prog isa := .ite (.zero .d .r23) (.seq oneCrypt (oneTag 0)) nonempty

def «seal» : Prog isa :=
 .frame (.alloc 112) (.seq (.block prelude) (sealWith body)) (.free 112)

end VG.Impl.AesGcm.PPC64LE.SealSplit
