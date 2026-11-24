module

public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args

/-! # One-shot AES-GCM from a contiguous source to an identical or disjoint destination -/

@[expose] public section
namespace VG.Impl.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64
open VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- With a 12-byte nonce, the initial payload counter ends in big-endian 2. -/
def initState12 : List Instr :=
  [.load .d .t0 .s1 0, .store .d .t0 .s1 48, .load .w .t0 .s1 8, .store .w .t0 .s1 56,
   .li .t0 2, .shift .sll .d .t0 .t0 24, .store .w .t0 .s1 60,
   .li .t0 0, .store .d .t0 .s1 16, .store .d .t0 .s1 24]
def nonceC : Prog isa := .seq (.block [.addi .a2 .s5 (-12)])
  (.ite (.zero .a2) (.block (j012 ++ initState12)) (.seq j0hash (.block initState)))
/-- Pad a short AAD directly in the GHASH input block. -/
def aadSmall : Prog isa := .ite (.zero .s10) (.block [])
  (.seq (.block [.li .t0 0, .store .d .t0 .s0 tO, .store .d .t0 .s0 (tO+8),
     .load .d .a0 .s0 aadO, .addi .a1 .s0 tO, mov .a2 .s10]) (.seq copyLoop (ghash1 16 .s0 tO)))
def aadLong : Prog isa :=
  .seq (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0])
    (.seq (absorb 16) (.seq (.block [.logicImm .and .s6 .s10 15]) (flush 16)))
def aadC : Prog isa := .seq (.block [.li .t0 16]) (.ite (.ltu .s10 .t0) aadSmall aadLong)
/-- The stack supplies the shared length, tag, bitsliced round keys and scratch. -/
def entry : List Instr := oneEntryAt 24 8 ++ [mov .s8 .a7, .load .d .s11 .t1 0]

/-- Keep the source in s4, compute the destination distance in s9, and save the
ciphertext base for the tag pass. -/
def payloadArgs : List Instr :=
  bkLoad 16 ++ dataArgs ++ [.sub .s9 .s8 .s4, .store .d .s8 .s0 dataO]

/-- Reload the tag after the crypt pass releases s9, then restore the callee-saved registers. -/
def exitHead : List Instr := [.addSp .t1 0, .load .d .s9 .t1 8]

def exitCode : List Instr := exitHead ++ tagOut ++ restore

def body : Prog isa :=
  .seq (.block entry)
    (.seq nonceC (.seq aadC (.seq (.block payloadArgs)
      (.seq (cryptWholeB true true) (.seq (cryptTailB true true) (.seq (oneTagB true 0)
        (.block exitCode)))))))
def code : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (144, [(0, 18)])]
    (withStackScratchArgs 2592 3 body)

end VG.Impl.AesGcm.RISCV64.Contiguous
