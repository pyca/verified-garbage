module

public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args

/-! # One-shot AES-GCM from a contiguous source to an identical or disjoint destination -/

@[expose] public section
namespace VG.Impl.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64
open VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- The stack supplies the shared length, tag, bitsliced round keys and scratch. -/
def entry : List Instr := oneEntryAt 24 8 ++ [mov .s8 .a7, .load .d .s11 .t1 0]

/-- Keep the source in s4, compute the destination distance in s9, and save the
ciphertext base for the tag pass. -/
def payloadArgs : List Instr :=
  bkLoad 16 ++ dataArgs ++ [.sub .s9 .s8 .s4, .store .d .s8 .s0 dataO]

/-- Reload the tag after the crypt pass releases s9, then restore the callee-saved registers. -/
def exitHead : List Instr := [.addSp .t1 0, .load .d .s9 .t1 8]

def exitCode : List Instr := exitHead ++ tagOut ++ restore

def longPayload : Prog isa :=
  .seq (cryptWholeB true true) (.seq (cryptTailB true true) (oneTagB true 0))
/-- Generate the tag mask first and the payload keystream directly after it.
The 256-byte workspace covers up to 240 bytes of payload. -/
def maskZero (n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.store .d .t0 .s0 (256+16*i), .store .d .t0 .s0 (264+16*i)]
def maskArgs : List Instr :=
  [mov .a0 .s7,mov .a1 .s3,mov .a2 .s1,.addi .a3 .s0 256,
   .addi .a4 .s5 15,.shift .srl .d .a4 .a4 4,.addi .a4 .a4 1,.addi .a5 .s0 scrO]
def masks : Prog isa :=
  .seq (.block ([.li .t0 0] ++ maskZero 16 ++ maskArgs)) (ctrCallB true)
def maskTag : Prog isa :=
  .seq (.block [mov .s4 .s10, mov .s6 .s11]) (.seq (lens 16)
    (.block [.load .d .t0 .s1 16, .load .d .t1 .s0 256, .logic .xor .t0 .t0 .t1, .store .d .t0 .s0 0,
       .load .d .t0 .s1 24, .load .d .t1 .s0 264, .logic .xor .t0 .t0 .t1, .store .d .t0 .s0 8]))
def xorRemainder : Prog isa := .ite (.zero .a2) (.block []) (xorLoopWith true)
def xorQwords : Prog isa :=
  .seq (.block [.shift .srl .d .a5 .a2 3,.logicImm .and .a2 .a2 7])
    (.seq (.ite (.zero .a5) (.block []) (.loop (.block
      [.load .d .t0 .a1 0, .load .d .a3 .a0 0, .logic .xor .t0 .t0 .a3,
       .store .d .t0 .a4 0, .addi .a0 .a0 8, .addi .a1 .a1 8, .addi .a4 .a4 8,
       .addi .a5 .a5 (-1)]) (.nonzero .a5))) xorRemainder)
def xorText : Prog isa := .seq (.block [.logic .or .t0 .a1 .a4,.logicImm .and .t0 .t0 7])
  (.ite (.zero .t0) xorQwords (xorLoopWith true))
def shortPayload : Prog isa :=
  .seq masks (.seq (.ite (.zero .s5) (.block []) (.seq (.block
      [.addi .a0 .s0 272, mov .a1 .s4, mov .a4 .s8, mov .a2 .s5]) xorText))
    (.seq (.block dataArgs) (.seq (absorb 16) (.seq (.block [.logicImm .and .s6 .s11 15]) (.seq (flush 16) maskTag)))))
def body : Prog isa :=
  .seq (.block entry) (.seq oneAad (.seq (.block (payloadArgs ++ [.li .t0 241]))
    (.seq (.ite (.ltu .s5 .t0) shortPayload longPayload) (.block exitCode))))

def code : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (160, [(0, 20)])]
    (.frame (.alloc 2608) (.seq (.block (setArgsAt 2608 3 40)) body) (.free 2608))

end VG.Impl.AesGcm.RISCV64.Contiguous
