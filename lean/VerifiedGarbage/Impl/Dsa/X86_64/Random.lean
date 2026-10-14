module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! # Bounded DSA scalar sampling on x86-64

An internal program for callers with a stack frame. Its slots start after
five outgoing stack arguments. The caller supplies q, qLen, rand and randLen;
`used` is an offset into that tape, preserved across signing retries.
`prepare` scans the public q and clears the padded nonce. `sample` consumes
at most 128 complete draws and returns status 1 (accepted), 2 (short tape),
or 0 (draw limit). The caller must skip `sample` if `prepare` returns zero.

Only caller-saved registers are used. This module is not an emitted artifact;
registration requires correctness, memory-safety and leakage proofs.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Random
open VG VG.X86_64

def sp (offset : Nat) : MemOp := { base := .rsp, disp := offset }

def oOut : Nat := 40
def oOutLen : Nat := 48
def oUsedPtr : Nat := 56
def oKey : Nat := 64
def oKeyLen : Nat := 72
def oPLen : Nat := 80
def oQLen : Nat := 88
def oDigest : Nat := 96
def oDigestLen : Nat := 104
def oRand : Nat := 112
def oRandLen : Nat := 120
def oScratch : Nat := 128
def oScratchLen : Nat := 136
def oUsed : Nat := 144
def oAttempts : Nat := 152
def oDraws : Nat := 160
def oQ : Nat := 168
def oWidth : Nat := 176
def oMask : Nat := 184
def oStatus : Nat := 192
def oNonce : Nat := 200
def frameBytes : Nat := 248

def address (r : Reg) (offset : Nat) : List Instr :=
  [.mov r (.reg .rsp), .alu .add r (.imm (BitVec.ofNat 32 offset))]

/-- Skip public leading zeros, stopping on the first nonzero byte or width zero. -/
def significant : Prog isa :=
  .loop (.seq (.block [.movzx8 .rax { base := .r10 }, .alu .cmp .rax (.imm 0)])
    (.ite .e (.block [.alu .add .r10 (.imm 1), .alu .sub .r11 (.imm 1)])
      (.block [.alu .cmp .r11 (.reg .r11)]))) .ne

/-- Shift a public leading byte to bit seven, constructing its mask in r8. -/
def mask : Prog isa :=
  .seq (.block [.mov .r8 (.imm 255), .alu .cmp .rax (.imm 128)])
    (.ite .b (.loop (.block [.shift .shl .rax 1, .shift .shr .r8 1,
      .alu .cmp .rax (.imm 128)]) .b) (.block []))

/-- Clear all 32 bytes, including padding outside the significant scalar. -/
def clearNonce : List Instr :=
  [.mov .rax (.imm 0), .store (sp oNonce) .rax, .store (sp (oNonce + 8)) .rax,
    .store (sp (oNonce + 16)) .rax, .store (sp (oNonce + 24)) .rax]

/-- qLen must be nonzero and at most 32. Returns rax=1 exactly when q>1. -/
def prepare : Prog isa :=
  .seq (.block (clearNonce ++ [.mov .r10 (.mem (sp oQ)), .mov .r11 (.mem (sp oQLen))]))
    (.seq significant
      (.seq (.block [.store (sp oQ) .r10, .store (sp oWidth) .r11,
          .alu .cmp .r11 (.imm 0)])
        (.ite .e (.block [.mov .rax (.imm 0)])
          (.seq (.block [.alu .cmp .r11 (.imm 1)])
            (.ite .e
              (.seq (.block [.alu .cmp .rax (.imm 1)])
                (.ite .e (.block [.mov .rax (.imm 0)])
                  (.seq mask (.block [.store (sp oMask) .r8, .mov .rax (.imm 1)]))))
              (.seq mask (.block [.store (sp oMask) .r8, .mov .rax (.imm 1)])))))))

/-- Copy one masked draw into the right-aligned nonce buffer. -/
def copy : Prog isa :=
  .seq (.block ([.mov .r10 (.mem (sp oRand)), .alu .add .r10 (.mem (sp oUsed)),
      .mov .r11 (.mem (sp oWidth))] ++ address .rdx oNonce ++
      [.alu .add .rdx (.mem (sp oQLen)), .alu .sub .rdx (.reg .r11),
       .movzx8 .rax { base := .r10 }, .alu .and .rax (.mem (sp oMask)),
       .store8 { base := .rdx } .rax,
       .alu .add .r10 (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .r11 (.imm 1)]))
    (.ite .ne (.loop (.block [.movzx8 .rax { base := .r10 }, .store8 { base := .rdx } .rax,
      .alu .add .r10 (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .r11 (.imm 1)]) .ne)
      (.block []))

/-- Subtract the public-modulus byte and incoming borrow from the nonce byte. -/
def borrow : List Instr :=
  [.alu .add .rcx (.reg .r8), .alu .sub .rax (.reg .rcx),
   .shift .shr .rax 63, .mov .r8 (.reg .rax)]

/-- Constant-time byte subtraction and nonzero check. r8 is the final borrow,
r9 the OR of all bytes. Only their conjunction reaches a branch. -/
def inRange : Prog isa :=
  .seq (.block (address .rdx oNonce ++
      [.alu .add .rdx (.mem (sp oQLen)), .mov .r10 (.mem (sp oQ)),
       .mov .r11 (.mem (sp oWidth)), .alu .add .r10 (.reg .r11),
       .mov .r8 (.imm 0), .mov .r9 (.imm 0)]))
    (.seq (.loop (.block ([.alu .sub .rdx (.imm 1), .alu .sub .r10 (.imm 1),
        .movzx8 .rax { base := .rdx }, .alu .or .r9 (.reg .rax),
        .movzx8 .rcx { base := .r10 }] ++ borrow ++
        [.alu .sub .r11 (.imm 1)])) .ne)
      (.block [.mov .rax (.imm 0), .alu .cmp .r9 (.imm 0), .cmov .e .r8 (.reg .rax),
        .alu .cmp .r8 (.imm 0)]))

/-- One complete draw, or short-tape failure. Status 4 means keep sampling. -/
def draw : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp oRandLen)), .alu .sub .rax (.mem (sp oUsed)),
      .alu .cmp .rax (.mem (sp oWidth))])
    (.ite .b (.block [.mov .rax (.imm 2), .store (sp oStatus) .rax])
      (.seq copy
        (.seq (.block [.mov .rax (.mem (sp oUsed)), .alu .add .rax (.mem (sp oWidth)),
            .store (sp oUsed) .rax])
          (.seq inRange
            (.ite .ne (.block [.mov .rax (.imm 1), .store (sp oStatus) .rax])
              (.seq (.block [.mov .rax (.mem (sp oDraws)), .alu .sub .rax (.imm 1),
                  .store (sp oDraws) .rax])
                (.ite .e (.block [.store (sp oStatus) .rax]) (.block []))))))))

/-- One 128-draw sampling budget; accumulated consumption is never reset. -/
def sample : Prog isa :=
  .seq (.block [.mov .rax (.imm 128), .store (sp oDraws) .rax,
      .mov .rax (.imm 4), .store (sp oStatus) .rax])
    (.seq (.loop (.seq draw (.block [.mov .rax (.mem (sp oStatus)),
        .alu .cmp .rax (.imm 4)])) .e)
      (.block [.mov .rax (.mem (sp oStatus))]))

end VG.Impl.Dsa.X86_64.Random
