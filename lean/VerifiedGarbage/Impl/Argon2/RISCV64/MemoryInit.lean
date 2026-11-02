module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Initial

/-!
# Argon2 on RISC-V: memory initialization

The whole matrix is cleared, then `vg_argon2_hprime` computes the first two
blocks of every lane, B[lane][column] = H′(1024, H₀ ‖ LE32(column) ‖
LE32(lane)), from the 72 bytes at `s3`, with `scratch` as its working
space. `s1` counts the lanes and `s2` points to the block being
initialized; H′ keeps both, as it keeps `s3` and `s4`.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.Derive

open VG.RISCV64

def hPrimeName : String := "vg_argon2_hprime"

/-- `hprime(a0, a1, a2, a3, a4)`. -/
def hPrimeCall : Prog isa := .call hPrimeName HPrime.code

/-- Zero `blocks · 128` doublewords from `memory` on. -/
def clearSetup : List Instr :=
  [lda .a2 memoryArg, lda .a3 blocksArg, .shift .sll .d .a3 .a3 7, .li .a4 0]

def clearWord : List Instr := [.store .d .a4 .a2 0, .addi .a2 .a2 8, .addi .a3 .a3 (-1)]

def clear : Prog isa := .seq (.block clearSetup) (.loop (.block clearWord) (.nonzero .a3))

/-- B[s1][column], at `s2`. -/
def initBlock (column : Nat) : Prog isa :=
  .seq (.block [.li .a0 column, .store .w .a0 .s3 columnOff, .store .w .s1 .s3 laneWordOff,
      .addi .a0 .s3 h0Off, .li .a1 72, HPrime.mov .a2 .s2, .li .a3 1024, HPrime.mov .a4 .s4])
    hPrimeCall

/-- The next lane's first block, and the difference of the lane and the lane
count. -/
def nextLane : List Instr :=
  [ld .a0 strideOff, .add .s2 .s2 .a0, .addi .s2 .s2 (-1024), .addi .s1 .s1 1, ldw .a0 lanesArg,
    .sub .a0 .s1 .a0]

def initLane : Prog isa :=
  .seq (initBlock 0) (.seq (.block [.addi .s2 .s2 1024]) (.seq (initBlock 1) (.block nextLane)))

def memoryInit : Prog isa :=
  .seq clear (.seq (.block [lda .s2 memoryArg, .li .s1 0]) (.loop initLane (.nonzero .a0)))

end VG.Impl.Argon2.RISCV64.Derive
