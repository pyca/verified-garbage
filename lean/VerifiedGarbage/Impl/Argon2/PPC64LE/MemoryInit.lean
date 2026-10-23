module

public import VerifiedGarbage.Impl.Argon2.PPC64LE.Initial

/-!
# Argon2 on PPC64LE: memory initialization

The whole matrix is cleared, then `vg_argon2_hprime` computes the first two
blocks of every lane, B[lane][column] = H′(1024, H₀ ‖ LE32(column) ‖
LE32(lane)), from the 72 bytes at `r30 + 32`, with `scratch` as its working
space. `r28` counts the lanes and `r29` points to the block being
initialized; H′ keeps both, as it keeps `r30` and `r31`.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.Derive

open VG.PPC64LE

def hPrimeName : String := "vg_argon2_hprime"

/-- `hprime(r3, r4, r5, r6, r7)`. -/
def hPrimeCall : Prog isa := .call hPrimeName HPrime.code

/-- Zero `blocks · 128` doublewords from `memory` on. -/
def clearSetup : List Instr :=
  [lda .r5 memoryArg, lda .r6 blocksArg, .lsl .r6 .r6 7, .li .r7 0]

def clearWord : List Instr := [.store .d .r7 .r5 0, .addi .r5 .r5 8, .subi .r6 .r6 1]

def clear : Prog isa := .seq (.block clearSetup) (.loop (.block clearWord) (.nonzero .d .r6))

/-- B[r28][column], at `r29`. -/
def initBlock (column : Nat) : Prog isa :=
  .seq (.block [.li .r3 column, .store .w .r3 .r30 columnOff, .store .w .r28 .r30 laneWordOff,
      .addi .r3 .r30 h0Off, .li .r4 72, HPrime.mov .r5 .r29, .li .r6 1024, HPrime.mov .r7 .r31])
    hPrimeCall

/-- The next lane's first block, and the difference of the lane and the lane
count. -/
def nextLane : List Instr :=
  [ld .r3 strideOff, .add .r29 .r29 .r3, .subi .r29 .r29 1024, .addi .r28 .r28 1, ldw .r3 lanesArg,
    .sub .r3 .r28 .r3]

def initLane : Prog isa :=
  .seq (initBlock 0) (.seq (.block [.addi .r29 .r29 1024]) (.seq (initBlock 1) (.block nextLane)))

def memoryInit : Prog isa :=
  .seq clear (.seq (.block [lda .r29 memoryArg, .li .r28 0]) (.loop initLane (.nonzero .d .r3)))

end VG.Impl.Argon2.PPC64LE.Derive
