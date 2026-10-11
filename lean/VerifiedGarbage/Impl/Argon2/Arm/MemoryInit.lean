module

public import VerifiedGarbage.Impl.Argon2.Arm.Initial

/-!
# Argon2 on ARMv7: memory initialization

The whole matrix is cleared, then `vg_argon2_hprime` computes the first two
blocks of every lane, B[lane][column] = H′(1024, H₀ ‖ LE32(column) ‖
LE32(lane)), from the 72 bytes at the start of the locals (`r11`), with
`scratch` as its working space. `r5` counts the lanes and `r6` points to
the block being initialized; both are kept across the calls, as `r11` is.
-/

@[expose] public section

namespace VG.Impl.Argon2.Arm.Derive

open VG.Arm

def hPrimeName : String := "vg_argon2_hprime"

/-- `hprime(r0, r1, r2, r3, r12)`: `scratch`, the fifth argument, is pushed
(with `lr`, keeping the stack pointer 8-byte aligned). -/
def hPrimeCall : Prog isa :=
  .frame (.push [.r12, .lr]) (.call hPrimeName HPrime.code) (.pop .r12 8)

/-- Zero `blocks · 256` words from `memory` on. -/
def clearSetup : List Instr :=
  [ld .r5 (argOff memoryArg), ld .r6 (argOff blocksArg), .mov .r6 (.shifted .r6 .lsl 8), .mov .r7 (.imm 0)]

def clearWord : List Instr := [.str .r7 .r5 0, .dp .add .r5 .r5 (.imm 4), .subs .r6 .r6 (.imm 1)]

def clear : Prog isa := .seq (.block clearSetup) (.loop (.block clearWord) .ne)

/-- B[r5][column], at `r6`. -/
def initBlock (column : Nat) : Prog isa :=
  .seq (.block [.mov .r0 (.imm (BitVec.ofNat 32 column)), st columnOff .r0, st laneWordOff .r5,
      .mov .r0 (.reg .r11), .mov .r1 (.imm 72), .mov .r2 (.reg .r6), .mov .r3 (.imm 1024),
      ld .r12 (argOff scratchArg)])
    hPrimeCall

/-- The next lane's first block, and the comparison of the lane with the
lane count. -/
def nextLane : List Instr :=
  [ld .r0 strideOff, .dp .add .r6 .r6 (.reg .r0), .dp .sub .r6 .r6 (.imm 1024),
    .dp .add .r5 .r5 (.imm 1), ld .r0 (argOff lanesArg), .cmp .r5 (.reg .r0)]

def initLane : Prog isa :=
  .seq (initBlock 0) (.seq (.block [.dp .add .r6 .r6 (.imm 1024)]) (.seq (initBlock 1) (.block nextLane)))

def memoryInit : Prog isa :=
  .seq clear (.seq (.block [ld .r6 (argOff memoryArg), .mov .r5 (.imm 0)])
    (.loop initLane .ne))

end VG.Impl.Argon2.Arm.Derive
