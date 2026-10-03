import VerifiedGarbage.Impl.Argon2.Arm.Fill

/-!
# Argon2 on ARMv7: the derivation

`vg_argon2(kind = r0, password = r1, password_len = r2, salt = r3, salt_len,
iterations, memory_cost, lanes, threads, secret, secret_len, associated_data,
ad_len, memory, blocks, scratch, out, out_len)`, the last fourteen on the
stack.

The register arguments are pushed below the stack arguments, then the
caller's `r4`–`r11` and our return address (in a frame with `r3`, so that the
stack pointer stays 8-byte aligned), then the locals
(`Impl/Argon2/Arm/Layout.lean`), at which `r11` points throughout. The
derivation computes the parameters and H₀, initializes the memory, fills it,
XORs the last block of every lane into the first block of the memory, and
writes H′ of it to `out`. The lanes are evaluated serially, which every
positive `threads` permits.
-/

namespace VG.Impl.Argon2.Arm.Derive

open VG.Arm

/-! ## The final block and the tag -/

/-- Zero the memory's first block. -/
def reduceClear : List Instr :=
  [ld .r3 (argOff memoryArg), .mov .r0 (.imm 0)] ++ (List.range 256).map fun k => .str .r0 .r3 (4 * k)

/-- XOR the last block of lane `[r11, #laneOff]` into the first block. -/
def reduceLane : List Instr :=
  [ld .r0 laneOff, ld .r1 laneLenOff, .dp .sub .r1 .r1 (.imm 1)] ++ blockAddr ++
    [.mov .r1 (.reg .r0), ld .r3 (argOff memoryArg)] ++ writeBlock true

def reduce : Prog isa :=
  .seq (.block (reduceClear ++ setLocal laneOff 0))
    (.loop (.block (reduceLane ++ advance laneOff (argOff lanesArg))) .ne)

/-- `hprime(memory, 1024, out, out_len, scratch)`. -/
def finalOutput : Prog isa :=
  .seq (.block [ld .r0 (argOff memoryArg), .mov .r1 (.imm 1024), ld .r2 (argOff outArg),
      ld .r3 (argOff outLenArg), ld .r12 (argOff scratchArg)])
    hPrimeCall

/-! ## The whole function -/

def body : Prog isa :=
  .seq (.block (.addSp .r11 0 :: parameters))
  (.seq code
  (.seq memoryInit
  (.seq passesLoop
  (.seq reduce finalOutput))))

/-- The caller's registers, in the frame that saves them (at `[sp, #4]` …). -/
def savedSlots : List (Reg × Nat) :=
  [(.r4, 4), (.r5, 8), (.r6, 12), (.r7, 16), (.r8, 20), (.r9, 24), (.r10, 28), (.r11, 32), (.lr, 36)]

/-- Restore them, before the frame's pop. -/
def restoreRegs : List Instr := savedSlots.map fun p => .ldrSp p.1 p.2

def derive : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3])
    (.frame (.push [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr])
      (.seq (.frame (.alloc locals) body (.free locals)) (.block restoreRegs))
      (.pop .r3 40))
    (.pop .r0 16)

end VG.Impl.Argon2.Arm.Derive
