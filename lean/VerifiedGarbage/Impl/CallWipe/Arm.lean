module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# A call that wipes part of a buffer afterwards (ARMv7)

`callWipe r n name body zname zcode` calls the function `name`, whose code is
`body`, with the arguments its caller was given, all in registers, then zeroes
the first `n` bytes of the buffer whose address was passed in `r` by calling
the zeroize function `zname`, whose code is `zcode`, and returns what `name`
returned, in `r0` and `r1`.

Its frame, `push {r4, r5, r6, lr}`, saves the callee-saved registers it uses
and the return address, which the calls change: `r4` keeps the buffer's
address across the first call, and `r5` and `r6` keep `name`'s result across
the second. Every instruction is the same in A32 and Thumb.
-/

@[expose] public section

namespace VG.Impl.CallWipe.Arm

open VG.Arm

/-- `mov d, m`. -/
def mov (d m : Reg) : Instr := .mov d (.reg m)

/-- `mov r4, r`: keep the buffer's address. -/
def saveArg (r : Reg) : List Instr := [mov .r4 r]

/-- `mov r5, r0; mov r6, r1; mov r0, r4; movw r1, #lo16(n); movt r1, #hi16(n)`:
keep the result in `r5` and `r6`, and pass the buffer's address and `n` to
the zeroize function. -/
def zeroArgs (n : Nat) : List Instr :=
  [mov .r5 .r0, mov .r6 .r1, mov .r0 .r4, .movw .r1 (BitVec.ofNat 16 n),
    .movt .r1 (BitVec.ofNat 16 (n / 2 ^ 16))]

/-- `mov r0, r5; mov r1, r6; ldr r5, [sp, #4]; ldr r6, [sp, #8]; ldr lr, [sp, #12]`:
restore the result, then `r5`, `r6` and the return address (the frame's pop
restores `r4`). -/
def restoreRet : List Instr :=
  [mov .r0 .r5, mov .r1 .r6, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .lr 12]

/-- A call of `name`, whose code is `body`, then of the zeroize function
`zname`, whose code is `zcode`, on the first `n` bytes of the buffer whose
address is in `r` on entry, returning `name`'s result. -/
def callWipe (r : Reg) (n : Nat) (name : String) (body : Prog isa) (zname : String)
    (zcode : Prog isa) : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .lr])
    (.seq (.block (saveArg r))
      (.seq (.call name body)
        (.seq (.block (zeroArgs n))
          (.seq (.call zname zcode) (.block restoreRet)))))
    (.pop .r4 16)

end VG.Impl.CallWipe.Arm
