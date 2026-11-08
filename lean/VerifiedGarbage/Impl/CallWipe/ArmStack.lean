module

public import VerifiedGarbage.Impl.CallWipe.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# A call that wipes part of a buffer afterwards, with stack arguments (ARMv7)

`callWipeStack k off n name body zname zcode` is `callWipe` for a function
whose arguments take `k` four-byte words of stack: it calls the function
`name`, whose code is `body`, with the arguments its caller was given, then
zeroes the first `n` bytes of the buffer whose address is the stack argument
at byte offset `off` by calling the zeroize function `zname`, whose code is
`zcode`, and returns what `name` returned, in `r0` and `r1`.

Within `callWipe`'s frame (`push {r4, r5, r6, lr}`), a frame of
`allocSize k` bytes holds a copy of the caller's stack arguments, which is
where `name` finds them (`copyArgs`, through `r12` and `lr`, as
`withStackScratch` does); `r4` keeps the buffer's address, loaded from the
copy, across the call. The frame is freed before the zeroize function is
called. Every instruction is the same in A32 and Thumb.
-/

@[expose] public section

namespace VG.Impl.CallWipe.ArmStack

open VG.Arm VG.Impl.CallWipe.Arm VG.Impl.StackScratch.Arm

/-- The bytes of the frame that holds `k` words of stack arguments: `4k`,
rounded up to a multiple of 8 (the stack's alignment). -/
def allocSize (k : Nat) : Nat := 8 * ((k + 1) / 2)

/-- `add r12, sp, #0`, then for each `j < k`, `ldr lr, [sp, #a + 16 + 4j];
str lr, [r12, #4j]` (`a` the frame's size): copy the caller's `k` stack
argument words, above the two frames, into the frame; then `ldr r4, [sp,
#off]`: keep the buffer's address, from the copy. -/
def copyArgs (k off : Nat) : List Instr :=
  ([.addSp .r12 0] : List Instr) ++ (List.range k).flatMap (copyArg (allocSize k + 16)) ++
    ([.ldrSp .r4 off] : List Instr)

/-- A call of `name`, whose code is `body` and whose arguments take `k`
words of stack, then of the zeroize function `zname`, whose code is
`zcode`, on the first `n` bytes of the buffer whose address is the stack
argument at byte offset `off`, returning `name`'s result. -/
def callWipeStack (k off n : Nat) (name : String) (body : Prog isa) (zname : String)
    (zcode : Prog isa) : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .lr])
    (.seq
      (.frame (.alloc (allocSize k)) (.seq (.block (copyArgs k off)) (.call name body))
        (.free (allocSize k)))
      (.seq (.block (zeroArgs n)) (.seq (.call zname zcode) (.block restoreRet))))
    (.pop .r4 16)

end VG.Impl.CallWipe.ArmStack
