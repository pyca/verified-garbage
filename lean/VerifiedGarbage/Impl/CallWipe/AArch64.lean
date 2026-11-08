module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# A call that wipes part of a buffer afterwards (AArch64)

`callWipe r n name body zname zcode` calls the function `name`, whose code is
`body`, with the arguments its caller was given, all in registers, then zeroes
the first `n` bytes of the buffer whose address was passed in `r` by calling
the zeroize function `zname`, whose code is `zcode`, and returns what `name`
returned. It allocates a frame of 32 bytes: the return address (`x30`, which
each call replaces) at `sp`, the buffer's address at `sp + 8`, saved before
the first call, and `name`'s result at `sp + 16`, saved across the second.
`n` is a 16-bit immediate (`movz`). `callWipe … off` zeroes the `n` bytes at
offset `off` of the buffer instead, for a function that writes only those
(`add x0, x0, #off`, a 12-bit immediate).

The same shape as x86-64's (`Impl/CallWipe/X86_64.lean`), with the return
address saved too: a call on AArch64 leaves it in `x30`, not on the stack.
-/

@[expose] public section

namespace VG.Impl.CallWipe.AArch64

open VG.AArch64

/-- `str x30, [sp]; str r, [sp, #8]`: save the return address and the
buffer's address. -/
def saveArg (r : Reg) : List Instr := [.strSp .x30 0, .strSp r 8]

/-- `str x0, [sp, #16]; ldr x0, [sp, #8]; add x0, x0, #off; movz x1, #n`:
save the result, and pass the address `off` bytes into the buffer and `n` to
the zeroize function (with no `add` for `off = 0`). -/
def zeroArgs (n : Nat) (off : Nat := 0) : List Instr :=
  [.strSp .x0 16, .ldrSp .x0 8] ++ (if off = 0 then [] else [.addImm .x .x0 .x0 off]) ++
    [.movz .x .x1 n 0]

/-- `ldr x0, [sp, #16]; ldr x30, [sp]`: restore the result and the return
address. -/
def restore : List Instr := [.ldrSp .x0 16, .ldrSp .x30 0]

/-- A call of `name`, whose code is `body`, then of the zeroize function
`zname`, whose code is `zcode`, on the `n` bytes at offset `off` (the first
`n`, by default) of the buffer whose address is in `r` on entry, returning
`name`'s result. -/
def callWipe (r : Reg) (n : Nat) (name : String) (body : Prog isa) (zname : String)
    (zcode : Prog isa) (off : Nat := 0) : Prog isa :=
  .frame (.alloc 32)
    (.seq (.block (saveArg r))
      (.seq (.call name body)
        (.seq (.block (zeroArgs n off))
          (.seq (.call zname zcode) (.block restore)))))
    (.free 32)

end VG.Impl.CallWipe.AArch64
