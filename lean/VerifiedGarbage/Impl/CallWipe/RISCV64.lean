module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# A call that wipes part of a buffer afterwards (RISC-V)

`callWipe fs r n name body zname zcode` calls the function `name`, whose code is
`body`, with the arguments its caller was given, all in registers, then zeroes
the first `n` bytes of the buffer whose address was passed in `r` by calling
the zeroize function `zname`, whose code is `zcode`, and returns what `name`
returned. It allocates a frame of `fs` bytes (a multiple of 16, with
`32 ≤ fs < 2048`; the frame's size sets where the callees' stack lies,
relative to the caller's): the return address (`ra`, which
each call replaces) at `sp`, the buffer's address at `sp + 8`, saved before
the first call, and `name`'s result at `sp + 16`, saved across the second.
The frame is addressed through `t0` (`addi t0, sp, 0`), as the model's loads
and stores take a base register; `n` is below `2^31 - 2048`: one `li` or `li`
and `addi` of 12-bit immediates below 4095, else a `lui` and, unless `n` is
a multiple of 4096, an `addi`.

The same shape as AArch64's (`Impl/CallWipe/AArch64.lean`).
-/

@[expose] public section

namespace VG.Impl.CallWipe.RISCV64

open VG.RISCV64

/-- `addi t0, sp, 0; sd ra, 0(t0); sd r, 8(t0)`: save the return address
and the buffer's address. -/
def saveArg (r : Reg) : List Instr := [.addSp .t0 0, .store .d .ra .t0 0, .store .d r .t0 8]

/-- The `lui` immediate of `n < 2^31 - 2048`: `n` rounded to the nearest
multiple of 4096, in units of 4096. -/
def hiOf (n : Nat) : Nat := (n + 2048) / 4096

/-- The rest of `n` after `hiOf n`, in `[-2048, 2048)`: an `addi`'s immediate. -/
def loOf (n : Nat) : Int := (n : Int) - 4096 * hiOf n

/-- `li a1, n`, as one `li` below 2048, `li a1, 2047; addi a1, a1, n - 2047`
below 4095, else `lui a1, hiOf n` then, unless it is zero, `addi a1, a1, loOf n`. -/
def lenArg (n : Nat) : List Instr :=
  if n < 2048 then [.li .a1 n]
  else if n < 4095 then [.li .a1 2047, .addi .a1 .a1 ((n : Int) - 2047)]
  else .lui .a1 (BitVec.ofNat 20 (hiOf n)) :: if loOf n = 0 then [] else [.addi .a1 .a1 (loOf n)]

/-- `addi t0, sp, 0; sd a0, 16(t0); ld a0, 8(t0); li a1, n`: save the
result, and pass the buffer's address and `n` to the zeroize function. -/
def zeroArgs (n : Nat) : List Instr :=
  [.addSp .t0 0, .store .d .a0 .t0 16, .load .d .a0 .t0 8] ++ lenArg n

/-- `addi t0, sp, 0; ld a0, 16(t0); ld ra, 0(t0)`: restore the result and
the return address. -/
def restore : List Instr := [.addSp .t0 0, .load .d .a0 .t0 16, .load .d .ra .t0 0]

/-- A call of `name`, whose code is `body`, then of the zeroize function
`zname`, whose code is `zcode`, on the first `n` bytes of the buffer whose
address is in `r` on entry, returning `name`'s result. -/
def callWipe (fs : Nat) (r : Reg) (n : Nat) (name : String) (body : Prog isa) (zname : String)
    (zcode : Prog isa) : Prog isa :=
  .frame (.alloc fs)
    (.seq (.block (saveArg r))
      (.seq (.call name body)
        (.seq (.block (zeroArgs n))
          (.seq (.call zname zcode) (.block restore)))))
    (.free fs)

end VG.Impl.CallWipe.RISCV64
