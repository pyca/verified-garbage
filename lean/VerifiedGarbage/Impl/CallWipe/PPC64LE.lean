module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# A call that wipes part of a buffer afterwards (PPC64LE)

`callWipe r n name body zname zcode` calls the function `name`, whose code is
`body`, with the arguments its caller was given, all in registers, then zeroes
the first `n` bytes of the buffer whose address was passed in `r` by calling
the zeroize function `zname`, whose code is `zcode`, and returns what `name`
returned.

The calls change the link register, which the code saves in `r0` and a
48-byte frame saving `r0` (`stdu r1, -48(r1)`; `std r0, 32(r1)`). The
frame's other doubleword, at `r1 + 40`, saves `r31`, which keeps the buffer's
address across the first call and `name`'s result across the second:
`r31` is callee-saved.
-/

@[expose] public section

namespace VG.Impl.CallWipe.PPC64LE

open VG.PPC64LE

/-- `mr d, n`. -/
def mov (d n : Reg) : Instr := .logic .or d n n

/-- `addi r12, r1, 40; std r31, 0(r12); mr r31, r`: save `r31`, and keep the
buffer's address in it. -/
def saveArg (r : Reg) : List Instr := [.addSp .r12 40, .store .d .r31 .r12 0, mov .r31 r]

/-- `mr r11, r3; mr r3, r31; li r4, 0; oris r4, r4, n >> 16; ori r4, r4, n`;
`mr r31, r11`: keep the result in `r31`, and pass the buffer's address and
`n` to the zeroize function. -/
def zeroArgs (n : Nat) : List Instr :=
  [mov .r11 .r3, mov .r3 .r31, .li .r4 0, .oris .r4 .r4 (BitVec.ofNat 16 (n / 2 ^ 16)),
    .ori .r4 .r4 (BitVec.ofNat 16 n), mov .r31 .r11]

/-- `mr r3, r31; addi r12, r1, 40; ld r31, 0(r12)`: restore the result and
`r31`. -/
def restoreRet : List Instr := [mov .r3 .r31, .addSp .r12 40, .load .d .r31 .r12 0]

/-- A call of `name`, whose code is `body`, then of the zeroize function
`zname`, whose code is `zcode`, on the first `n` bytes of the buffer whose
address is in `r` on entry, returning `name`'s result. -/
def callWipe (r : Reg) (n : Nat) (name : String) (body : Prog isa) (zname : String)
    (zcode : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq
      (.frame (.push .r0)
        (.seq (.block (saveArg r))
          (.seq (.call name body)
            (.seq (.block (zeroArgs n))
              (.seq (.call zname zcode) (.block restoreRet)))))
        (.pop .r0))
      (.block [.mtlr .r0]))

end VG.Impl.CallWipe.PPC64LE
