module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# Modular exponentiation by a secret exponent on PPC64LE

`powSecret`: `x^d mod m` for an exponent `d` of a public number of bytes,
read most significant first from memory (`r30`, `r31` bytes), whose value is
secret. In the public-key operation's working space (`PublicChecked`): `m` in
array 0, `R² mod m` in array 1, `x` in array 4, with `r10` array 0's base,
`r29` an array's size, `r11` `2 w` and `r12` `-m⁻¹ mod 2³²`; the result in
array 4.

Every bit of every byte is scanned from the top: a Montgomery square and a
Montgomery multiplication by `x R mod m`, the product selected by a mask of
the bit (`PublicChecked.step`). The code is the same for every exponent of
the same length, and nothing branches on its value.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.ModExp

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

/-- The eight bits of the byte at `r30`, from the top, `r30` advanced. -/
def byteScan : Prog isa :=
  .seq (.block [.lbz .r24 .r30 0, .lsl .r24 .r24 56, .addi .r30 .r30 1, .li .r25 8])
    (.loop (.seq PublicChecked.step (.block [.subi .r25 .r25 1])) (.nonzero .d .r25))

/-- The `r31` bytes from `r30`, each scanned. -/
def scan : Prog isa :=
  .loop (.seq byteScan (.block [.subi .r31 .r31 1])) (.nonzero .d .r31)

/-- `x^d mod m` into array 4: `a := R mod m`, `x R mod m` into array 6, the
scan, then out of Montgomery form. -/
def powSecret : Prog isa :=
  .seq one (.seq (montOp 5 1 7) (.seq (montOp 6 4 1) (.seq scan (montOp 4 5 7))))

end VG.Impl.Bignum.PPC64LE.ModExp
