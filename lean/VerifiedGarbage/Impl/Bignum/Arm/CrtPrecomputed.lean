module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Impl.Bignum.Arm.PrimeR2From

/-! # ARMv7 private RSA CRT given the factors' `R² mod p` and `R² mod q`

`vg_rsa_private_crt_precomputed` takes `vg_rsa_private_crt`'s arguments and
then the address of the factors' `R² mod p` and `R² mod q` (`max(2, ⌈len/8⌉)`
words each, `Spec.Rsa.primeR2`), its incoming argument 14 (frame slot 112).

Each factor is prepared at the narrow width `v` as `narrowPrime` does, but
for its `R² mod X`: when `v` is the factor's own `⌈len/8⌉`, so that `R` is the
radix of the given value, that value is copied into array 4, and replaced by
1, `R² mod 3`, if the key is rejected, without a branch; otherwise `R² mod X`
is computed from 1 (`r2`). The test depends only on the public lengths.

The key check is `vg_rsa_private_crt`'s but for `p q = n`, which the given
values imply. -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

/-- Z set iff the narrow width `v` (header byte 48) is `⌈len/8⌉`, for the
factor's byte length in frame slot `lenSlot`. -/
def r2WidthTest (lenSlot : Nat) : List Instr :=
  [.ldr .r1 .r0 48, .ldrSp .r2 lenSlot, .dp .add .r2 .r2 (.imm 7), .mov .r2 (.shifted .r2 .lsr 3),
   .cmp .r1 (.reg .r2)]

/-- The factor's given `R² mod X` into r1: frame slot 112 for p, and for q
`8 max(2, ⌈p_len/8⌉)` bytes on (`⌈p_len/8⌉ ≥ 1`, so the maximum adds 1 to it
just when it is 1). -/
def r2Source (primeSlot : Nat) : List Instr :=
  .ldrSp .r1 112 :: (if primeSlot = 72 then
    [.ldrSp .r2 68, .dp .add .r2 .r2 (.imm 7), .mov .r2 (.shifted .r2 .lsr 3), .dp .sub .r3 .r2 (.imm 2),
     .mov .r3 (.shifted .r3 .lsr 31), .dp .add .r2 .r2 (.reg .r3), .dp .add .r1 .r1 (.shifted .r2 .lsl 3)]
    else [])

/-- The given `R² mod X` into array 4 (`lowArgs 4`: array 4 in r0, its
`8 v` bytes in lr, and the workspace in r5), and then 1 in its place if the
key is rejected (the acceptance bit at frame slot 48), as `sanitizeModulus`
puts 3 in the modulus' place: array 7 is scratch. -/
def r2Copy (primeSlot : Nat) : Prog isa :=
  .seq (.block (r2Source primeSlot ++ lowArgs 4)) (.seq copyBytes (.seq (.block [.mov .r0 (.reg .r5)])
    (.seq (smallConst 7 1) (.seq (.block [.ldrSp .r11 48]) (selectArray 4 7 4)))))

/-- `R² mod X`: given, or computed from 1. -/
def r2Given (primeSlot : Nat) : Prog isa :=
  .seq (.block (r2WidthTest (primeSlot + 4))) (.ite .eq (r2Copy primeSlot) r2)

/-- `narrowPrime` with `r2Given`. -/
def narrowPrimeGiven (primeSlot : Nat) : Prog isa := .seq (narrowPrimeInv primeSlot) (r2Given primeSlot)

end VG.Impl.Bignum.Arm.Crt

namespace VG.Impl.Bignum.Arm.CrtFn
open VG VG.Arm

/-- `validate` but for `p q = n`. -/
def validateGiven : Prog isa := .seq acceptInput (.seq loadP loadQ)

def codeGiven (phase : Prog isa) : Prog isa := codeOf validateGiven Crt.narrowPrimeGiven phase

end VG.Impl.Bignum.Arm.CrtFn
