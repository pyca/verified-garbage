module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign

/-!
# DSA key derivation on PPC64LE

`vg_dsa_derive_key(out = r3, out_len = r4, params = r5, params_len = r6,
p_len = r7, x = r8, q_len = r9, scratch = r10, scratch_len)`, `scratch_len`
on the stack (the code does not read it). The entry saves the nonvolatile
registers in `scratch`'s header and keeps the domain p||q||g, x and `out` in
`r27`, `r28` and `r26`, and the lengths in `r2`. After `checkParams`
(`Common.lean`), which branches on the domain only:

* in the P space, `y = g^x mod p` (`powP` over x's octets) into array 4,
  the mask of `y ≠ 0` and `y ≠ 1` (`nonZero` against 0, then 1, in array 7)
  in `r22`, and y to the buffer's first `p_len` octets (`storeBE`); `y < p`
  holds by construction, as does `y^q mod p = 1` from `g^q mod p = 1`;
* in the Q space, x into array 5 and `r22 &=` the mask of `0 < x < q`
  (`inRange`);
* the domain, y (from the buffer) and x, each octet and'ed with the mask, to
  `out` (`maskCopy`); the result is the mask's low bit.

A domain that fails the checks zeroes `out` and returns 0. Nothing branches
on x or y, only on the domain and the lengths.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Derive

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (one)

/-- The working space (`scratch`), the registers saved there, the domain, x
and `out` into `r27`, `r28` and `r26`, and the lengths into `r2`. -/
def entry : List Instr :=
  [.addi .r11 .r10 0] ++ save .r11 ++
    [.addi .r27 .r5 0, .addi .r28 .r8 0, .addi .r26 .r3 0, .lsl .r0 .r9 16, .add .r2 .r7 .r0]

/-- In the P space: `y = g^x mod p` into array 4, `r22 :=` the mask of
`y ≠ 0` and `y ≠ 1`, and y to the buffer's first `p_len` octets. -/
def yValue : Prog isa :=
  .seq (.block ([.addi .r24 .r28 0] ++ ptrG)) (.seq Verify.powP (.seq (Verify.zeroArr 7)
    (.seq (.block [.li .r22 0, .subi .r22 .r22 1]) (.seq (Sign.nonZero 4) (.seq one (.seq (Sign.nonZero 4)
      (.seq (.block (bufBase .r12 .r0 ++ getP .r6)) (storeBE 4))))))))

/-- In the Q space: x into array 5, 0 into array 7, `r22 &=` the mask of
`0 < x < q`, and the mask into `r20`. -/
def xRange : Prog isa :=
  .seq (.block (enterQ ++ Verify.ptrR)) (.seq (loadArr 5) (.seq (Verify.zeroArr 7)
    (.seq (Verify.inRange 5) (.block [.addi .r20 .r22 0]))))

/-- The `r17 > 0` octets at `r14`, each and'ed with `r20`, to `r16`. -/
def maskCopy : Prog isa :=
  Precompute.countLoop .r17 [.lbz .r0 .r14 0, .logic .and .r0 .r0 .r20, .stb .r0 .r16 0, .addi .r14 .r14 1,
    .addi .r16 .r16 1]

/-- The domain, y (from the buffer) and x, masked by `r20`, to `out`;
`r3 :=` the mask's low bit. -/
def output : Prog isa :=
  .seq (.block ([.addi .r16 .r26 0, .addi .r14 .r27 0] ++ getP .r17 ++ getQ .r0 ++
      [.add .r17 .r17 .r17, .add .r17 .r17 .r0]))
    (.seq maskCopy (.seq (.block (bufBase .r12 .r0 ++ [.addi .r14 .r12 0] ++ getP .r17)) (.seq maskCopy
      (.seq (.block ([.addi .r14 .r28 0] ++ getQ .r17)) (.seq maskCopy (.block [.li .r0 1, .logic .and .r3 .r20 .r0]))))))

/-- The derivation, after the check of the domain. -/
def body : Prog isa := .seq yValue (.seq xRange output)

/-- `out`'s `3 p_len + 2 q_len` octets := 0, and `r3 := 0`. -/
def zeroOut : Prog isa :=
  .seq (.block ([.addi .r16 .r26 0] ++ getP .r17 ++ getQ .r0 ++
      [.add .r0 .r0 .r17, .add .r17 .r17 .r0, .add .r17 .r17 .r0, .li .r0 0]))
    (.seq (Precompute.countLoop .r17 [.stb .r0 .r16 0, .addi .r16 .r16 1]) (.block [.li .r3 0]))

/-- `vg_dsa_derive_key`. -/
def derive : Prog isa :=
  .seq (.block entry) (.seq (checkParams body zeroOut) (.block restore))

end VG.Impl.Dsa.PPC64LE.Derive
