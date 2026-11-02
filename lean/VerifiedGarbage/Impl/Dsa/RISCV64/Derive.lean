module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign

/-!
# DSA key derivation on RISC-V

`vg_dsa_derive_key(out = a0, out_len = a1, params = a2, params_len = a3,
p_len = a4, x = a5, q_len = a6, scratch = a7, scratch_len)`, `scratch_len`
on the stack (the code does not read it). As on PPC64LE
(`Impl/Dsa/PPC64LE/Derive.lean`): the entry saves the callee-saved
registers in `scratch`'s header and keeps the domain p||q||g and x in `s11`
and `ra`, and `out` and the lengths in the header. After `checkParams`
(`Common.lean`), which branches on the domain only:

* in the P space, `y = g^x mod p` (`powP` over x's octets) into array 4,
  the mask of `y ≠ 0` and `y ≠ 1` (`nonZero` against 0, then 1, in array 7)
  in `a4`, and y to the buffer's first `p_len` octets (`storeBE`); `y < p`
  holds by construction, as does `y^q mod p = 1` from `g^q mod p = 1`;
* in the Q space, x into array 5 and `a4 &=` the mask of `0 < x < q`
  (`inRange`);
* the domain, y (from the buffer) and x, each octet and'ed with the mask, to
  `out` (`maskCopy`); the result is the mask's low bit.

A domain that fails the checks zeroes `out` and returns 0. Nothing branches
on x or y, only on the domain and the lengths.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Derive

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (one)

/-- The working space (`scratch`), the registers saved there, the domain and
x into `s11` and `ra`, and `out` and the lengths into the header. -/
def entry : List Instr :=
  [.addi .t2 .a7 0] ++ save .t2 ++
    [.addi .s11 .a2 0, .addi .ra .a5 0, .store .d .a0 .s6 Sign.hOut, .shift .sll .d .t3 .a6 16,
      .add .t3 .a4 .t3, .store .d .t3 .s6 hLens]

/-- In the P space: `y = g^x mod p` into array 4, `a4 :=` the mask of
`y ≠ 0` and `y ≠ 1`, and y to the buffer's first `p_len` octets. -/
def yValue : Prog isa :=
  .seq (.block ([.addi .s9 .ra 0] ++ ptrG)) (.seq Verify.powP (.seq (zeroArr 7)
    (.seq (.block [.li .a4 (-1)]) (.seq (Sign.nonZero 4) (.seq one (.seq (Sign.nonZero 4)
      (.seq (.block (bufBase .s7 .t2 ++ getP .s8)) (storeBE 4))))))))

/-- In the Q space: x into array 5, 0 into array 7, and `a4 &=` the mask of
`0 < x < q`. -/
def xRange : Prog isa :=
  .seq (.block (enterQ ++ Verify.ptrR)) (.seq (loadArr 5) (.seq (zeroArr 7) (Verify.inRange 5)))

/-- The `t5 > 0` octets at `t3`, each and'ed with `a4`, to `t4`. -/
def maskCopy : Prog isa :=
  countLoop .t5 [.load .b .s0 .t3 0, .logic .and .s0 .s0 .a4, .store .b .s0 .t4 0, .addi .t3 .t3 1,
    .addi .t4 .t4 1]

/-- The domain, y (from the buffer) and x, masked by `a4`, to `out`;
`a0 :=` the mask's low bit. -/
def output : Prog isa :=
  .seq (.block ([.load .d .t4 .s6 Sign.hOut, .addi .t3 .s11 0] ++ getP .t5 ++ getQ .t2 ++
      [.add .t5 .t5 .t5, .add .t5 .t5 .t2]))
    (.seq maskCopy (.seq (.block (bufBase .t3 .t2 ++ getP .t5)) (.seq maskCopy
      (.seq (.block ([.addi .t3 .ra 0] ++ getQ .t5)) (.seq maskCopy (.block [.logicImm .and .a0 .a4 1]))))))

/-- The derivation, after the check of the domain. -/
def body : Prog isa := .seq yValue (.seq xRange output)

/-- `out`'s `3 p_len + 2 q_len` octets := 0, and `a0 := 0`. -/
def zeroOut : Prog isa :=
  .seq (.block ([.load .d .t4 .s6 Sign.hOut] ++ getP .t5 ++ getQ .t2 ++
      [.add .t2 .t2 .t5, .add .t5 .t5 .t2, .add .t5 .t5 .t2, .li .s0 0]))
    (.seq (countLoop .t5 [.store .b .s0 .t4 0, .addi .t4 .t4 1]) (.block [.li .a0 0]))

/-- `vg_dsa_derive_key`. -/
def derive : Prog isa :=
  .seq (.block entry) (.seq (checkParams body zeroOut) (.block restore))

end VG.Impl.Dsa.RISCV64.Derive
