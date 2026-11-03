module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
public import VerifiedGarbage.Impl.Ecdh.P521.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Shr

/-!
# ECDSA over P-521 on RISC-V

`vg_ecdsa_p521_sign(out, d, digest, k, scratch)`: P-256's and P-384's
(`Impl/Ecdsa/RISCV64/Sign.lean`) on P-521's slots and functions, with its
numbers of 66 bytes read and written by `loadLen` and `storeLen`
(`Impl/Ecdh/RISCV64.lean`), and `[k]G` by the ladder, `vg_p521_mul`, for
RFC 6979's signature with SHA-512 (`Impl/Ecdsa/Rfc6979/RISCV64.lean`), which
calls it with SHA-512's 64-byte digest and a candidate's leftmost 66 bytes:
`e` is the digest's number (its 512 bits are fewer than `n`'s 521), and `k`
the leftmost 521 bits of the 66 bytes, their number shifted right by 7 bits
in place (`shrWords`, `Impl/Ecdh/RISCV64/Shr.lean`), as `bits2int` has
them.

`vg_ecdsa_p521_verify`: P-256's and P-384's (`Impl/Ecdsa/RISCV64/Verify.lean`)
on P-521's slots and functions, with the key's coordinates, `r`, `s` and the
digest's 66 bytes read by `loadLen`, `e` the digest's leftmost 521 bits,
their number shifted right by 7 bits (`shrWords`), and `r mod n` by
multiplications (`compareP521`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.P521

open VG.RISCV64 VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify

/-- The bytes of P-521's numbers. -/
abbrev len : Nat := 66

/-- The digest's bytes. -/
abbrev dlen : Nat := 64

/-- Signing's setup (`Sign.Cfg.setup`), with numbers of 66 bytes, `k` the 66
bytes' number shifted right by 7 bits, and `e` the digest's 64 bytes (its
top word zero). -/
def signSetup : List Instr :=
  Cfg.saveCode .a4 ++ loadLen len (p521.sl K) .a3 0 ++ shrWords 9 (p521.sl K) 7 ++
    loadLen len (p521.sl DD) .a1 0 ++ loadLen dlen (p521.sl EE) .a2 0 ++ setConst 1 (p521.sl EE + dlen) 0 ++
    [.li .t0 0, .addi .t0 .t0 (-1)] ++ sdAt .t0 wb (p521.sl FLAG) ++
    Cfg.constCode p521 ++ (Sign.Cfg.nConsts p521).flatMap (fun (i, x) => setConst 9 (p521.sl i) x) ++
    Cfg.rangeOf p521 DD ++ copy 9 (p521.sl RX) (p521.sl GX) ++ copy 9 (p521.sl RY) (p521.sl GY)

/-- Signing's end (`Sign.Cfg.finish`), with numbers of 66 bytes. -/
def signFinish : List Instr :=
  Sign.Cfg.nonzeroFlag p521 RR ++ Sign.Cfg.nonzeroFlag p521 SS ++ ldAt .a7 wb (p521.sl FLAG) ++
    storeLen len (p521.sl RR) .s2 0 ++ storeLen len (p521.sl SS) .s2 len ++ Cfg.retCode p521

/-- `vg_ecdsa_p521_sign(out = a0, d = a1, digest = a2, k = a3, scratch = a4)`,
with `[k]G` by four-bit windows, `vg_p521_mul`. -/
def signP521 : Prog isa :=
  .seq (.block signSetup) <|
  .seq (Cfg.tail p521 "vg_p521_mul" mulP521) <|
  .seq (.seq (addCall p521Order (p521.sl RR) (p521.sl XO) (p521.sl ZERO)) (Sign.Cfg.scalars p521 p521Order))
    (.block signFinish)

/-- Verification's setup (`Verify.Cfg.setup`), with numbers of 66 bytes and
`e` the digest's number shifted right by 7 bits. -/
def verifySetup : List Instr :=
  Cfg.saveCode .a3 ++ loadLen p521.C.len (p521.sl CX) .a0 1 ++ loadLen p521.C.len (p521.sl CY) .a0 (1 + p521.C.len) ++
    leadMask .a0 ++ sdAt .a7 wb (p521.sl FLAG) ++ Cfg.constCode p521 ++
    loadLen len (p521.sl VR) .a2 0 ++ loadLen len (p521.sl VS) .a2 len ++ loadLen len (p521.sl VE) .a1 0 ++
    shrWords 9 (p521.sl VE) 7 ++ Cfg.rangeOf p521 VR ++ Cfg.rangeOf p521 VS

/-- `x mod n`, `r mod n` and their difference (`Verify.Cfg.compare`), with
`r mod n` by multiplications, `r R mod n` then times one: `r`'s 66 bytes may
make it as large as `2^528`, past the addition's `2n`. -/
def compareP521 : Prog isa :=
  progs [addCall p521Order (p521.sl XN) (p521.sl XO) (p521.sl ZERO),
    mulCall p521Order (p521.sl RM) (p521.sl VR) (p521.sl R2N),
    mulCall p521Order (p521.sl RN) (p521.sl RM) (p521.sl ONE),
    subCall p521Order (p521.sl WD) (p521.sl XN) (p521.sl RN)]

/-- `vg_ecdsa_p521_verify(public = a0, digest = a1, sig = a2, scratch = a3)`. -/
def verifyP521 : Prog isa :=
  .seq (.block verifySetup) <|
  .seq (Cfg.wsCall "vg_p521_check_point" checkP521) <|
  .seq (.block ((Sign.Cfg.nConsts p521).flatMap (fun (i, x) => setConst 9 (p521.sl i) x))) <|
  .seq (Verify.Cfg.uv p521 p521Order) <|
  .seq (VerifyJ.Cfg.joint p521 Impl.Weierstrass.dblJ) <|
  .seq (chainPow (Cfg.chainP p521) (p521.sl ONEP) p521.FP) <|
  .seq (Cfg.affineCoord p521 XM XO RX) <|
  .seq compareP521 (.block (Verify.Cfg.finish p521))

end VG.Impl.Ecdsa.RISCV64.P521
