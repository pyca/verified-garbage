module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64

/-!
# ECDSA over P-192 on RISC-V

`vg_ecdsa_p192_sign` and `vg_ecdsa_p192_verify`: P-256's and P-384's
(`Impl/Ecdsa/RISCV64/Sign.lean`, `Impl/Ecdsa/RISCV64/Verify.lean`) on
P-192's slots and functions, with its numbers of 24 bytes in four words
whose top one is zero, read by `loadNum0` (`Impl/Ecdh/RISCV64/Num0.lean`)
and written by `storeNum` of the low three words, and `[k]G` by the ladder,
`vg_p192_mul`. The hash's integer `e` is the digest's first 24 bytes, as `n`
has 192 bits.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.P192

open VG.RISCV64 VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify

/-- Signing's setup (`Sign.Cfg.setup`), with numbers of 24 bytes. -/
def signSetup : List Instr :=
  Cfg.saveCode .a4 ++ loadNum0 3 (p192.sl K) .a3 0 ++ loadNum0 3 (p192.sl DD) .a1 0 ++
    loadNum0 3 (p192.sl EE) .a2 0 ++ [.li .t0 0, .addi .t0 .t0 (-1)] ++ sdAt .t0 wb (p192.sl FLAG) ++
    Cfg.constCode p192 ++ (Sign.Cfg.nConsts p192).flatMap (fun (i, x) => setConst 4 (p192.sl i) x) ++
    Cfg.rangeOf p192 DD ++ copy 4 (p192.sl RX) (p192.sl GX) ++ copy 4 (p192.sl RY) (p192.sl GY)

/-- Signing's end (`Sign.Cfg.finish`), with numbers of 24 bytes. -/
def signFinish : List Instr :=
  Sign.Cfg.nonzeroFlag p192 RR ++ Sign.Cfg.nonzeroFlag p192 SS ++ ldAt .a7 wb (p192.sl FLAG) ++
    storeNum 3 (p192.sl RR) .s2 0 ++ storeNum 3 (p192.sl SS) .s2 24 ++ Cfg.retCode p192

/-- `vg_ecdsa_p192_sign(out = a0, d = a1, digest = a2, k = a3, scratch = a4)`,
with `[k]G` by the ladder, `vg_p192_mul`. -/
def signP192 : Prog isa :=
  .seq (.block signSetup) <|
  .seq (Cfg.tail p192 "vg_p192_mul" mulP192) <|
  .seq (.seq (addCall p192Order (p192.sl RR) (p192.sl XO) (p192.sl ZERO)) (Sign.Cfg.scalars p192 p192Order))
    (.block signFinish)

/-- Verification's setup (`Verify.Cfg.setup`), with numbers of 24 bytes. -/
def verifySetup : List Instr :=
  Cfg.saveCode .a3 ++ loadNum0 3 (p192.sl CX) .a0 1 ++ loadNum0 3 (p192.sl CY) .a0 25 ++
    leadMask .a0 ++ sdAt .a7 wb (p192.sl FLAG) ++ Cfg.constCode p192 ++
    loadNum0 3 (p192.sl VR) .a2 0 ++ loadNum0 3 (p192.sl VS) .a2 24 ++ loadNum0 3 (p192.sl VE) .a1 0 ++
    Cfg.rangeOf p192 VR ++ Cfg.rangeOf p192 VS

/-- `vg_ecdsa_p192_verify(public = a0, digest = a1, sig = a2, scratch = a3)`. -/
def verifyP192 : Prog isa :=
  .seq (.block verifySetup) <|
  .seq (Cfg.wsCall "vg_p192_check_point" checkP192) <|
  .seq (.block ((Sign.Cfg.nConsts p192).flatMap (fun (i, x) => setConst 4 (p192.sl i) x))) <|
  .seq (Verify.Cfg.uv p192 p192Order) <|
  .seq (VerifyJ.Cfg.joint p192 Impl.Weierstrass.dblJ) <|
  .seq (chainPow (Cfg.chainP p192) (p192.sl ONEP) p192.FP) <|
  .seq (Cfg.affineCoord p192 XM XO RX) <|
  .seq (Verify.Cfg.compare p192 p192Order) (.block (Verify.Cfg.finish p192))

end VG.Impl.Ecdsa.RISCV64.P192
