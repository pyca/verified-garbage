module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64

/-!
# ECDSA over P-224 on RISC-V

`vg_ecdsa_p224_sign` and `vg_ecdsa_p224_verify`: P-256's and P-384's
(`Impl/Ecdsa/RISCV64/Sign.lean`, `Impl/Ecdsa/RISCV64/Verify.lean`) on
P-224's slots and functions, with its numbers of 28 bytes read and written
by `loadNum4` and `storeNum4` (`Impl/Ecdh/RISCV64/Num4.lean`), and `[k]G` by
the ladder, `vg_p224_mul`. The hash's integer `e` is the digest's 28 bytes,
as `n` has 224 bits.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.P224

open VG.RISCV64 VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify

/-- Signing's setup (`Sign.Cfg.setup`), with numbers of 28 bytes. -/
def signSetup : List Instr :=
  Cfg.saveCode .a4 ++ loadNum4 3 (p224.sl K) .a3 0 ++ loadNum4 3 (p224.sl DD) .a1 0 ++
    loadNum4 3 (p224.sl EE) .a2 0 ++ [.li .t0 0, .addi .t0 .t0 (-1)] ++ sdAt .t0 wb (p224.sl FLAG) ++
    Cfg.constCode p224 ++ (Sign.Cfg.nConsts p224).flatMap (fun (i, x) => setConst 4 (p224.sl i) x) ++
    Cfg.rangeOf p224 DD ++ copy 4 (p224.sl RX) (p224.sl GX) ++ copy 4 (p224.sl RY) (p224.sl GY)

/-- Signing's end (`Sign.Cfg.finish`), with numbers of 28 bytes. -/
def signFinish : List Instr :=
  Sign.Cfg.nonzeroFlag p224 RR ++ Sign.Cfg.nonzeroFlag p224 SS ++ ldAt .a7 wb (p224.sl FLAG) ++
    storeNum4 3 (p224.sl RR) .s2 0 ++ storeNum4 3 (p224.sl SS) .s2 28 ++ Cfg.retCode p224

/-- `vg_ecdsa_p224_sign(out = a0, d = a1, digest = a2, k = a3, scratch = a4)`,
with `[k]G` by the ladder, `vg_p224_mul`. -/
def signP224 : Prog isa :=
  .seq (.block signSetup) <|
  .seq (Cfg.tail p224 "vg_p224_mul" mulP224) <|
  .seq (.seq (addCall p224Order (p224.sl RR) (p224.sl XO) (p224.sl ZERO)) (Sign.Cfg.scalars p224 p224Order))
    (.block signFinish)

/-- Verification's setup (`Verify.Cfg.setup`), with numbers of 28 bytes. -/
def verifySetup : List Instr :=
  Cfg.saveCode .a3 ++ loadNum4 3 (p224.sl CX) .a0 1 ++ loadNum4 3 (p224.sl CY) .a0 29 ++
    leadMask .a0 ++ sdAt .a7 wb (p224.sl FLAG) ++ Cfg.constCode p224 ++
    loadNum4 3 (p224.sl VR) .a2 0 ++ loadNum4 3 (p224.sl VS) .a2 28 ++ loadNum4 3 (p224.sl VE) .a1 0 ++
    Cfg.rangeOf p224 VR ++ Cfg.rangeOf p224 VS

/-- `vg_ecdsa_p224_verify(public = a0, digest = a1, sig = a2, scratch = a3)`. -/
def verifyP224 : Prog isa :=
  .seq (.block verifySetup) <|
  .seq (Cfg.wsCall "vg_p224_check_point" checkP224) <|
  .seq (.block ((Sign.Cfg.nConsts p224).flatMap (fun (i, x) => setConst 4 (p224.sl i) x))) <|
  .seq (Verify.Cfg.uv p224 p224Order) <|
  .seq (Verify.Cfg.joint p224) <|
  .seq (chainPow (Cfg.chainP p224) (p224.sl ONEP) p224.FP) <|
  .seq (Cfg.affineCoord p224 XM XO RX) <|
  .seq (Verify.Cfg.compare p224 p224Order) (.block (Verify.Cfg.finish p224))

end VG.Impl.Ecdsa.RISCV64.P224
