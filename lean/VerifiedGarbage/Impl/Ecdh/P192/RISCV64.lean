module

public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num0
public import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-!
# P-192's check of a public point, ECDH and public keys on RISC-V

As P-256's and P-384's (`Impl/Ecdh/RISCV64.lean`), but for P-192's numbers
of 24 bytes, in four words whose top one is zero (`loadNum0`,
`Impl/Ecdh/RISCV64/Num0.lean`; `storeNum` of the low three words).
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Weierstrass.RISCV64

/-- `vg_p192_check_point`. -/
def checkP192 : Prog isa := Cfg.checkFn p192

/-- `04 ‖ x ‖ y` (or zeros, by the mask `a7`) to `out` (in `s2`), from the
slots `xo` and `yo`, the flag's low bit returned and the registers
restored. -/
def pointOut192 (xo yo : Nat) : List Instr :=
  [.li .t0 4, .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ storeNum 3 (p192.sl xo) .s2 1 ++
    storeNum 3 (p192.sl yo) .s2 25 ++ Cfg.retCode p192

/-- `vg_ecdh_p192(out = a0, d = a1, peer = a2, scratch = a3)`. -/
def ecdhP192 : Prog isa :=
  .seq (.block (Cfg.saveCode .a3 ++ loadNum0 3 (p192.sl K) .a1 0 ++ loadNum0 3 (p192.sl CX) .a2 1 ++
    loadNum0 3 (p192.sl CY) .a2 25 ++ leadMask .a2 ++ sdAt .a7 wb (p192.sl FLAG) ++ Cfg.constCode p192)) <|
  .seq (Cfg.wsCall "vg_p192_check_point" checkP192) <|
  .seq (.block (copy 4 (p192.sl RX) (p192.sl CPX) ++ copy 4 (p192.sl RY) (p192.sl CPY))) <|
  .seq (Cfg.tail p192 "vg_p192_mul" mulP192) <|
  .block (Cfg.zCode p192 ++ storeNum 3 (p192.sl XO) .s2 0 ++ Cfg.retCode p192)

/-- `vg_ec_p192_public_key(out = a0, d = a1, scratch = a2)`, with `[d]G` by
the ladder, `vg_p192_mul`. -/
def publicKeyP192 : Prog isa :=
  .seq (.block (Cfg.saveCode .a2 ++ loadNum0 3 (p192.sl K) .a1 0 ++
    [.li .t0 0, .addi .t0 .t0 (-1)] ++ sdAt .t0 wb (p192.sl FLAG) ++ Cfg.constCode p192 ++
    copy 4 (p192.sl RX) (p192.sl GX) ++ copy 4 (p192.sl RY) (p192.sl GY))) <|
  .seq (Cfg.tail p192 "vg_p192_mul" mulP192) <|
  .seq (Cfg.affineCoord p192 YM YO RY) <|
  .block (Cfg.zCode p192 ++ pointOut192 XO YO)

end VG.Impl.Ecdh.RISCV64
