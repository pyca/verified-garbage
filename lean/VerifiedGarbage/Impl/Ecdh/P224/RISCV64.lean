module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# P-224's check of a public point, ECDH and public keys on RISC-V

As P-256's and P-384's (`Impl/Ecdh/RISCV64.lean`), but for P-224's numbers
of 28 bytes, which are four words with the top one of four bytes:
`loadNum4` reads the top word from four bytes (`loadBE32`), then three
doublewords, and `storeNum4` writes the top word's low four bytes, then
three doublewords.
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Weierstrass.RISCV64

/-- `[o] = ` the big-endian number of `8 k + 4` bytes at `p + off`: its top
word from the first four bytes, then `k` doublewords, through `t0` and `t1`. -/
def loadNum4 (k o : Nat) (p : Reg) (off : Nat) : List Instr :=
  Impl.Words.RISCV64.loadBE32 .t0 .t1 p off ++ [.store .d .t0 wb (o + 8 * k)] ++ loadNum k o p (off + 4)

/-- The `k + 1`-word number at `a` under the mask `a7`, to `q + off`
big-endian in `8 k + 4` bytes: its top word's low four bytes, then `k`
doublewords, through `t0` and `t1`. -/
def storeNum4 (k a : Nat) (q : Reg) (off : Nat) : List Instr :=
  [.load .d .t0 wb (a + 8 * k), .logic .and .t0 .t0 .a7] ++ Impl.Words.RISCV64.storeBE 4 .t0 .t1 q off ++
    storeNum k a q (off + 4)

/-- `vg_p224_check_point`. -/
def checkP224 : Prog isa := Cfg.checkFn p224

/-- `04 ‖ x ‖ y` (or zeros, by the mask `a7`) to `out` (in `s2`), from the
slots `xo` and `yo`, the flag's low bit returned and the registers
restored. -/
def pointOut224 (xo yo : Nat) : List Instr :=
  [.li .t0 4, .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ storeNum4 3 (p224.sl xo) .s2 1 ++
    storeNum4 3 (p224.sl yo) .s2 29 ++ Cfg.retCode p224

/-- `vg_ecdh_p224(out = a0, d = a1, peer = a2, scratch = a3)`. -/
def ecdhP224 : Prog isa :=
  .seq (.block (Cfg.saveCode .a3 ++ loadNum4 3 (p224.sl K) .a1 0 ++ loadNum4 3 (p224.sl CX) .a2 1 ++
    loadNum4 3 (p224.sl CY) .a2 29 ++ leadMask .a2 ++ sdAt .a7 wb (p224.sl FLAG) ++ Cfg.constCode p224)) <|
  .seq (Cfg.wsCall "vg_p224_check_point" checkP224) <|
  .seq (.block (copy 4 (p224.sl RX) (p224.sl CPX) ++ copy 4 (p224.sl RY) (p224.sl CPY))) <|
  .seq (Cfg.tail p224 "vg_p224_mul" mulP224) <|
  .block (Cfg.zCode p224 ++ storeNum4 3 (p224.sl XO) .s2 0 ++ Cfg.retCode p224)

/-- `vg_ec_p224_public_key(out = a0, d = a1, scratch = a2)`, with `[d]G` by
the ladder, `vg_p224_mul`. -/
def publicKeyP224 : Prog isa :=
  .seq (.block (Cfg.saveCode .a2 ++ loadNum4 3 (p224.sl K) .a1 0 ++
    [.li .t0 0, .addi .t0 .t0 (-1)] ++ sdAt .t0 wb (p224.sl FLAG) ++ Cfg.constCode p224 ++
    copy 4 (p224.sl RX) (p224.sl GX) ++ copy 4 (p224.sl RY) (p224.sl GY))) <|
  .seq (Cfg.tail p224 "vg_p224_mul" mulP224) <|
  .seq (Cfg.affineCoord p224 YM YO RY) <|
  .block (Cfg.zCode p224 ++ pointOut224 XO YO)

end VG.Impl.Ecdh.RISCV64
