module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64

/-!
# P-192's point compression and decompression on RISC-V

As P-256's and P-384's (`Impl/EcKey/Compressed/RISCV64.lean`, for
`p ≡ 3 (mod 4)`), with P-192's numbers of 24 bytes in four words whose top
one is zero (`loadNum0`, and `storeNum` of the low three words).
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64.Cfg

/-- `vg_ec_p192_compress_public_key`. -/
def compressP192 : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum0 3 (p192.sl CX) .a1 1 ++ loadNum0 3 (p192.sl CY) .a1 25 ++
    leadMask .a1 ++ sdAt .a7 wb (p192.sl FLAG) ++ constCode p192)) <|
  .seq (wsCall "vg_p192_check_point" checkP192) <|
  .block (ldAt .a7 wb (p192.sl FLAG) ++ [.load .d .t0 wb (p192.sl CY), .logicImm .and .t0 .t0 1, .addi .t0 .t0 2,
      .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ storeNum 3 (p192.sl CX) .s2 1 ++ retCode p192)

/-- `vg_ec_p192_decompress_public_key`. -/
def decompressP192 : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum0 3 (p192.sl CX) .a1 1 ++ parCode p192 .a1 ++ tagMask .a1 ++
    sdAt .a7 wb (p192.sl FLAG) ++ constCode p192 ++ setConst 4 (p192.sl EXPS) ((p192.C.p + 1) / 4) ++
    ltMask 4 (p192.sl CX) (p192.sl MP) ++ andFlag p192)) <|
  .seq (fprog p192Field (rhsOps p192)) <|
  .seq (pow (sqrtP p192) p192Field) <|
  .seq (fprog p192Field (rootOps p192)) <|
  .block (zeroMask 4 (p192.sl DIF) ++ andFlag p192 ++ parMask p192 Y1 ++ sel 4 (p192.sl YF) (p192.sl Y1) (p192.sl Y2) ++
    sameMask p192 YF ++ andFlag p192 ++ ldAt .a7 wb (p192.sl FLAG) ++ pointOut192 CX YF)

end VG.Impl.EcKey.Compressed.RISCV64
