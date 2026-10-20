module

public import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM-1024 on AArch64: compression with encoding, and decoding with decompression

`ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d` for the widths
`d` = 5 and 11 of ML-KEM-1024, in vectors of four `u32` coefficients, with
the steps of ML-KEM-768's (`Impl/MlKem/AArch64/Compress.lean`).

* `compressEncode(f = x0, d = w1, out = x2, len = x3)`: `Compress_d(x)` of a
  lane is `((x · M_d + 261888) >> 19) mod 2ᵈ` (`cmpV`, with `M_d` and the
  addend of `width5` and `width11`). For `d = 5` pairs of lanes are paired
  twice (`pairV`) and the words paired into doublewords (`dpairV`): groups
  of 40 bits, whose five bytes each TBL picks, as for `d = 10` (`ce5Body`).
  For `d = 11` lanes are paired once and the words paired into doublewords
  of 44 bits; the two of a register become a group of 88 bits in its 11 low
  bytes (`merge88`: SHL, EXT, ORR and INS), whose bytes TBL picks from four
  registers (`ce11Body`).
* `decodeDecompress(b = x0, len = x1, d = w2, f = x3)`: the reverse.
  `Decompress_d(y)` of a lane is `(q · y + 2ᵈ⁻¹) >> d` (`decV`). For
  `d = 5` TBL puts each group's five bytes in a doubleword, which is split
  into values of ten bits (`ddSplit`) and those into values of five
  (`dd5Quarter`: USHR, AND and ZIPs). For `d = 11` TBL puts each group's 11
  bytes in a register, whose 88 bits USHR, SHL, EXT, ORR and ZIP1 split into
  two doublewords of 44 (`dd11Group`), split into values of 11 bits
  (`ddSplit`).

The width is chosen by `len` (160 or 352 bytes), which is public: the
contracts require `len = 32 d`. Every address and branch depends only on
the pointers and `len`. The code uses `v0`–`v7` and `v16`–`v23`, none of
the registers the procedure call standard preserves.
-/

@[expose] public section

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64
open VG.Impl.MlKem.AArch64 (movImm Width dupW bytesVec ld8 cmp8 pairV dpairV ceLoop decV ddLoop ddSplit
  ce10Idx ce10IdxHi dd10Idx dd10IdxHi)

def width5 : Width := ⟨5, 8, 5, 5040, 261888⟩
def width11 : Width := ⟨11, 8, 11, 322542, 261888⟩

/-! ## `compressEncode` -/

/-- `d = 5`: 32 coefficients to 20 bytes. -/
def ce5Math : List Instr :=
  cmp8 ++ pairV 5 .v0 .v0 .v1 ++ pairV 5 .v1 .v2 .v3 ++ pairV 5 .v2 .v4 .v5 ++ pairV 5 .v3 .v6 .v7 ++
    pairV 10 .v4 .v0 .v1 ++ pairV 10 .v5 .v2 .v3 ++ dpairV 20 .v4 ++ dpairV 20 .v5 ++
    [.vop (.tblN false 2 .v6 .v4 .v20), .vop (.tblN false 2 .v7 .v4 .v21)]

def ce5Body : List Instr :=
  ld8 ++ ce5Math ++
    [.strq .v6 .x2 0, .umov .w .x9 .v7 0, .str .w .x9 .x2 16, .addImm .x .x0 .x0 128, .addImm .x .x2 .x2 20,
     .subImm .x .x11 .x11 1]

/-- The two doublewords of `v`, groups of 44 bits, as one group of 88 bits in its 11 low bytes,
through `v19` and `v23`. -/
def merge88 (v : VReg) : List Instr :=
  [.vop (.shift .ushr .d2 .v23 v 20), .vop (.shift .shl .d2 .v19 v 44), .vop (.ext .v19 .v19 .v19 8),
   .vop (.logic .orr v v .v19), .vop (.insE .d2 v 1 .v23 1)]

/-- The indices of the bytes `ce11Body` stores from the four registers of 11 bytes. -/
def ce11Idx0 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 17, 18, 19, 20]
def ce11Idx1 : List Nat := [21, 22, 23, 24, 25, 26, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
def ce11Idx2 : List Nat := [42, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]

/-- `d = 11`: 32 coefficients to 44 bytes. -/
def ce11Math : List Instr :=
  cmp8 ++ pairV 11 .v0 .v0 .v1 ++ pairV 11 .v1 .v2 .v3 ++ pairV 11 .v2 .v4 .v5 ++ pairV 11 .v3 .v6 .v7 ++
    dpairV 22 .v0 ++ dpairV 22 .v1 ++ dpairV 22 .v2 ++ dpairV 22 .v3 ++
    merge88 .v0 ++ merge88 .v1 ++ merge88 .v2 ++ merge88 .v3 ++
    [.vop (.tblN false 4 .v4 .v0 .v20), .vop (.tblN false 4 .v5 .v0 .v21),
     .vop (.tblN false 4 .v6 .v0 .v22)]

def ce11Body : List Instr :=
  ld8 ++ ce11Math ++
    [.strq .v4 .x2 0, .strq .v5 .x2 16, .umov .x .x9 .v6 0, .str .x .x9 .x2 32, .umov .w .x9 .v6 2,
     .str .w .x9 .x2 40, .addImm .x .x0 .x0 128, .addImm .x .x2 .x2 44, .subImm .x .x11 .x11 1]

def compressEncode : Prog isa :=
  .seq (.block [.subImm .x .x9 .x3 160]) <|
  .ite (.zero .x .x9) (ceLoop width5 8 (bytesVec .v20 ce10Idx ++ bytesVec .v21 ce10IdxHi) ce5Body)
    (ceLoop width11 8 (bytesVec .v20 ce11Idx0 ++ bytesVec .v21 ce11Idx1 ++ bytesVec .v22 ce11Idx2) ce11Body)

/-! ## `decodeDecompress` -/

/-- The values of ten bits in the lanes of `a` (`v2` or `v3`), split into pairs of values of five
bits, decompressed and stored as 8 coefficients at `x3 + o`, through `v0` and `v1`. `v22` holds 31
in every word. -/
def dd5Quarter (a : VReg) (o : Nat) : List Instr :=
  [.vop (.shift .ushr .s4 .v1 a 5), .vop (.logic .and a a .v22), .vop (.perm .zip1 .s4 .v0 a .v1),
   .vop (.perm .zip2 .s4 a a .v1)] ++
  decV 5 .v0 ++ decV 5 a ++ [.strq .v0 .x3 o, .strq a .x3 (o + 16)]

/-- The two groups of 40 bits in the doublewords of `g` to 16 coefficients at `x3 + o`. `v18`
holds `2²⁰ - 1` in every word, `v19` `2¹⁰ - 1`. -/
def dd5Half (g : VReg) (o : Nat) : List Instr :=
  ddSplit 10 g ++ dd5Quarter .v2 o ++ dd5Quarter .v3 (o + 32)

/-- `d = 5`: 20 bytes to 32 coefficients. -/
def dd5Body : List Instr :=
  [.ldrq .v4 .x0 0, .ldr .w .x9 .x0 16, .vop (.ins .s4 .v5 0 .x9),
   .vop (.tblN false 2 .v6 .v4 .v20), .vop (.tblN false 2 .v7 .v4 .v21)] ++
  dd5Half .v6 0 ++ dd5Half .v7 64 ++
  [.addImm .x .x0 .x0 20, .addImm .x .x3 .x3 128, .subImm .x .x11 .x11 1]

/-- The indices of the bytes of group `g` of 88 bits. -/
def dd11Idx (g : Nat) : List Nat := (List.range 11).map (11 * g + ·)

/-- The index vector of group `g`. -/
def dd11IdxReg (g : Nat) : VReg := Nat.repeat VReg.succ g .v20

/-- Group `g` of 88 bits of the input (in `v4`, `v5` and `v6`) to 8 coefficients at `x3 + 32 g`.
`v18` holds `2²² - 1` in every word, `v19` `2¹¹ - 1`. -/
def dd11Group (g : Nat) : List Instr :=
  [.vop (.tblN false 3 .v7 .v4 (dd11IdxReg g)), .vop (.shift .ushr .d2 .v1 .v7 44),
   .vop (.shift .shl .d2 .v2 .v7 20), .vop (.ext .v2 .v2 .v2 8), .vop (.logic .orr .v1 .v1 .v2),
   .vop (.perm .zip1 .d2 .v7 .v7 .v1)] ++
  ddSplit 11 .v7 ++ decV 11 .v2 ++ decV 11 .v3 ++ [.strq .v2 .x3 (32 * g), .strq .v3 .x3 (32 * g + 16)]

/-- `d = 11`: 44 bytes to 32 coefficients. -/
def dd11Body : List Instr :=
  [.ldrq .v4 .x0 0, .ldrq .v5 .x0 16, .ldr .x .x9 .x0 32, .vop (.ins .d2 .v6 0 .x9), .ldr .w .x9 .x0 40,
   .vop (.ins .s4 .v6 2 .x9)] ++
  dd11Group 0 ++ dd11Group 1 ++ dd11Group 2 ++ dd11Group 3 ++
  [.addImm .x .x0 .x0 44, .addImm .x .x3 .x3 128, .subImm .x .x11 .x11 1]

def decodeDecompress : Prog isa :=
  .seq (.block [.subImm .x .x9 .x1 160]) <|
  .ite (.zero .x .x9)
    (ddLoop 5 8 (dupW .v18 (2 ^ 20 - 1) ++ dupW .v19 1023 ++ bytesVec .v20 dd10Idx ++ bytesVec .v21 dd10IdxHi ++
      dupW .v22 31) dd5Body)
    (ddLoop 11 8 (dupW .v18 (2 ^ 22 - 1) ++ dupW .v19 2047 ++ bytesVec .v20 (dd11Idx 0) ++
      bytesVec .v21 (dd11Idx 1) ++ bytesVec .v22 (dd11Idx 2) ++ bytesVec .v23 (dd11Idx 3)) dd11Body)

end VG.Impl.MlKem1024.AArch64
