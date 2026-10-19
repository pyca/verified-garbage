module

public import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-KEM on AArch64: compression with encoding, and decoding with decompression

`ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d` for the widths
`d` = 1, 4 and 10 of ML-KEM-768, in vectors: a register holds four `u32`
coefficients, which each step treats alike.

* `compressEncode(f = x0, d = w1, out = x2, len = x3)`: `Compress_d(x)` of a
  lane is `((x · M_d + 262080) >> 19) mod 2ᵈ` (`M_d` in `v16`, 262080 in
  `v17`, `2ᵈ - 1` in `v18`; `cmpV`). The lanes of two registers become the
  lanes `x₂ₑ + 2ᵇ x₂ₑ₊₁` of one (`pairV`, by UZP1, UZP2, SHL and ORR), which
  repeats until a lane holds the group of coefficients one or more bytes
  encode: a byte for `d = 1` (eight coefficients, `ce1Body`) and `d = 4`
  (two, `ce4Body`), whose words UZP1 narrows to bytes; 40 bits for `d = 10`
  (four, `ce10Body`), which a doubleword gets by `ushr` and `sli`, and whose
  five bytes TBL picks.
* `decodeDecompress(b = x0, len = x1, d = w2, f = x3)`: the reverse.
  `Decompress_d(y)` of a lane is `(q · y + 2ᵈ⁻¹) >> d` (`q` in `v16`, `2ᵈ⁻¹`
  in `v17`; `decV`). For `d = 4` the nibbles of 16 bytes are split (AND,
  USHR), interleaved (ZIP1, ZIP2) and widened to words by ZIPs with zero
  (`dd4Body`); for `d = 1` each byte is broadcast (DUP), and its bit `i`
  masked in lane `i` (AND) gives a zero lane exactly when the bit is clear
  (CMEQ), which BIC turns into `0` or `1665` (`dd1Byte`); for `d = 10` TBL
  puts each group's five bytes in a doubleword, which `ushr`, TRN1, ANDs
  and ZIPs split into its four values (`dd10Half`).

The width is chosen by `len` (32, 128 or 320 bytes), which is public: the
contracts require `len = 32 d`. Every address and branch depends only on
the pointers and `len`. The code uses `v0`–`v7` and `v16`–`v23`, none of
the registers the procedure call standard preserves.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- `mov d, #v` for a 64-bit constant: a `movz` and three `movk`s. -/
def movImm (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0, .movk .x d (v.extractLsb' 16 16) 1,
   .movk .x d (v.extractLsb' 32 16) 2, .movk .x d (v.extractLsb' 48 16) 3]

/-- A width: `c` coefficients of `d` bits per group of `nb` bytes. -/
structure Width where
  d : Nat
  c : Nat
  nb : Nat
  /-- The multiplier of `Compress_d`. -/
  mul : Nat
  /-- The addend of `Compress_d`. -/
  add : Nat

def width1 : Width := ⟨1, 8, 1, 315, 262080⟩
def width4 : Width := ⟨4, 2, 1, 2520, 262080⟩
def width10 : Width := ⟨10, 4, 5, 161271, 262080⟩

/-- `c` in every word of `v`, through `x9`. -/
def dupW (v : VReg) (c : Nat) : List Instr := movImm .x9 (BitVec.ofNat 64 c) ++ [.vop (.dup .s4 v .x9)]

/-- The bytes `xs` (255 past its end) in `v`, through `x9`. -/
def bytesVec (v : VReg) (xs : List Nat) : List Instr :=
  let word (start : Nat) := (List.range 8).foldl (fun a i => a + (xs.getD (start + i) 255) * 2 ^ (8 * i)) 0
  movImm .x9 (BitVec.ofNat 64 (word 0)) ++ [.vop (.dup .d2 v .x9)] ++
    movImm .x9 (BitVec.ofNat 64 (word 8)) ++ [.vop (.ins .d2 v 1 .x9)]

/-! ## `compressEncode` -/

/-- `Compress_d` of the four lanes of `v`. -/
def cmpV (v : VReg) : List Instr :=
  [.vop (.mul v v .v16), .vop (.add .s4 v v .v17), .vop (.shift .ushr .s4 v v 19),
   .vop (.logic .and v v .v18)]

/-- The lanes of `x` and `y`, less than `2ᵇ`, paired into `d`: `x₀ + 2ᵇ x₁`, `x₂ + 2ᵇ x₃`,
`y₀ + 2ᵇ y₁`, `y₂ + 2ᵇ y₃`, through `v19`. -/
def pairV (b : Nat) (d x y : VReg) : List Instr :=
  [.vop (.perm .uzp2 .s4 .v19 x y), .vop (.perm .uzp1 .s4 d x y), .vop (.shift .shl .s4 .v19 .v19 b),
   .vop (.logic .orr d d .v19)]

/-- The words of `d`, less than `2ᵇ`, paired into its doublewords: `x₀ + 2ᵇ x₁`, `x₂ + 2ᵇ x₃`,
through `v19`. -/
def dpairV (b : Nat) (d : VReg) : List Instr :=
  [.vop (.shift .ushr .d2 .v19 d 32), .vop (.shift .sli .d2 d .v19 b)]

/-- Sixteen coefficients from `x0 + o` into `a`, `b`, `c` and `d`. -/
def ld4 (a b c d : VReg) (o : Nat) : List Instr :=
  [.ldrq a .x0 o, .ldrq b .x0 (o + 16), .ldrq c .x0 (o + 32), .ldrq d .x0 (o + 48)]

def ld8 : List Instr := ld4 .v0 .v1 .v2 .v3 0 ++ ld4 .v4 .v5 .v6 .v7 64

def cmp4 (a b c d : VReg) : List Instr := cmpV a ++ cmpV b ++ cmpV c ++ cmpV d

def cmp8 : List Instr := cmp4 .v0 .v1 .v2 .v3 ++ cmp4 .v4 .v5 .v6 .v7

/-- `d = 1`: 32 coefficients to 4 bytes. -/
def ce1Math : List Instr :=
  cmp8 ++ pairV 1 .v0 .v0 .v1 ++ pairV 1 .v1 .v2 .v3 ++ pairV 1 .v2 .v4 .v5 ++ pairV 1 .v3 .v6 .v7 ++
    pairV 2 .v0 .v0 .v1 ++ pairV 2 .v1 .v2 .v3 ++ pairV 4 .v0 .v0 .v1 ++
    [.vop (.perm .uzp1 .h8 .v0 .v0 .v0), .vop (.perm .uzp1 .b16 .v0 .v0 .v0)]

def ce1Body : List Instr :=
  ld8 ++ ce1Math ++ [.umov .w .x9 .v0 0, .str .w .x9 .x2 0, .addImm .x .x0 .x0 128, .addImm .x .x2 .x2 4,
    .subImm .x .x11 .x11 1]

/-- `d = 4`: 32 coefficients to 16 bytes. -/
def ce4Math : List Instr :=
  cmp8 ++ pairV 4 .v0 .v0 .v1 ++ pairV 4 .v1 .v2 .v3 ++ pairV 4 .v2 .v4 .v5 ++ pairV 4 .v3 .v6 .v7 ++
    [.vop (.perm .uzp1 .h8 .v0 .v0 .v1), .vop (.perm .uzp1 .h8 .v2 .v2 .v3),
     .vop (.perm .uzp1 .b16 .v0 .v0 .v2)]

def ce4Body : List Instr :=
  ld8 ++ ce4Math ++ [.strq .v0 .x2 0, .addImm .x .x0 .x0 128, .addImm .x .x2 .x2 16, .subImm .x .x11 .x11 1]

/-- The indices of the bytes `ce10Body` stores from `v4` and `v5`: the five
low bytes of each doubleword. -/
def ce10Idx : List Nat := [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 16, 17, 18, 19, 20, 24]
def ce10IdxHi : List Nat := [25, 26, 27, 28]

/-- `d = 10`: 16 coefficients to 20 bytes. -/
def ce10Math : List Instr :=
  cmp4 .v0 .v1 .v2 .v3 ++ pairV 10 .v4 .v0 .v1 ++ pairV 10 .v5 .v2 .v3 ++
    dpairV 20 .v4 ++ dpairV 20 .v5 ++
    [.vop (.tblN false 2 .v6 .v4 .v20), .vop (.tblN false 2 .v7 .v4 .v21)]

def ce10Body : List Instr :=
  ld4 .v0 .v1 .v2 .v3 0 ++ ce10Math ++
    [.strq .v6 .x2 0, .umov .w .x9 .v7 0, .str .w .x9 .x2 16, .addImm .x .x0 .x0 64, .addImm .x .x2 .x2 20,
     .subImm .x .x11 .x11 1]

/-- The constants of `cmpV` for the width `w`, the count `n` in `x11`, and `body` until it is
zero. -/
def ceLoop (w : Width) (n : Nat) (setup body : List Instr) : Prog isa :=
  .seq (.block (dupW .v16 w.mul ++ dupW .v17 w.add ++ dupW .v18 (2 ^ w.d - 1) ++ setup ++
      movImm .x11 (BitVec.ofNat 64 n)))
    (.loop (.block body) (.nonzero .x .x11))

def compressEncode : Prog isa :=
  .seq (.block [.subImm .x .x9 .x3 32]) <|
  .ite (.zero .x .x9) (ceLoop width1 8 [] ce1Body) <|
  .seq (.block [.subImm .x .x9 .x3 128]) <|
  .ite (.zero .x .x9) (ceLoop width4 8 [] ce4Body)
    (ceLoop width10 16 (bytesVec .v20 ce10Idx ++ bytesVec .v21 ce10IdxHi) ce10Body)

/-! ## `decodeDecompress` -/

/-- `Decompress_d` of the four lanes of `v`. -/
def decV (d : Nat) (v : VReg) : List Instr :=
  [.vop (.mul v v .v16), .vop (.add .s4 v v .v17), .vop (.shift .ushr .s4 v v d)]

/-- `d = 4`: 16 bytes to 32 coefficients. `v18` holds `0x0f` in every byte, `v19` zero. -/
def dd4Math : List Instr :=
  [.vop (.logic .and .v1 .v0 .v18), .vop (.shift .ushr .b16 .v2 .v0 4),
   .vop (.perm .zip1 .b16 .v0 .v1 .v2), .vop (.perm .zip2 .b16 .v1 .v1 .v2),
   .vop (.perm .zip1 .b16 .v2 .v0 .v19), .vop (.perm .zip2 .b16 .v3 .v0 .v19),
   .vop (.perm .zip1 .b16 .v4 .v1 .v19), .vop (.perm .zip2 .b16 .v5 .v1 .v19),
   .vop (.perm .zip1 .h8 .v0 .v2 .v19), .vop (.perm .zip2 .h8 .v1 .v2 .v19),
   .vop (.perm .zip1 .h8 .v2 .v3 .v19), .vop (.perm .zip2 .h8 .v3 .v3 .v19),
   .vop (.perm .zip1 .h8 .v6 .v4 .v19), .vop (.perm .zip2 .h8 .v7 .v4 .v19),
   .vop (.perm .zip1 .h8 .v20 .v5 .v19), .vop (.perm .zip2 .h8 .v21 .v5 .v19)] ++
  decV 4 .v0 ++ decV 4 .v1 ++ decV 4 .v2 ++ decV 4 .v3 ++ decV 4 .v6 ++ decV 4 .v7 ++ decV 4 .v20 ++
    decV 4 .v21

def dd4Body : List Instr :=
  .ldrq .v0 .x0 0 :: dd4Math ++
  [.strq .v0 .x3 0, .strq .v1 .x3 16, .strq .v2 .x3 32, .strq .v3 .x3 48, .strq .v6 .x3 64,
   .strq .v7 .x3 80, .strq .v20 .x3 96, .strq .v21 .x3 112,
   .addImm .x .x0 .x0 16, .addImm .x .x3 .x3 128, .subImm .x .x11 .x11 1]

/-- `d = 1`: byte `j` of `v22` to 8 coefficients at `x3 + 32 j`. `v18` holds the
words 1, 2, 4, 8, `v19` 16, 32, 64, 128, `v20` 1665 in every word and `v21` zero. -/
def dd1Byte (j : Nat) : List Instr :=
  [.vop (.dupE .b16 .v0 .v22 j), .vop (.logic .and .v1 .v0 .v18), .vop (.logic .and .v2 .v0 .v19),
   .vop (.cmeq .s4 .v1 .v1 .v21), .vop (.cmeq .s4 .v2 .v2 .v21),
   .vop (.logic .bic .v1 .v20 .v1), .vop (.logic .bic .v2 .v20 .v2),
   .strq .v1 .x3 (32 * j), .strq .v2 .x3 (32 * j + 16)]

def dd1Body : List Instr :=
  .ldrq .v22 .x0 0 :: (List.range 16).flatMap dd1Byte ++
    ([.addImm .x .x0 .x0 16, .addImm .x .x3 .x3 512, .subImm .x .x11 .x11 1] : List Instr)

/-- The indices of the bytes `dd10Body` puts in its doublewords: a group's five bytes each. -/
def dd10Idx : List Nat := [0, 1, 2, 3, 4, 255, 255, 255, 5, 6, 7, 8, 9, 255, 255, 255]
def dd10IdxHi : List Nat := [10, 11, 12, 13, 14, 255, 255, 255, 15, 16, 17, 18, 19, 255, 255, 255]

/-- The two groups of `2 b` bits in the doublewords of `g` (`b ≤ 11`) split into eight values of
`b` bits, in `v2` and `v3`, through `v1`: `v18` holds `2^(2 b) - 1` in every word, `v19` `2ᵇ - 1`. -/
def ddSplit (b : Nat) (g : VReg) : List Instr :=
  [.vop (.shift .ushr .d2 .v1 g (2 * b)), .vop (.perm .trn1 .s4 g g .v1), .vop (.logic .and g g .v18),
   .vop (.shift .ushr .s4 .v1 g b), .vop (.logic .and g g .v19),
   .vop (.perm .zip1 .s4 .v2 g .v1), .vop (.perm .zip2 .s4 .v3 g .v1)]

/-- The two groups of 40 bits in the doublewords of `g` to 8 coefficients at
`x3 + o`. `v18` holds `2²⁰ - 1` in every word, `v19` `2¹⁰ - 1`. -/
def dd10Half (g : VReg) (o : Nat) : List Instr :=
  ddSplit 10 g ++ decV 10 .v2 ++ decV 10 .v3 ++ [.strq .v2 .x3 o, .strq .v3 .x3 (o + 16)]

/-- `d = 10`: 20 bytes to 16 coefficients. -/
def dd10Body : List Instr :=
  [.ldrq .v4 .x0 0, .ldr .w .x9 .x0 16, .vop (.ins .s4 .v5 0 .x9),
   .vop (.tblN false 2 .v6 .v4 .v20), .vop (.tblN false 2 .v7 .v4 .v21)] ++
  dd10Half .v6 0 ++ dd10Half .v7 32 ++
  [.addImm .x .x0 .x0 20, .addImm .x .x3 .x3 64, .subImm .x .x11 .x11 1]

/-- The constants of `decV`, the count `n` in `x11`, and `body` until it is zero. -/
def ddLoop (d n : Nat) (setup body : List Instr) : Prog isa :=
  .seq (.block (dupW .v16 3329 ++ dupW .v17 (2 ^ (d - 1)) ++ setup ++ movImm .x11 (BitVec.ofNat 64 n)))
    (.loop (.block body) (.nonzero .x .x11))

def decodeDecompress : Prog isa :=
  .seq (.block [.subImm .x .x9 .x1 32]) <|
  .ite (.zero .x .x9)
    (ddLoop 1 2 (bytesVec .v18 [1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] ++
      bytesVec .v19 [16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] ++ dupW .v20 1665 ++
      [.vop (.movi0 .v21)]) dd1Body) <|
  .seq (.block [.subImm .x .x9 .x1 128]) <|
  .ite (.zero .x .x9)
    (ddLoop 4 8 (movImm .x9 15 ++ [.vop (.dup .b16 .v18 .x9), .vop (.movi0 .v19)]) dd4Body)
    (ddLoop 10 16 (dupW .v18 (2 ^ 20 - 1) ++ dupW .v19 1023 ++ bytesVec .v20 dd10Idx ++
      bytesVec .v21 dd10IdxHi) dd10Body)

end VG.Impl.MlKem.AArch64
