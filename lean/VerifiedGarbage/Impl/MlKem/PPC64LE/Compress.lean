module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ML-KEM on PPC64LE: `ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d`

As on 32-bit ARM (`Impl/MlKem/Arm/Poly.lean`), but with the bytes built in
registers: with 64-bit registers and more of them, each group of fields
(one byte for `d = 1` and `d = 4`, five bytes for `d = 10`) is assembled in
`r8` and stored a byte at a time, or loaded into `r8` and taken apart. Both
functions zero-extend `d` (a `u32`, public in its low word only) first,
branch on it, and loop with `r11`
counting down; they use only volatile registers and no stack.

* `vg_mlkem_compress_encode(f = r3, d = r4, out = r5, len = r6)`:
  `Compress_d(x)` is `((x · M_d + 2¹⁸ - 64) >> 19) mod 2ᵈ`
  (`VG.Proof.MlKem.compress_eq`), with `M_d` in `r9` and `2¹⁸ - 64` in
  `r10`; the `mod 2ᵈ` and the field's place in the byte are a pair of
  shifts.
* `vg_mlkem_decode_decompress(b = r3, len = r4, d = r5, f = r6)`:
  `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`, with `q` in `r9`.

Every address is a pointer plus a constant, and every branch depends on a
counter or `d`: only the pointers, `d` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE

open VG.PPC64LE

/-! ## `ByteEncode_d ∘ Compress_d` -/

/-- `(x · M + 2¹⁸ - 64) >> 19` of the coefficient at `r3 + off`, into `r7`. -/
def compressAt (off : Nat) : List Instr :=
  [.load .w .r7 .r3 off, .mul .r7 .r7 .r9, .add .r7 .r7 .r10, .lsr .d .r7 .r7 19]

/-- `r10 = 2¹⁸ - 64`. -/
def biasConst : List Instr := [.lis .r10 0x3, .ori .r10 .r10 0xFFC0]

/-- Bit `j` of an output byte of `ByteEncode₁(Compress₁)`, added into `r8`. -/
def ce1Bit (j : Nat) : List Instr :=
  compressAt (4 * j) ++ [.lsl .r7 .r7 63, .lsr .d .r7 .r7 (63 - j), .add .r8 .r8 .r7]

def ce1Body : List Instr :=
  [.li .r8 0] ++ (List.range 8).flatMap ce1Bit ++
    [.stb .r8 .r5 0, .addi .r3 .r3 32, .addi .r5 .r5 1, .subi .r11 .r11 1]

def ce4Body : List Instr :=
  compressAt 0 ++ [.lsl .r7 .r7 60, .lsr .d .r8 .r7 60] ++
  compressAt 4 ++ [.lsl .r7 .r7 60, .lsr .d .r7 .r7 56, .add .r8 .r8 .r7] ++
  [.stb .r8 .r5 0, .addi .r3 .r3 8, .addi .r5 .r5 1, .subi .r11 .r11 1]

/-- `Compress₁₀` of coefficient `k` of the group, at bit `10 k` of `r8`. -/
def ce10Coeff (k : Nat) : List Instr :=
  compressAt (4 * k) ++ [.lsl .r7 .r7 54, .lsr .d .r7 .r7 (54 - 10 * k), .add .r8 .r8 .r7]

def ce10Body : List Instr :=
  [.li .r8 0] ++ ce10Coeff 0 ++ ce10Coeff 1 ++ ce10Coeff 2 ++ ce10Coeff 3 ++
  [.stb .r8 .r5 0, .lsr .d .r7 .r8 8, .stb .r7 .r5 1, .lsr .d .r7 .r8 16, .stb .r7 .r5 2,
   .lsr .d .r7 .r8 24, .stb .r7 .r5 3, .lsr .d .r7 .r8 32, .stb .r7 .r5 4,
   .addi .r3 .r3 16, .addi .r5 .r5 5, .subi .r11 .r11 1]

def compressEncode : Prog isa :=
  .seq (.block [.rotr .w .r4 .r4 0]) (.seq (.block [.subi .r7 .r4 1])
    (.ite (.zero .w .r7)
      (.seq (.block (biasConst ++ [.li .r9 315, .li .r11 32])) (.loop (.block ce1Body) (.nonzero .d .r11)))
      (.seq (.block [.subi .r7 .r4 4])
        (.ite (.zero .w .r7)
          (.seq (.block (biasConst ++ [.li .r9 2520, .li .r11 128])) (.loop (.block ce4Body) (.nonzero .d .r11)))
          (.seq (.block (biasConst ++ [.lis .r9 0x2, .ori .r9 .r9 0x75F7, .li .r11 64]))
            (.loop (.block ce10Body) (.nonzero .d .r11)))))))

/-! ## `Decompress_d ∘ ByteDecode_d` -/

/-- `(q · y + 2ᵈ⁻¹) >> d` of `y` in `r7`, stored at `r6 + off`. -/
def decompressTo (d off : Nat) : List Instr :=
  [.mul .r7 .r7 .r9, .addi .r7 .r7 (2 ^ (d - 1)), .lsr .d .r7 .r7 d, .store .w .r7 .r6 off]

/-- Coefficient `j` of a byte of `ByteDecode₁`: bit `j` of `r8`. -/
def dd1Bit (j : Nat) : List Instr := [.lsl .r7 .r8 (63 - j), .lsr .d .r7 .r7 63] ++ decompressTo 1 (4 * j)

def dd1Body : List Instr :=
  [.lbz .r8 .r3 0] ++ (List.range 8).flatMap dd1Bit ++ [.addi .r3 .r3 1, .addi .r6 .r6 32, .subi .r11 .r11 1]

def dd4Body : List Instr :=
  [.lbz .r8 .r3 0, .lsl .r7 .r8 60, .lsr .d .r7 .r7 60] ++ decompressTo 4 0 ++
  [.lsr .d .r7 .r8 4] ++ decompressTo 4 4 ++ [.addi .r3 .r3 1, .addi .r6 .r6 8, .subi .r11 .r11 1]

/-- Byte `k` of the group, added into `r8` at bit `8 k`. -/
def dd10Byte (k : Nat) : List Instr := [.lbz .r7 .r3 k, .lsl .r7 .r7 (8 * k), .add .r8 .r8 .r7]

/-- Field `k` of the group, from `r8`. -/
def dd10Field (k : Nat) : List Instr :=
  [.lsl .r7 .r8 (54 - 10 * k), .lsr .d .r7 .r7 54] ++ decompressTo 10 (4 * k)

def dd10Body : List Instr :=
  [.lbz .r8 .r3 0] ++ dd10Byte 1 ++ dd10Byte 2 ++ dd10Byte 3 ++ dd10Byte 4 ++
  dd10Field 0 ++ dd10Field 1 ++ dd10Field 2 ++ dd10Field 3 ++
  [.addi .r3 .r3 5, .addi .r6 .r6 16, .subi .r11 .r11 1]

def decodeDecompress : Prog isa :=
  .seq (.block [.rotr .w .r5 .r5 0]) (.seq (.block [.li .r9 3329, .subi .r7 .r5 1])
    (.ite (.zero .w .r7)
      (.seq (.block [.li .r11 32]) (.loop (.block dd1Body) (.nonzero .d .r11)))
      (.seq (.block [.subi .r7 .r5 4])
        (.ite (.zero .w .r7)
          (.seq (.block [.li .r11 128]) (.loop (.block dd4Body) (.nonzero .d .r11)))
          (.seq (.block [.li .r11 64]) (.loop (.block dd10Body) (.nonzero .d .r11)))))))

end VG.Impl.MlKem.PPC64LE
