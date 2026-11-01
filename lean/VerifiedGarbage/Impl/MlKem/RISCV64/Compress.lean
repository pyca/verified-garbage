module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Poly

/-!
# ML-KEM on RISC-V: `ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d`

As on PPC64LE (`Impl/MlKem/PPC64LE/Compress.lean`): each group of fields
(one byte for `d = 1` and `d = 4`, five bytes for `d = 10`) is assembled in
`a5` and stored a byte at a time, or loaded into `a5` and taken apart. Both
functions zero-extend `d` (a `u32`, public in its low word only) with a
pair of shifts first, branch on it, and loop with `t1` counting down; they
use only registers the calling convention lets them clobber and no stack.

* `vg_mlkem_compress_encode(f = a0, d = a1, out = a2, len = a3)`:
  `Compress_d(x)` is `((x · M_d + 2¹⁸ - 64) >> 19) mod 2ᵈ`
  (`VG.Proof.MlKem.compress_eq`), with `M_d` in `a6` and `2¹⁸ - 64` in
  `a7`; the `mod 2ᵈ` and the field's place in the byte are a pair of
  shifts.
* `vg_mlkem_decode_decompress(b = a0, len = a1, d = a2, f = a3)`:
  `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`, with `q` in `a6`.

Every address is a pointer plus a constant, and every branch depends on a
counter or `d`: only the pointers, `d` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64

open VG.RISCV64

/-! ## `ByteEncode_d ∘ Compress_d` -/

/-- `(x · M + 2¹⁸ - 64) >> 19` of the coefficient at `a0 + off`, into `a4`. -/
def compressAt (off : Nat) : List Instr :=
  [.load .w .a4 .a0 off, .mul .a4 .a4 .a6, .add .a4 .a4 .a7, .shift .srl .d .a4 .a4 19]

/-- `a7 = 2¹⁸ - 64`. -/
def biasConst : List Instr := [.lui .a7 0x40, .addi .a7 .a7 (-64)]

/-- `r`'s low word, zero-extended. -/
def zext32 (r : Reg) : List Instr := [.shift .sll .d r r 32, .shift .srl .d r r 32]

/-- Bit `j` of an output byte of `ByteEncode₁(Compress₁)`, added into `a5`. -/
def ce1Bit (j : Nat) : List Instr :=
  compressAt (4 * j) ++ [.shift .sll .d .a4 .a4 63, .shift .srl .d .a4 .a4 (63 - j), .add .a5 .a5 .a4]

def ce1Body : List Instr :=
  [.li .a5 0] ++ (List.range 8).flatMap ce1Bit ++
    [.store .b .a5 .a2 0, .addi .a0 .a0 32, .addi .a2 .a2 1, .addi .t1 .t1 (-1)]

def ce4Body : List Instr :=
  compressAt 0 ++ [.shift .sll .d .a4 .a4 60, .shift .srl .d .a5 .a4 60] ++
  compressAt 4 ++ [.shift .sll .d .a4 .a4 60, .shift .srl .d .a4 .a4 56, .add .a5 .a5 .a4] ++
  [.store .b .a5 .a2 0, .addi .a0 .a0 8, .addi .a2 .a2 1, .addi .t1 .t1 (-1)]

/-- `Compress₁₀` of coefficient `k` of the group, at bit `10 k` of `a5`. -/
def ce10Coeff (k : Nat) : List Instr :=
  compressAt (4 * k) ++ [.shift .sll .d .a4 .a4 54, .shift .srl .d .a4 .a4 (54 - 10 * k), .add .a5 .a5 .a4]

def ce10Body : List Instr :=
  [.li .a5 0] ++ ce10Coeff 0 ++ ce10Coeff 1 ++ ce10Coeff 2 ++ ce10Coeff 3 ++
  [.store .b .a5 .a2 0, .shift .srl .d .a4 .a5 8, .store .b .a4 .a2 1, .shift .srl .d .a4 .a5 16, .store .b .a4 .a2 2,
   .shift .srl .d .a4 .a5 24, .store .b .a4 .a2 3, .shift .srl .d .a4 .a5 32, .store .b .a4 .a2 4,
   .addi .a0 .a0 16, .addi .a2 .a2 5, .addi .t1 .t1 (-1)]

def compressEncode : Prog isa :=
  .seq (.block (zext32 .a1)) (.seq (.block [.addi .a4 .a1 (-1)])
    (.ite (.zero .a4)
      (.seq (.block (biasConst ++ [.li .a6 315, .li .t1 32])) (.loop (.block ce1Body) (.nonzero .t1)))
      (.seq (.block [.addi .a4 .a1 (-4)])
        (.ite (.zero .a4)
          (.seq (.block (biasConst ++ liq .a6 2520 ++ [.li .t1 128])) (.loop (.block ce4Body) (.nonzero .t1)))
          (.seq (.block (biasConst ++ [.lui .a6 0x27, .addi .a6 .a6 1527, .li .t1 64]))
            (.loop (.block ce10Body) (.nonzero .t1)))))))

/-! ## `Decompress_d ∘ ByteDecode_d` -/

/-- `(q · y + 2ᵈ⁻¹) >> d` of `y` in `a4`, stored at `a3 + off`. -/
def decompressTo (d off : Nat) : List Instr :=
  [.mul .a4 .a4 .a6, .addi .a4 .a4 (2 ^ (d - 1)), .shift .srl .d .a4 .a4 d, .store .w .a4 .a3 off]

/-- Coefficient `j` of a byte of `ByteDecode₁`: bit `j` of `a5`. -/
def dd1Bit (j : Nat) : List Instr := [.shift .sll .d .a4 .a5 (63 - j), .shift .srl .d .a4 .a4 63] ++ decompressTo 1 (4 * j)

def dd1Body : List Instr :=
  [.load .b .a5 .a0 0] ++ (List.range 8).flatMap dd1Bit ++ [.addi .a0 .a0 1, .addi .a3 .a3 32, .addi .t1 .t1 (-1)]

def dd4Body : List Instr :=
  [.load .b .a5 .a0 0, .shift .sll .d .a4 .a5 60, .shift .srl .d .a4 .a4 60] ++ decompressTo 4 0 ++
  [.shift .srl .d .a4 .a5 4] ++ decompressTo 4 4 ++ [.addi .a0 .a0 1, .addi .a3 .a3 8, .addi .t1 .t1 (-1)]

/-- Byte `k` of the group, added into `a5` at bit `8 k`. -/
def dd10Byte (k : Nat) : List Instr := [.load .b .a4 .a0 k, .shift .sll .d .a4 .a4 (8 * k), .add .a5 .a5 .a4]

/-- Field `k` of the group, from `a5`. -/
def dd10Field (k : Nat) : List Instr :=
  [.shift .sll .d .a4 .a5 (54 - 10 * k), .shift .srl .d .a4 .a4 54] ++ decompressTo 10 (4 * k)

def dd10Body : List Instr :=
  [.load .b .a5 .a0 0] ++ dd10Byte 1 ++ dd10Byte 2 ++ dd10Byte 3 ++ dd10Byte 4 ++
  dd10Field 0 ++ dd10Field 1 ++ dd10Field 2 ++ dd10Field 3 ++
  [.addi .a0 .a0 5, .addi .a3 .a3 16, .addi .t1 .t1 (-1)]

def decodeDecompress : Prog isa :=
  .seq (.block (zext32 .a2)) (.seq (.block (liq .a6 3329 ++ [.addi .a4 .a2 (-1)]))
    (.ite (.zero .a4)
      (.seq (.block [.li .t1 32]) (.loop (.block dd1Body) (.nonzero .t1)))
      (.seq (.block [.addi .a4 .a2 (-4)])
        (.ite (.zero .a4)
          (.seq (.block [.li .t1 128]) (.loop (.block dd4Body) (.nonzero .t1)))
          (.seq (.block [.li .t1 64]) (.loop (.block dd10Body) (.nonzero .t1)))))))

end VG.Impl.MlKem.RISCV64
