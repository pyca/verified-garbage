module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Compress
public import VerifiedGarbage.Impl.MlKem.RISCV64.Codec

/-!
# ML-KEM-1024: the compression to 5 and 11 bits, and the key check, on RISC-V

As on PPC64LE (`Impl/MlKem1024/PPC64LE/Poly.lean`): the primitives of
`Proof/MlKem1024/Contract.lean` that go through the coefficients once, as
`Impl/MlKem/RISCV64/Compress.lean` does for the widths of ML-KEM-768: the
fields of a group are assembled in `a5` and stored a byte at a time, or
loaded into `a5` and taken apart with pairs of shifts. Both functions
zero-extend `d` (a `u32`, public in its low word only), branch on it, and
loop with `t1` counting down; they use only registers the calling
convention lets them clobber and no stack.

A group of 8 coefficients is `d` bytes for both widths: 5 bytes (40 bits,
one doubleword) for `d = 5`, and 11 bytes (88 bits) for `d = 11`, which take
two: the low 5 bytes come from the first four coefficients (44 bits), whose
remaining 4 bits start the second doubleword of the last four (48 bits, the
6 bytes left), assembled in `t2`.

* `vg_mlkem1024_compress_encode(f = a0, d = a1, out = a2, len = a3)`:
  `Compress_d(x)` is `((x · M_d + 2¹⁸ - 256) >> 19) mod 2ᵈ`
  (`VG.Proof.MlKem.compress1024_eq`), with `M_d` in `a6` and `2¹⁸ - 256` in
  `a7`; the `mod 2ᵈ` and the field's place in the doubleword are a pair of
  shifts.
* `vg_mlkem1024_decode_decompress(b = a0, len = a1, d = a2, f = a3)`:
  `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`, with `q` in `a6`.
* `vg_mlkem1024_check_ek(ek = a0)`: `vg_mlkem768_check_ek`'s loop, over the
  512 groups of three bytes of `ek[0 : 1536]`.

Every address is a pointer plus a constant, and every branch depends on a
counter or `d`: only the pointers, `d` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem1024.RISCV64

open VG.RISCV64
open VG.Impl.MlKem.RISCV64 (compressAt decompressTo checkEkBody zext32 liq)

/-! ## `ByteEncode_d ∘ Compress_d` -/

/-- `a7 = 2¹⁸ - 256`, the bias of the widths of ML-KEM-1024. -/
def biasConst1024 : List Instr := [.lui .a7 0x40, .addi .a7 .a7 (-256)]

/-- `Compress₅` of coefficient `k` of the group, at bit `5 k` of `a5`. -/
def ce5Coeff (k : Nat) : List Instr :=
  compressAt (4 * k) ++ [.shift .sll .d .a4 .a4 59, .shift .srl .d .a4 .a4 (59 - 5 * k), .add .a5 .a5 .a4]

/-- The five bytes of `a5` stored at `a2`. -/
def ce5Store : List Instr :=
  [.store .b .a5 .a2 0, .shift .srl .d .a4 .a5 8, .store .b .a4 .a2 1, .shift .srl .d .a4 .a5 16,
   .store .b .a4 .a2 2, .shift .srl .d .a4 .a5 24, .store .b .a4 .a2 3, .shift .srl .d .a4 .a5 32,
   .store .b .a4 .a2 4]

def ce5Body : List Instr :=
  [.li .a5 0] ++ ce5Coeff 0 ++ ce5Coeff 1 ++ ce5Coeff 2 ++ ce5Coeff 3 ++ ce5Coeff 4 ++ ce5Coeff 5 ++
  ce5Coeff 6 ++ ce5Coeff 7 ++ ce5Store ++
  [.addi .a0 .a0 32, .addi .a2 .a2 5, .addi .t1 .t1 (-1)]

/-- `Compress₁₁` of coefficient `k` of the group, at bit `p` of `a5`. -/
def ce11Coeff (k p : Nat) : List Instr :=
  compressAt (4 * k) ++ [.shift .sll .d .a4 .a4 53, .shift .srl .d .a4 .a4 (53 - p), .add .a5 .a5 .a4]

/-- `Compress₁₁` of coefficient `k` of the group, at bit `p` of `t2`: the
last four coefficients are assembled apart from the first four, so that the
group is read before any of it is stored. -/
def ce11CoeffHi (k p : Nat) : List Instr :=
  compressAt (4 * k) ++ [.shift .sll .d .a4 .a4 53, .shift .srl .d .a4 .a4 (53 - p), .add .t2 .t2 .a4]

/-- The six bytes of `a5` stored at `a2 + 5`. -/
def ce11Store : List Instr :=
  [.store .b .a5 .a2 5, .shift .srl .d .a4 .a5 8, .store .b .a4 .a2 6, .shift .srl .d .a4 .a5 16,
   .store .b .a4 .a2 7, .shift .srl .d .a4 .a5 24, .store .b .a4 .a2 8, .shift .srl .d .a4 .a5 32,
   .store .b .a4 .a2 9, .shift .srl .d .a4 .a5 40, .store .b .a4 .a2 10]

def ce11Body : List Instr :=
  [.li .a5 0, .li .t2 0] ++ ce11Coeff 0 0 ++ ce11Coeff 1 11 ++ ce11Coeff 2 22 ++ ce11Coeff 3 33 ++
  ce11CoeffHi 4 4 ++ ce11CoeffHi 5 15 ++ ce11CoeffHi 6 26 ++ ce11CoeffHi 7 37 ++
  ce5Store ++ [.shift .srl .d .a5 .a5 40, .add .a5 .a5 .t2] ++ ce11Store ++
  [.addi .a0 .a0 32, .addi .a2 .a2 11, .addi .t1 .t1 (-1)]

def compressEncode1024 : Prog isa :=
  .seq (.block (zext32 .a1)) (.seq (.block [.addi .a4 .a1 (-5)])
    (.ite (.zero .a4)
      (.seq (.block (biasConst1024 ++ liq .a6 5040 ++ [.li .t1 32])) (.loop (.block ce5Body) (.nonzero .t1)))
      (.seq (.block (biasConst1024 ++ [.lui .a6 0x4F, .addi .a6 .a6 (-1042), .li .t1 32]))
        (.loop (.block ce11Body) (.nonzero .t1)))))

/-! ## `Decompress_d ∘ ByteDecode_d` -/

/-- Byte `off` of the group, added into `a5` at bit `sh`. -/
def ddByteAt (off sh : Nat) : List Instr := [.load .b .a4 .a0 off, .shift .sll .d .a4 .a4 sh, .add .a5 .a5 .a4]

/-- Byte `off` of the group, added into `t2` at bit `sh`: the last six
bytes of a group of 11-bit fields are loaded apart from the first six, so
that the group is read before any coefficient is stored. -/
def ddByteAtHi (off sh : Nat) : List Instr := [.load .b .a4 .a0 off, .shift .sll .d .a4 .a4 sh, .add .t2 .t2 .a4]

/-- The 5-bit field at bit `p` of `a5`, decompressed into coefficient `k`. -/
def dd5Field (k p : Nat) : List Instr :=
  [.shift .sll .d .a4 .a5 (59 - p), .shift .srl .d .a4 .a4 59] ++ decompressTo 5 (4 * k)

def dd5Body : List Instr :=
  [.load .b .a5 .a0 0] ++ ddByteAt 1 8 ++ ddByteAt 2 16 ++ ddByteAt 3 24 ++ ddByteAt 4 32 ++
  dd5Field 0 0 ++ dd5Field 1 5 ++ dd5Field 2 10 ++ dd5Field 3 15 ++ dd5Field 4 20 ++
  dd5Field 5 25 ++ dd5Field 6 30 ++ dd5Field 7 35 ++
  [.addi .a0 .a0 5, .addi .a3 .a3 32, .addi .t1 .t1 (-1)]

/-- The 11-bit field at bit `p` of `a5`, decompressed into coefficient `k`. -/
def dd11Field (k p : Nat) : List Instr :=
  [.shift .sll .d .a4 .a5 (53 - p), .shift .srl .d .a4 .a4 53] ++ decompressTo 11 (4 * k)

/-- The 11-bit field at bit `p` of `t2`, decompressed into coefficient `k`. -/
def dd11FieldHi (k p : Nat) : List Instr :=
  [.shift .sll .d .a4 .t2 (53 - p), .shift .srl .d .a4 .a4 53] ++ decompressTo 11 (4 * k)

def dd11Body : List Instr :=
  [.load .b .a5 .a0 0] ++ ddByteAt 1 8 ++ ddByteAt 2 16 ++ ddByteAt 3 24 ++ ddByteAt 4 32 ++
  ddByteAt 5 40 ++
  [.load .b .t2 .a0 5] ++ ddByteAtHi 6 8 ++ ddByteAtHi 7 16 ++ ddByteAtHi 8 24 ++ ddByteAtHi 9 32 ++
  ddByteAtHi 10 40 ++
  dd11Field 0 0 ++ dd11Field 1 11 ++ dd11Field 2 22 ++ dd11Field 3 33 ++
  dd11FieldHi 4 4 ++ dd11FieldHi 5 15 ++ dd11FieldHi 6 26 ++ dd11FieldHi 7 37 ++
  [.addi .a0 .a0 11, .addi .a3 .a3 32, .addi .t1 .t1 (-1)]

def decodeDecompress1024 : Prog isa :=
  .seq (.block (zext32 .a2)) (.seq (.block (liq .a6 3329 ++ [.addi .a4 .a2 (-5)]))
    (.ite (.zero .a4)
      (.seq (.block [.li .t1 32]) (.loop (.block dd5Body) (.nonzero .t1)))
      (.seq (.block [.li .t1 32]) (.loop (.block dd11Body) (.nonzero .t1)))))

/-! ## The encapsulation key check -/

def checkEk1024 : Prog isa :=
  .seq (.block ([.li .a1 512, .li .a2 0] ++ liq .a5 3328))
    (.seq (.loop (.block checkEkBody) (.nonzero .a1))
      (.block [.li .a3 0, .sub .a3 .a3 .a2, .shift .srl .d .a3 .a3 63, .li .a0 1, .sub .a0 .a0 .a3]))

end VG.Impl.MlKem1024.RISCV64
