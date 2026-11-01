module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Compress
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Codec

/-!
# ML-KEM-1024: the compression to 5 and 11 bits, and the key check, on PPC64LE

The primitives of `Proof/MlKem1024/Contract.lean` that go through the
coefficients once, as `Impl/MlKem/PPC64LE/Compress.lean` does for the widths
of ML-KEM-768: the fields of a group are assembled in `r8` and stored a byte
at a time, or loaded into `r8` and taken apart with pairs of shifts. Both
functions zero-extend `d` (a `u32`, public in its low word only), branch on
it, and loop with `r11` counting down; they use only volatile registers and
no stack.

A group of 8 coefficients is `d` bytes for both widths: 5 bytes (40 bits,
one doubleword) for `d = 5`, and 11 bytes (88 bits) for `d = 11`, which take
two: the low 5 bytes come from the first four coefficients (44 bits), whose
remaining 4 bits start the second doubleword of the last four (48 bits, the
6 bytes left).

* `vg_mlkem1024_compress_encode(f = r3, d = r4, out = r5, len = r6)`:
  `Compress_d(x)` is `((x · M_d + 2¹⁸ - 256) >> 19) mod 2ᵈ`
  (`VG.Proof.MlKem.compress1024_eq`), with `M_d` in `r9` and `2¹⁸ - 256` in
  `r10`; the `mod 2ᵈ` and the field's place in the doubleword are a pair of
  shifts.
* `vg_mlkem1024_decode_decompress(b = r3, len = r4, d = r5, f = r6)`:
  `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`, with `q` in `r9`.
* `vg_mlkem1024_check_ek(ek = r3)`: `vg_mlkem768_check_ek`'s loop, over the
  512 groups of three bytes of `ek[0 : 1536]`.

Every address is a pointer plus a constant, and every branch depends on a
counter or `d`: only the pointers, `d` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem1024.PPC64LE

open VG.PPC64LE
open VG.Impl.MlKem.PPC64LE (compressAt decompressTo checkEkBody)

/-! ## `ByteEncode_d ∘ Compress_d` -/

/-- `r10 = 2¹⁸ - 256`, the bias of the widths of ML-KEM-1024. -/
def biasConst1024 : List Instr := [.lis .r10 0x3, .ori .r10 .r10 0xFF00]

/-- `Compress₅` of coefficient `k` of the group, at bit `5 k` of `r8`. -/
def ce5Coeff (k : Nat) : List Instr :=
  compressAt (4 * k) ++ [.lsl .r7 .r7 59, .lsr .d .r7 .r7 (59 - 5 * k), .add .r8 .r8 .r7]

/-- The five bytes of `r8` stored at `r5`. -/
def ce5Store : List Instr :=
  [.stb .r8 .r5 0, .lsr .d .r7 .r8 8, .stb .r7 .r5 1, .lsr .d .r7 .r8 16, .stb .r7 .r5 2,
   .lsr .d .r7 .r8 24, .stb .r7 .r5 3, .lsr .d .r7 .r8 32, .stb .r7 .r5 4]

def ce5Body : List Instr :=
  [.li .r8 0] ++ ce5Coeff 0 ++ ce5Coeff 1 ++ ce5Coeff 2 ++ ce5Coeff 3 ++ ce5Coeff 4 ++ ce5Coeff 5 ++
  ce5Coeff 6 ++ ce5Coeff 7 ++ ce5Store ++
  [.addi .r3 .r3 32, .addi .r5 .r5 5, .subi .r11 .r11 1]

/-- `Compress₁₁` of coefficient `k` of the group, at bit `p` of `r8`. -/
def ce11Coeff (k p : Nat) : List Instr :=
  compressAt (4 * k) ++ [.lsl .r7 .r7 53, .lsr .d .r7 .r7 (53 - p), .add .r8 .r8 .r7]

/-- `Compress₁₁` of coefficient `k` of the group, at bit `p` of `r12`: the
last four coefficients are assembled apart from the first four, so that the
group is read before any of it is stored. -/
def ce11CoeffHi (k p : Nat) : List Instr :=
  compressAt (4 * k) ++ [.lsl .r7 .r7 53, .lsr .d .r7 .r7 (53 - p), .add .r12 .r12 .r7]

/-- The six bytes of `r8` stored at `r5 + 5`. -/
def ce11Store : List Instr :=
  [.stb .r8 .r5 5, .lsr .d .r7 .r8 8, .stb .r7 .r5 6, .lsr .d .r7 .r8 16, .stb .r7 .r5 7,
   .lsr .d .r7 .r8 24, .stb .r7 .r5 8, .lsr .d .r7 .r8 32, .stb .r7 .r5 9,
   .lsr .d .r7 .r8 40, .stb .r7 .r5 10]

def ce11Body : List Instr :=
  [.li .r8 0, .li .r12 0] ++ ce11Coeff 0 0 ++ ce11Coeff 1 11 ++ ce11Coeff 2 22 ++ ce11Coeff 3 33 ++
  ce11CoeffHi 4 4 ++ ce11CoeffHi 5 15 ++ ce11CoeffHi 6 26 ++ ce11CoeffHi 7 37 ++
  ce5Store ++ [.lsr .d .r8 .r8 40, .add .r8 .r8 .r12] ++ ce11Store ++
  [.addi .r3 .r3 32, .addi .r5 .r5 11, .subi .r11 .r11 1]

def compressEncode1024 : Prog isa :=
  .seq (.block [.rotr .w .r4 .r4 0]) (.seq (.block [.subi .r7 .r4 5])
    (.ite (.zero .w .r7)
      (.seq (.block (biasConst1024 ++ [.li .r9 5040, .li .r11 32])) (.loop (.block ce5Body) (.nonzero .d .r11)))
      (.seq (.block (biasConst1024 ++ [.lis .r9 0x4, .ori .r9 .r9 0xEBEE, .li .r11 32]))
        (.loop (.block ce11Body) (.nonzero .d .r11)))))

/-! ## `Decompress_d ∘ ByteDecode_d` -/

/-- Byte `off` of the group, added into `r8` at bit `sh`. -/
def ddByteAt (off sh : Nat) : List Instr := [.lbz .r7 .r3 off, .lsl .r7 .r7 sh, .add .r8 .r8 .r7]

/-- Byte `off` of the group, added into `r12` at bit `sh`: the last six
bytes of a group of 11-bit fields are loaded apart from the first six, so
that the group is read before any coefficient is stored. -/
def ddByteAtHi (off sh : Nat) : List Instr := [.lbz .r7 .r3 off, .lsl .r7 .r7 sh, .add .r12 .r12 .r7]

/-- The 5-bit field at bit `p` of `r8`, decompressed into coefficient `k`. -/
def dd5Field (k p : Nat) : List Instr :=
  [.lsl .r7 .r8 (59 - p), .lsr .d .r7 .r7 59] ++ decompressTo 5 (4 * k)

def dd5Body : List Instr :=
  [.lbz .r8 .r3 0] ++ ddByteAt 1 8 ++ ddByteAt 2 16 ++ ddByteAt 3 24 ++ ddByteAt 4 32 ++
  dd5Field 0 0 ++ dd5Field 1 5 ++ dd5Field 2 10 ++ dd5Field 3 15 ++ dd5Field 4 20 ++
  dd5Field 5 25 ++ dd5Field 6 30 ++ dd5Field 7 35 ++
  [.addi .r3 .r3 5, .addi .r6 .r6 32, .subi .r11 .r11 1]

/-- The 11-bit field at bit `p` of `r8`, decompressed into coefficient `k`. -/
def dd11Field (k p : Nat) : List Instr :=
  [.lsl .r7 .r8 (53 - p), .lsr .d .r7 .r7 53] ++ decompressTo 11 (4 * k)

/-- The 11-bit field at bit `p` of `r12`, decompressed into coefficient `k`. -/
def dd11FieldHi (k p : Nat) : List Instr :=
  [.lsl .r7 .r12 (53 - p), .lsr .d .r7 .r7 53] ++ decompressTo 11 (4 * k)

def dd11Body : List Instr :=
  [.lbz .r8 .r3 0] ++ ddByteAt 1 8 ++ ddByteAt 2 16 ++ ddByteAt 3 24 ++ ddByteAt 4 32 ++
  ddByteAt 5 40 ++
  [.lbz .r12 .r3 5] ++ ddByteAtHi 6 8 ++ ddByteAtHi 7 16 ++ ddByteAtHi 8 24 ++ ddByteAtHi 9 32 ++
  ddByteAtHi 10 40 ++
  dd11Field 0 0 ++ dd11Field 1 11 ++ dd11Field 2 22 ++ dd11Field 3 33 ++
  dd11FieldHi 4 4 ++ dd11FieldHi 5 15 ++ dd11FieldHi 6 26 ++ dd11FieldHi 7 37 ++
  [.addi .r3 .r3 11, .addi .r6 .r6 32, .subi .r11 .r11 1]

def decodeDecompress1024 : Prog isa :=
  .seq (.block [.rotr .w .r5 .r5 0]) (.seq (.block [.li .r9 3329, .subi .r7 .r5 5])
    (.ite (.zero .w .r7)
      (.seq (.block [.li .r11 32]) (.loop (.block dd5Body) (.nonzero .d .r11)))
      (.seq (.block [.li .r11 32]) (.loop (.block dd11Body) (.nonzero .d .r11)))))

/-! ## The encapsulation key check -/

def checkEk1024 : Prog isa :=
  .seq (.block [.li .r4 512, .li .r5 0])
    (.seq (.loop (.block checkEkBody) (.nonzero .d .r4))
      (.block [.li .r6 0, .sub .r6 .r6 .r5, .lsr .d .r6 .r6 63, .li .r3 1, .sub .r3 .r3 .r6]))

end VG.Impl.MlKem1024.PPC64LE
