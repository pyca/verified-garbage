module

public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# ECDSA verification of the hash function's output on PPC64LE

`vg_ecdsa_<curve>_verify(public, digest, digest_len, sig, scratch) -> r3`
(`Instance.verifyHashContract`, `Spec/Ecdsa/Verify/Generic.lean`): in a
frame of `frameBytes` bytes on the stack (`withStackScratch`, the address of
its 80 bytes of local variable space in `r8`), the `len` bytes of the hash
that the verification of a curve takes (`Proof.Ecdsa.Verify.fixedDigest`),
then that verification, `core`, run with them in place of the hash
(`hashed`):

1. whether `digest_len < len` (`isShort`), computed without a comparison
   or the carry: with `d = digest_len - len` (modulo `2⁶⁴`), the sign bit of
   `(digest_len ⊕ d) ∧ d`, the borrow of the subtraction, as `len < 2⁶³`;
2. if not, the hash's leftmost `len` bytes copied to the buffer
   (`copyBytes`);
3. otherwise 72 zero bytes stored, and the hash copied to the `len -
   digest_len` bytes after the buffer's start (`copyLoop`, if `digest_len`
   is not zero); for a curve whose `n` has 7 bits fewer than `8 len` (`wide`,
   P-521), the `len + 1` bytes then shifted right by one bit, byte `i`
   becoming the low bit of byte `i` and the seven high bits of byte `i + 1`
   (`shiftBytes`), so that the `len` bytes are the hash's integer shifted left
   by 7 bits;
4. `core`'s arguments: `public` stays in `r3`, the buffer goes to `r4`, `sig`
   to `r5` and `scratch` to `r6`.

The hash, its length and the pointers are public, so the branches and the
loop may depend on them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE.VerifyHash

open VG.PPC64LE

/-- The buffer's bytes: at least `len + 1` (67 for P-521) and 72 (the zeros). -/
def bufBytes : Nat := 80

/-- The frame: the buffer above the frame's 32-byte header, a multiple of 16. -/
def frameBytes : Nat := 112

/-- Copy the `n` bytes at `soff(src)` to `doff(dst)`, a byte at a time,
through `tmp`. -/
def copyBytes (tmp src dst : Reg) (soff doff n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.lbz tmp src (soff + i), .stb tmp dst (doff + i)]

/-- Copy `cnt` bytes from `src` to `dst`, a byte at a time through `tmp`; `cnt`
is nonzero on entry. -/
def copyLoop (tmp src dst cnt : Reg) : Prog isa :=
  .loop (.block [.lbz tmp src 0, .stb tmp dst 0, .addi src src 1, .addi dst dst 1,
    .subi cnt cnt 1]) (.nonzero .d cnt)

/-- Byte `i` of the `len` bytes becomes the low bit of byte `i` and the seven
high bits of byte `i + 1`, through `r9` and `r10`. -/
def shiftBytes (len : Nat) : List Instr :=
  (List.range len).flatMap fun i =>
    [.lbz .r9 .r8 i, .lbz .r10 .r8 (i + 1), .lsl .r9 .r9 7, .lsr .d .r10 .r10 1, .add .r9 .r9 .r10,
      .stb .r9 .r8 i]

/-- `r12 :=` 1 if `digest_len` (`r5`) is below `len`, and 0 otherwise. -/
def isShort (len : Nat) : List Instr :=
  [.li .r11 len, .sub .r12 .r5 .r11, .logic .xor .r11 .r5 .r12, .logic .and .r12 .r11 .r12,
    .lsr .d .r12 .r12 63]

/-- Zero the 72 bytes at `r8`, from `r9` (zero). -/
def zeroBytes : List Instr := (List.range 72).flatMap fun j => [.stb .r9 .r8 j]

/-- A hash shorter than `len` bytes: zeros, the hash after `len - digest_len`
of them, and, if `wide`, the shift. -/
def short (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (.li .r9 0 :: zeroBytes ++ [.addi .r10 .r8 len, .sub .r10 .r10 .r5])) <|
  .seq (.ite (.zero .d .r5) (.block []) (copyLoop .r9 .r4 .r10 .r5)) <|
  .block (if wide then shiftBytes len else [])

/-- The `len` bytes of the hash at `r4` (`r5` bytes) in the buffer at `r8`. -/
def convert (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (isShort len)) <|
  .ite (.nonzero .d .r12) (short len wide) (.block (copyBytes .r9 .r4 .r8 0 0 len))

/-- The arguments of `core`: the buffer in `r4`, `sig` in `r5`, `scratch` in
`r6` (`mr`). -/
def args : List Instr := [.logic .or .r4 .r8 .r8, .logic .or .r5 .r6 .r6, .logic .or .r6 .r7 .r7]

/-- The conversion, then `core` with the buffer for the hash. -/
def hashed (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  .seq (convert len wide) (.seq (.block args) core)

/-- `vg_ecdsa_<curve>_verify`, with the buffer in a frame on the stack. -/
def verifyHash (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  Impl.StackScratch.PPC64LE.withStackScratch frameBytes .r8 (hashed len wide core)

end VG.Impl.Ecdsa.PPC64LE.VerifyHash
