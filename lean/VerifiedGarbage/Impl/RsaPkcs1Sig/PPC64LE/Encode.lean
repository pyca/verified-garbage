module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# EMSA-PKCS1-v1_5 encoding on PPC64LE

`encode` writes EMSA-PKCS1-v1_5-ENCODE (RFC 8017 §9.2) of a hash value to
a buffer, as on AArch64 (`Impl/RsaPkcs1Sig/AArch64/Encode.lean`): `0x00 0x01`,
the bytes `0xff` of `PS`, `0x00`, the hash's `DigestInfo` prefix
(`Spec.RsaPkcs1Sig.Hash.prefix`) and the value.

Registers: the buffer in `r4`, its length `k` in `r5`, the hash function's
number (`Hash.ofId`, a `u32` whose upper bits are unspecified) in `r6`, the
hash value in `r7` and its length in `r8`. It returns 1 in `r3` and writes the
`k` bytes of the encoding if the number names a hash function, the value is
as long as its values and `k` is at least 11 bytes more than its
`DigestInfo`; it returns 0 and writes nothing otherwise. It writes `r0`,
`r3`, `r4` and `r7` to `r11`.

Everything that decides a branch (the hash function's number, the lengths)
is public. The number is compared by subtracting it, as a word
(`cmplwi`); `k < tLen + 11` is the top bit of `k - (tLen + 11)`, both below
`2^63`.

The buffer is written from its start, one byte at a time, through `r4`:
`0x00 0x01`, then `k - tLen - 3` bytes `0xff` counted down in `r11`, `0x00`,
the prefix by an immediate per byte, chosen by the hash function's number,
and the hash value, `hLen` bytes counted down in `r8`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.PPC64LE

open VG VG.PPC64LE Spec.RsaPkcs1Sig

/-- The hash functions, in the order of their numbers (`Hash.ofId`). -/
def hashes : List Hash :=
  [.md5, .sha1, .sha224, .sha256, .sha384, .sha512, .sha512_224, .sha512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512]

/-- `c h` if `r6` is the number `i` of a hash function `h` (`hashes`, from
`i`), `d` if it is no such number; through `r9`. -/
def dispatch (c : Hash → Prog isa) (d : Prog isa) : List Hash → Nat → Prog isa
  | [], _ => d
  | h :: hs, i => .seq (.block [.subi .r9 .r6 i]) (.ite (.zero .w .r9) (c h) (dispatch c d hs (i + 1)))

/-- `tLen`, the length of the hash's `DigestInfo`, into `r9`, and `hLen`
into `r10`. -/
def lens (h : Hash) : Prog isa := .block [.li .r9 (h.prefix.length + h.len), .li .r10 h.len]

/-- For a number that names no hash function: a `tLen` longer than every
modulus, so that the length check fails. -/
def noLens : Prog isa := .block [.li .r9 2048, .li .r10 0]

/-- The byte `b` to `[r4]`, and `r4` to the next byte. -/
def putByte (b : Byte) : List Instr := [.li .r0 b.toNat, .stb .r0 .r4 0, .addi .r4 .r4 1]

/-- The bytes `bs` from `[r4]` on. -/
def putBytes (bs : List Byte) : List Instr := bs.flatMap putByte

/-- The hash's `DigestInfo` prefix from `[r4]` on. -/
def prefixBytes (h : Hash) : Prog isa := .block (putBytes h.prefix)

/-- `0x00 0x01` from the start of the buffer, `r11 := k - tLen - 3`, the
length of `PS`, and `r0 := 0xff`. -/
def head : List Instr :=
  putByte 0x00 ++ putByte 0x01 ++ [.sub .r11 .r5 .r9, .subi .r11 .r11 3, .li .r0 0xff]

/-- `r11` (at least 1) bytes `r0` from `[r4]` on. -/
def fillLoop : Prog isa :=
  .loop (.block [.stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r11 .r11 1]) (.nonzero .d .r11)

/-- `r8` (at least 1) bytes from `[r7]` to `[r4]`. -/
def copyLoop : Prog isa :=
  .loop (.block [.lbz .r0 .r7 0, .stb .r0 .r4 0, .addi .r7 .r7 1, .addi .r4 .r4 1, .subi .r8 .r8 1])
    (.nonzero .d .r8)

/-- The encoding, once the lengths are checked. -/
def write : Prog isa :=
  .seq (.block head) (.seq fillLoop (.seq (.block (putByte 0x00))
    (.seq (dispatch prefixBytes (.block []) hashes 0) (.seq copyLoop (.block [.li .r3 1])))))

/-- 0 into `r3`: the encoding fails. -/
def fail : Prog isa := .block [.li .r3 0]

/-- EMSA-PKCS1-v1_5-ENCODE to the buffer at `r4`, returning 1 in `r3`, or
0 if it fails: if the hash value's length `r8` is not `hLen` (`r10`), or
`k` (`r5`) is less than `tLen + 11` (`r9 + 11`). -/
def encode : Prog isa :=
  .seq (dispatch lens noLens hashes 0)
    (.seq (.block [.sub .r11 .r8 .r10])
      (.ite (.nonzero .d .r11) fail
        (.seq (.block [.addi .r11 .r9 11, .sub .r11 .r5 .r11, .lsr .d .r11 .r11 63])
          (.ite (.nonzero .d .r11) fail write))))

/-- `r7 := OR of [r4 + i] ^ [r5 + i]` for `i < r6` (at least 1): zero
exactly when the two buffers are equal. It writes `r4` to `r9`. -/
def compare : Prog isa :=
  .seq (.block [.li .r7 0])
    (.loop (.block [.lbz .r8 .r4 0, .lbz .r9 .r5 0, .logic .xor .r8 .r8 .r9, .logic .or .r7 .r7 .r8,
      .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r6 .r6 1]) (.nonzero .d .r6))

end VG.Impl.RsaPkcs1Sig.PPC64LE
