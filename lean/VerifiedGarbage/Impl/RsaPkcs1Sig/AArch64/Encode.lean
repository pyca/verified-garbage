module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# EMSA-PKCS1-v1_5 encoding on AArch64

`encode` writes EMSA-PKCS1-v1_5-ENCODE (RFC 8017 §9.2) of a hash value to
a buffer, as on x86-64 (`Impl/RsaPkcs1Sig/X86_64/Encode.lean`): `0x00 0x01`,
the bytes `0xff` of `PS`, `0x00`, the hash's `DigestInfo` prefix
(`Spec.RsaPkcs1Sig.Hash.prefix`) and the value. It is inlined into
`vg_rsa_pkcs1_sign`, `vg_rsa_pkcs1_verify` and `vg_rsa_pkcs1_recover`.

Registers: the buffer in `x8`, its length `k` in `x9`, the hash function's
number (`Hash.ofId`) in `w10`, the hash value in `x11` and its length in
`x12`. It returns 1 in `x0` and writes the `k` bytes of the encoding if the
number names a hash function, the value is as long as its values and `k` is
at least 11 bytes more than its `DigestInfo`; it returns 0 and writes nothing
otherwise. It writes `x0` and `x11` to `x15`.

Everything that decides a branch (the hash function's number, the lengths)
is public; the hash value is only copied, so signing (where it is secret)
is constant time. The branches are on registers (`cbz`, `cbnz`): the
number is compared by subtracting it, and `k < tLen + 11` is the top bit of
`k - (tLen + 11)`, both below `2^63`.

The buffer is written from its start, one byte at a time, through `x14`:
`0x00 0x01`, then `k - tLen - 3` bytes `0xff` counted down in `x13`, `0x00`,
the prefix by an immediate per byte, chosen by the hash function's number
(`prefixes`), and the hash value, `hLen` bytes counted down in `x12`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.AArch64

open VG VG.AArch64 Spec.RsaPkcs1Sig

/-- The hash functions, in the order of their numbers (`Hash.ofId`). -/
def hashes : List Hash :=
  [.md5, .sha1, .sha224, .sha256, .sha384, .sha512, .sha512_224, .sha512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512]

/-- `c i h` if `w10` is the number `i` of a hash function `h` (`hashes`,
from `i`), `d` if it is no such number; through `t`. -/
def dispatch (t : Reg) (c : Nat → Hash → Prog isa) (d : Prog isa) : List Hash → Nat → Prog isa
  | [], _ => d
  | h :: hs, i => .seq (.block [.subImm .w t .x10 i])
      (.ite (.zero .w t) (c i h) (dispatch t c d hs (i + 1)))

/-- `tLen`, the length of the hash's `DigestInfo`, into `x13`, and `hLen`
into `x15`. -/
def lens (h : Hash) : Prog isa :=
  .block [.movz .x .x13 (BitVec.ofNat 16 (h.prefix.length + h.len)) 0,
    .movz .x .x15 (BitVec.ofNat 16 h.len) 0]

/-- For a number that names no hash function: a `tLen` longer than every
modulus, so that the length check fails. -/
def noLens : Prog isa := .block [.movz .x .x13 2048 0, .movz .x .x15 0 0]

/-- The byte `b` to `[x14]`, and `x14` to the next byte. -/
def putByte (b : Byte) : List Instr :=
  [.movz .x .x15 (b.setWidth 16) 0, .strb .x15 .x14 0, .addImm .x .x14 .x14 1]

/-- The bytes `bs` from `[x14]` on. -/
def putBytes (bs : List Byte) : List Instr := bs.flatMap putByte

/-- The hash's `DigestInfo` prefix from `[x14]` on. -/
def prefixBytes (h : Hash) : Prog isa := .block (putBytes h.prefix)

/-- `0x00 0x01` from the start of the buffer, and `x13 := k - tLen - 3`, the
length of `PS`, and `x15 := 0xff`. -/
def head : List Instr :=
  [.addImm .x .x14 .x8 0] ++ putByte 0x00 ++ putByte 0x01 ++
    [.sub .x .x13 .x9 .x13, .subImm .x .x13 .x13 3, .movz .x .x15 0xff 0]

/-- `PS`: `x13` bytes `x15`. -/
def psLoop : Prog isa :=
  .loop (.block [.strb .x15 .x14 0, .addImm .x .x14 .x14 1, .subImm .x .x13 .x13 1]) (.nonzero .x .x13)

/-- The hash value: `x12` bytes from `[x11]`. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .x15 .x11 0, .strb .x15 .x14 0, .addImm .x .x11 .x11 1,
    .addImm .x .x14 .x14 1, .subImm .x .x12 .x12 1]) (.nonzero .x .x12)

/-- The encoding, once the lengths are checked. -/
def write : Prog isa :=
  .seq (.block head) (.seq psLoop (.seq (.block (putByte 0x00))
    (.seq (dispatch .x0 (fun _ h => prefixBytes h) (.block []) hashes 0)
      (.seq copyLoop (.block [.movz .x .x0 1 0])))))

/-- 0 into `x0`: the encoding fails. -/
def fail : Prog isa := .block [.movz .x .x0 0 0]

/-- EMSA-PKCS1-v1_5-ENCODE to the buffer at `x8`, returning 1 in `x0`, or
0 if it fails: if the hash value's length `x12` is not `hLen` (`x15`), or
`k` (`x9`) is less than `tLen + 11` (`x13 + 11`). -/
def encode : Prog isa :=
  .seq (dispatch .x0 (fun _ h => lens h) noLens hashes 0)
    (.seq (.block [.sub .x .x0 .x12 .x15])
      (.ite (.nonzero .x .x0) fail
        (.seq (.block [.addImm .x .x0 .x13 11, .sub .x .x0 .x9 .x0, .lsr .x .x0 .x0 63])
          (.ite (.nonzero .x .x0) fail write))))

/-- `x12 := OR of [x14 + i] ^ [x15 + i]` for `i < x13` (at least 1): zero
exactly when the two buffers are equal. It writes `x10` to `x15`. -/
def compare : Prog isa :=
  .seq (.block [.movz .x .x12 0 0])
    (.loop (.block [.ldrb .x10 .x14 0, .ldrb .x11 .x15 0, .logic .eor .x .x10 .x10 .x11,
      .logic .orr .x .x12 .x12 .x10, .addImm .x .x14 .x14 1, .addImm .x .x15 .x15 1,
      .subImm .x .x13 .x13 1]) (.nonzero .x .x13))

end VG.Impl.RsaPkcs1Sig.AArch64
