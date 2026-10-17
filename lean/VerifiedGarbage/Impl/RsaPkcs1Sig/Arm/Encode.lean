module

public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# EMSA-PKCS1-v1_5 encoding on ARMv7

`encode` writes EMSA-PKCS1-v1_5-ENCODE (RFC 8017 §9.2) of a hash value to
a buffer, as on AArch64 (`Impl/RsaPkcs1Sig/AArch64/Encode.lean`):
`0x00 0x01`, the bytes `0xff` of `PS`, `0x00`, the hash's `DigestInfo`
prefix (`Spec.RsaPkcs1Sig.Hash.prefix`) and the value. It is inlined into
`vg_rsa_pkcs1_sign`, `vg_rsa_pkcs1_verify_precomputed` and
`vg_rsa_pkcs1_recover_precomputed`.

Registers: the buffer in `r0`, the hash value in `r1`, the hash function's
number (`Hash.ofId`) in `r2`, the buffer's length `k` in `r3` and the hash
value's in `lr`. It sets `r3` to 1 and writes the `k` bytes of the encoding
if the number names a hash function, the value is as long as its values and
`k` is at least 11 bytes more than its `DigestInfo`; it sets `r3` to 0 and
writes nothing otherwise. It writes `r0` to `r3` and `lr`.

The number is compared with each hash function's (`dispatch`), and each has
code of its own (`encodeH`), with its lengths and prefix as immediates: the
hash value's length is compared with `hLen`, and `k < tLen + 11` is the top
bit of `k - (tLen + 11)` (`k` is at most 1024); then `0x00 0x01`, `PS`
(`fill`, `k - tLen - 3` bytes `0xff`, at least 8), `0x00` and the prefix
from `r0`, and the hash value (`Bignum.Arm.copyBytes`). Everything that
decides a branch (the number, the lengths) is public; the hash value is
only copied, so signing (where it is secret) is constant time.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.Arm

open VG VG.Arm Spec.RsaPkcs1Sig

/-- The hash functions, in the order of their numbers (`Hash.ofId`). -/
def hashes : List Hash :=
  [.md5, .sha1, .sha224, .sha256, .sha384, .sha512, .sha512_224, .sha512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512]

/-- `tLen`, the length of the hash's `DigestInfo`. -/
def tLen (h : Hash) : Nat := h.prefix.length + h.len

/-- The encoding fails: `r3 := 0`. -/
def fail : Prog isa := .block [.mov .r3 (.imm 0)]

/-- `r3` bytes `r2` from `r0` on. -/
def fill : Prog isa :=
  .loop (.block [.strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1), .subs .r3 .r3 (.imm 1)]) .ne

/-- The bytes `bs` at `r0 + o`, `r0 + o + 1`, … -/
def putBytes : List Byte → Nat → List Instr
  | [], _ => []
  | b :: bs, o => .mov .r2 (.imm (b.setWidth 32)) :: .strb .r2 .r0 o :: putBytes bs (o + 1)

/-- `0x00 0x01` at `r0`, `r0` after them, `r3 := k - tLen - 3`, the length
of `PS`, and `r2 := 0xff`. -/
def head (h : Hash) : List Instr :=
  [.mov .r2 (.imm 0), .strb .r2 .r0 0, .mov .r2 (.imm 1), .strb .r2 .r0 1, .dp .add .r0 .r0 (.imm 2),
    .dp .sub .r3 .r3 (.imm (BitVec.ofNat 32 (tLen h + 3))), .mov .r2 (.imm 0xff)]

/-- `0x00` and the prefix after `PS`, `r0` after them and `lr := hLen`. -/
def mid (h : Hash) : List Instr :=
  putBytes (0 :: h.prefix) 0 ++
    ([.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (h.prefix.length + 1))), .mov .lr (.imm (BitVec.ofNat 32 h.len))] :
      List Instr)

/-- The encoding, once the lengths are checked. -/
def write (h : Hash) : Prog isa :=
  .seq (.block (head h)) (.seq fill (.seq (.block (mid h)) (.seq Bignum.Arm.copyBytes
    (.block [.mov .r3 (.imm 1)]))))

/-- The encoding with the hash function `h`: the checks of the lengths, then
`write`. -/
def encodeH (h : Hash) : Prog isa :=
  .seq (.block [.cmp .lr (.imm (BitVec.ofNat 32 h.len))])
    (.ite .ne fail (.seq (.block [.dp .sub .r2 .r3 (.imm (BitVec.ofNat 32 (tLen h + 11))),
      .mov .r2 (.shifted .r2 .lsr 31), .cmp .r2 (.imm 0)]) (.ite .ne fail (write h))))

/-- `encodeH h` for the hash function `h` whose number is `r2`, among `hs`
from the number `i`; `fail` if none. -/
def dispatch : List Hash → Nat → Prog isa
  | [], _ => fail
  | h :: hs, i => .seq (.block [.cmp .r2 (.imm (BitVec.ofNat 32 i))]) (.ite .eq (encodeH h) (dispatch hs (i + 1)))

/-- EMSA-PKCS1-v1_5-ENCODE to the buffer at `r0`. -/
def encode : Prog isa := dispatch hashes 0

end VG.Impl.RsaPkcs1Sig.Arm
