module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul
public import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# EMSA-PKCS1-v1_5 encoding on RISC-V

`encode` writes EMSA-PKCS1-v1_5-ENCODE (RFC 8017 §9.2) of a hash value to
a buffer, as on PPC64LE (`Impl/RsaPkcs1Sig/PPC64LE/Encode.lean`): `0x00 0x01`,
the bytes `0xff` of `PS`, `0x00`, the hash's `DigestInfo` prefix
(`Spec.RsaPkcs1Sig.Hash.prefix`) and the value.

Registers: the buffer in `a1`, its length `k` in `a2`, the hash function's
number (`Hash.ofId`, zero-extended) in `a3`, the hash value in `a4` and its
length in `a5`. It returns 1 in `a0` and writes the `k` bytes of the
encoding if the number names a hash function, the value is as long as its
values and `k` is at least 11 bytes more than its `DigestInfo`; it returns 0
and writes nothing otherwise. It writes `a0`, `a1`, `a4`, `a5` and `t0`,
`t3`–`t5`.

Everything that decides a branch (the hash function's number, the lengths)
is public. `k < tLen + 11` is the top bit of `k - (tLen + 11)`, both below
`2^63`.

The buffer is written from its start, one byte at a time, through `a1`:
`0x00 0x01`, then `k - tLen - 3` bytes `0xff` counted down in `t5`, `0x00`,
the prefix by an immediate per byte, chosen by the hash function's number,
and the hash value, `hLen` bytes counted down in `a5`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.RISCV64

open VG VG.RISCV64 Spec.RsaPkcs1Sig
open VG.Impl.Bignum.RISCV64 (countLoop)

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The hash functions, in the order of their numbers (`Hash.ofId`). -/
def hashes : List Hash :=
  [.md5, .sha1, .sha224, .sha256, .sha384, .sha512, .sha512_224, .sha512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512]

/-- `c h` if `a3` is the number `i` of a hash function `h` (`hashes`, from
`i`), `d` if it is no such number; through `t3`. -/
def dispatch (c : Hash → Prog isa) (d : Prog isa) : List Hash → Nat → Prog isa
  | [], _ => d
  | h :: hs, i => .seq (.block [.addi .t3 .a3 (-(i : Int))]) (.ite (.zero .t3) (c h) (dispatch c d hs (i + 1)))

/-- `tLen`, the length of the hash's `DigestInfo`, into `t3`, and `hLen`
into `t4`. -/
def lens (h : Hash) : Prog isa := .block [.li .t3 (h.prefix.length + h.len), .li .t4 h.len]

/-- For a number that names no hash function: a `tLen` longer than every
modulus, so that the length check fails. -/
def noLens : Prog isa := .block [.li .t3 2047, .li .t4 0]

/-- The byte `b` to `[a1]`, and `a1` to the next byte. -/
def putByte (b : Byte) : List Instr := [.li .t0 b.toNat, .store .b .t0 .a1 0, .addi .a1 .a1 1]

/-- The bytes `bs` from `[a1]` on. -/
def putBytes (bs : List Byte) : List Instr := bs.flatMap putByte

/-- The hash's `DigestInfo` prefix from `[a1]` on. -/
def prefixBytes (h : Hash) : Prog isa := .block (putBytes h.prefix)

/-- `0x00 0x01` from the start of the buffer, `t5 := k - tLen - 3`, the
length of `PS`, and `t0 := 0xff`. -/
def head : List Instr :=
  putByte 0x00 ++ putByte 0x01 ++ [.sub .t5 .a2 .t3, .addi .t5 .t5 (-3), .li .t0 0xff]

/-- `t5` (at least 1) bytes `t0` from `[a1]` on. -/
def fillLoop : Prog isa := countLoop .t5 [.store .b .t0 .a1 0, .addi .a1 .a1 1]

/-- `a5` (at least 1) bytes from `[a4]` to `[a1]`. -/
def copyLoop : Prog isa :=
  countLoop .a5 [.load .b .t0 .a4 0, .store .b .t0 .a1 0, .addi .a4 .a4 1, .addi .a1 .a1 1]

/-- The encoding, once the lengths are checked. -/
def write : Prog isa :=
  .seq (.block head) (.seq fillLoop (.seq (.block (putByte 0x00))
    (.seq (dispatch prefixBytes (.block []) hashes 0) (.seq copyLoop (.block [.li .a0 1])))))

/-- 0 into `a0`: the encoding fails. -/
def fail : Prog isa := .block [.li .a0 0]

/-- EMSA-PKCS1-v1_5-ENCODE to the buffer at `a1`, returning 1 in `a0`, or
0 if it fails: if the hash value's length `a5` is not `hLen` (`t4`), or
`k` (`a2`) is less than `tLen + 11` (`t3 + 11`). -/
def encode : Prog isa :=
  .seq (dispatch lens noLens hashes 0)
    (.seq (.block [.sub .t5 .a5 .t4])
      (.ite (.nonzero .t5) fail
        (.seq (.block [.addi .t5 .t3 11, .sub .t5 .a2 .t5, .shift .srl .d .t5 .t5 63])
          (.ite (.nonzero .t5) fail write))))

/-- `t4 := OR of [a1 + i] ^ [a2 + i]` for `i < a3` (at least 1): zero
exactly when the two buffers are equal. It writes `a1`–`a3`, `t0` and
`t1`. -/
def compare : Prog isa :=
  .seq (.block [.li .t4 0])
    (countLoop .a3 [.load .b .t0 .a1 0, .load .b .t1 .a2 0, .logic .xor .t0 .t0 .t1, .logic .or .t4 .t4 .t0,
      .addi .a1 .a1 1, .addi .a2 .a2 1])

end VG.Impl.RsaPkcs1Sig.RISCV64
