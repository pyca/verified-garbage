module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# EMSA-PKCS1-v1_5 encoding on x86-64

`encode` writes EMSA-PKCS1-v1_5-ENCODE (RFC 8017 §9.2) of a hash value to
a buffer: `0x00 0x01`, the bytes `0xff` of `PS`, `0x00`, the hash's
`DigestInfo` prefix (`Spec.RsaPkcs1Sig.Hash.prefix`) and the value. It is
inlined into `vg_rsa_pkcs1_sign`, `vg_rsa_pkcs1_verify` and
`vg_rsa_pkcs1_recover`, which save their arguments before it.

Registers: the buffer in `r8`, its length `k` in `rcx`, the hash function's
number (`Hash.ofId`) in the low 32 bits of `rdx`, the hash value in `rsi`
and its length in `r9`. It returns 1 in `rax` and writes the `k` bytes of
the encoding if the number names a hash function, the value is as long as
its values and `k` is at least 11 bytes more than its `DigestInfo`; it
returns 0 and writes nothing otherwise. It writes `rax`, `rsi`, `rdi`,
`r10` and `r11`.

Everything that decides a branch (the hash function's number, the lengths)
is public; the hash value is only copied, so signing (where it is secret)
is constant time.

The buffer is written from its start, one byte at a time, through `rdi`:
`0x00 0x01`, then `k - tLen - 3` bytes `0xff` counted down in `r10`, `0x00`,
the prefix by an immediate per byte, chosen by the hash function's number
(`prefixes`), and the hash value, `hLen` bytes counted down in `r9`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86_64

open VG VG.X86_64 Spec.RsaPkcs1Sig

/-- The hash functions, in the order of their numbers (`Hash.ofId`). -/
def hashes : List Hash :=
  [.md5, .sha1, .sha224, .sha256, .sha384, .sha512, .sha512_224, .sha512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512]

/-- `c i h` if the low 32 bits of `rdx` are the number `i` of a hash function
`h` (`hashes`, from `i`), `d` if they are no such number. -/
def dispatch (c : Nat → Hash → Prog isa) (d : Prog isa) : List Hash → Nat → Prog isa
  | [], _ => d
  | h :: hs, i => .seq (.block [.alu32 .cmp .rdx (.imm (BitVec.ofNat 32 i))])
      (.ite .e (c i h) (dispatch c d hs (i + 1)))

/-- `tLen`, the length of the hash's `DigestInfo`, into `r10`, and `hLen`
into `r11`. -/
def lens (h : Hash) : Prog isa :=
  .block [.mov32 .r10 (.imm (BitVec.ofNat 32 (h.prefix.length + h.len))),
    .mov32 .r11 (.imm (BitVec.ofNat 32 h.len))]

/-- For a number that names no hash function: a `tLen` longer than every
modulus, so that the length check fails. -/
def noLens : Prog isa := .block [.mov32 .r10 (.imm 2048), .mov32 .r11 (.imm 0)]

/-- The byte `b` to `[rdi]`, and `rdi` to the next byte. -/
def putByte (b : Byte) : List Instr :=
  [.mov32 .rax (.imm (b.setWidth 32)), .store8 { base := .rdi } .rax, .alu .add .rdi (.imm 1)]

/-- The bytes `bs` from `[rdi]` on. -/
def putBytes (bs : List Byte) : List Instr := bs.flatMap putByte

/-- The hash's `DigestInfo` prefix from `[rdi]` on. -/
def prefixBytes (h : Hash) : Prog isa := .block (putBytes h.prefix)

/-- `0x00 0x01` from the start of the buffer, and `r10 := k - tLen - 3`, the
length of `PS`. -/
def head : List Instr :=
  [.mov .rdi (.reg .r8)] ++ putByte 0x00 ++ putByte 0x01 ++
    [.mov .rax (.reg .rcx), .alu .sub .rax (.reg .r10), .alu .sub .rax (.imm 3), .mov .r10 (.reg .rax),
      .mov32 .rax (.imm 0xff)]

/-- `PS`: `r10` bytes `0xff` (in `rax`). -/
def psLoop : Prog isa :=
  .loop (.block [.store8 { base := .rdi } .rax, .alu .add .rdi (.imm 1), .alu .sub .r10 (.imm 1)]) .ne

/-- The hash value: `r9` bytes from `[rsi]`. -/
def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax { base := .rsi }, .store8 { base := .rdi } .rax, .alu .add .rsi (.imm 1),
    .alu .add .rdi (.imm 1), .alu .sub .r9 (.imm 1)]) .ne

/-- The encoding, once the lengths are checked. -/
def write : Prog isa :=
  .seq (.block head) (.seq psLoop (.seq (.block (putByte 0x00))
    (.seq (dispatch (fun _ h => prefixBytes h) (.block []) hashes 0)
      (.seq copyLoop (.block [.mov32 .rax (.imm 1)])))))

/-- 0 into `rax`: the encoding fails. -/
def fail : Prog isa := .block [.mov32 .rax (.imm 0)]

/-- EMSA-PKCS1-v1_5-ENCODE to the buffer at `r8`, returning 1 in `rax`, or
0 if it fails: if the hash value's length `r9` is not `hLen` (`r11`), or
`k` (`rcx`) is less than `tLen + 11` (`r10 + 11`). -/
def encode : Prog isa :=
  .seq (dispatch (fun _ h => lens h) noLens hashes 0)
    (.seq (.block [.alu .cmp .r9 (.reg .r11)])
      (.ite .ne fail
        (.seq (.block [.mov .rax (.reg .r10), .alu .add .rax (.imm 11), .alu .cmp .rcx (.reg .rax)])
          (.ite .b fail write))))

/-- `rdx := OR of [rdi + i] ^ [rsi + i]` for `i < rcx` (at least 1), through
the index `r11`: zero exactly when the two buffers are equal. It writes
`rax`, `rdx`, `r10` and `r11`. -/
def compare : Prog isa :=
  .seq (.block [.mov32 .r11 (.imm 0), .mov32 .rdx (.imm 0)])
    (.loop (.block [.movzx8 .rax { base := .rdi, index := some .r11 },
      .movzx8 .r10 { base := .rsi, index := some .r11 }, .alu .xor .rax (.reg .r10),
      .alu .or .rdx (.reg .rax), .alu .add .r11 (.imm 1), .alu .cmp .r11 (.reg .rcx)]) .ne)

end VG.Impl.RsaPkcs1Sig.X86_64
