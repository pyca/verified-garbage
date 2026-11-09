module

public import VerifiedGarbage.Impl.Md5.RISCV64.Stream
public import VerifiedGarbage.Impl.Sha1.RISCV64.Stream
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream

/-!
# The digest of a hash value on RISC-V, a function of the tables of `MdHash`

`digest out` (`digest(value = a0, out = a1)`) writes the digest of the hash
value at `value` to `out`, as the streaming `finalize` of a hash function
writes it from its final hash value (`out`, which reads the hash value at
`s1` and writes to `s3`, as a byte at a time): `s1` and `s3` are set from
the arguments, and our caller's kept in `a2` and `a3`, which `out` does not
write. It is the function 4 of a table of `MdHash` (`Spec/MdHashTable.lean`),
whose callers compress a message themselves and take its digest from the hash
value after its last block. The digest is the whole hash value's
(`digestOf`): MD5's four words little-endian, SHA-1's five and SHA-256's
eight 32-bit words big-endian, the SHA-512 family's eight 64-bit words
big-endian; a caller of a hash function with a shorter digest (SHA-224, …)
takes its first bytes.
-/

@[expose] public section

namespace VG.Impl.MdHashTable.RISCV64

open VG.RISCV64
open VG.Impl.MdStream.RISCV64 (mov)

/-- `digest(value = a0, out = a1)`, writing what `out` writes. -/
def digest (out : List Instr) : Prog isa :=
  .block ([mov .a2 .s1, mov .a3 .s3, mov .s1 .a0, mov .s3 .a1] ++ out ++ [mov .s1 .a2, mov .s3 .a3])

/-- The digest of a whole hash value: MD5's, SHA-1's, SHA-256's (and
SHA-224's), and the SHA-512 family's. -/
def outMd5 : List Instr := Impl.Md5.RISCV64.Stream.params.out
def outSha1 : List Instr := Impl.Sha1.RISCV64.Stream.params.out
def outSha256 : List Instr := (List.range 8).flatMap Impl.Sha256.RISCV64.Stream.outW
def outSha512 : List Instr := (List.range 8).flatMap Impl.Sha512.RISCV64.Stream.outW

end VG.Impl.MdHashTable.RISCV64
