module

public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
public import VerifiedGarbage.Impl.MdStream.RISCV64.Digest
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Spec.Sha512.Contract

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on RISC-V, as emitted

Each streaming function, then its cleanup (`Impl.Scrub.RISCV64.scrubAll rb W`):
the zeroing of the `W` bytes of stack its frames use (none for `init`, the
208-byte frame of `update` and `finalize`), and the clearing of the
caller-saved registers, `a0` included (none returns a value), so that it
returns without secret residue.

`digest` is the generic one-shot digest (`Impl.MdStream.RISCV64.Digest`)
over the streaming functions (`hash384`, `hash512`, …, each an instance of
`hash`), then its cleanup
(`Impl.Scrub.RISCV64.scrubSel rb fs`): the caller-saved registers cleared,
and, of the 448 bytes of stack it and its callees use, only the runs of
doublewords `fs` states, those the residue analysis (`RISCV64.rtaint`) finds
may differ between two runs: the code wipes most of its own scratch space.
-/

@[expose] public section

namespace VG.Impl.Sha512.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll scrubSel)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open Spec.Sha512 (HashValue)

/-- `vg_sha384_init`, as emitted. -/
def init384 : Prog isa := scrubAll 0 0 (Stream.initWith Spec.Sha512.H0_384)

/-- `vg_sha512_init`, as emitted. -/
def init512 : Prog isa := scrubAll 0 0 (Stream.initWith Spec.Sha512.H0_512)

/-- `vg_sha512_224_init`, as emitted. -/
def init512_224 : Prog isa := scrubAll 0 0 (Stream.initWith Spec.Sha512.H0_512_224)

/-- `vg_sha512_256_init`, as emitted. -/
def init512_256 : Prog isa := scrubAll 0 0 (Stream.initWith Spec.Sha512.H0_512_256)

/-- `vg_sha512_update`, which the family shares, as emitted. -/
def update : Prog isa := scrubAll 0 208 Stream.update

/-- `vg_sha512_finalize`, as emitted. -/
def finalize : Prog isa := scrubAll 0 208 Stream.finalize

/-- `vg_sha384_finalize`, as emitted. -/
def finalize384 : Prog isa := scrubAll 0 208 Stream.finalize384

/-- `vg_sha512_256_finalize`, as emitted. -/
def finalize512_256 : Prog isa := scrubAll 0 208 Stream.finalize512_256

/-- `vg_sha512_224_finalize`, as emitted. -/
def finalize512_224 : Prog isa := scrubAll 0 208 Stream.finalize512_224

/-- The streaming functions of the hash function with initial hash value
`iv` (whose `init` is `initN`) and a digest of `D` bytes, written by
`finC` (named `finN`), as the one-shot digest calls them: a 128-byte block,
a 64-byte hash value, and 208 bytes of stack for `update` and `finalize`. -/
def hash (iv : HashValue) (D : Nat) (initN finN : String) (finC : Prog isa) : Hash where
  b := 7
  N := 64
  D := D
  F := 208
  initN := initN
  initC := Stream.initWith iv
  updN := Spec.Sha512.updateApi.name ++ "_core"
  updC := Stream.update
  finN := finN
  finC := finC

/-- SHA-384's streaming functions. -/
def hash384 : Hash :=
  hash Spec.Sha512.H0_384 48 (Spec.Sha512.init384Api.name ++ "_core")
    (Spec.Sha512.finalize384Api.name ++ "_core") Stream.finalize384

/-- SHA-512's streaming functions. -/
def hash512 : Hash :=
  hash Spec.Sha512.H0_512 64 (Spec.Sha512.init512Api.name ++ "_core")
    (Spec.Sha512.finalizeApi.name ++ "_core") Stream.finalize

/-- SHA-512/224's streaming functions. -/
def hash512_224 : Hash :=
  hash Spec.Sha512.H0_512_224 28 (Spec.Sha512.init512_224Api.name ++ "_core")
    (Spec.Sha512.finalize512_224Api.name ++ "_core") Stream.finalize512_224

/-- SHA-512/256's streaming functions. -/
def hash512_256 : Hash :=
  hash Spec.Sha512.H0_512_256 32 (Spec.Sha512.init512_256Api.name ++ "_core")
    (Spec.Sha512.finalize512_256Api.name ++ "_core") Stream.finalize512_256

/-- The one-shot digest over `H`, as emitted. -/
def digestOf (H : Hash) : Prog isa :=
  scrubSel 0 [(448, [(0, 26), (50, 6)])] (Impl.MdStream.RISCV64.Digest.digest H)

/-- `vg_sha384_digest`, as emitted. -/
def digest384 : Prog isa := digestOf hash384

/-- `vg_sha512_digest`, as emitted. -/
def digest512 : Prog isa := digestOf hash512

/-- `vg_sha512_224_digest`, as emitted. -/
def digest512_224 : Prog isa := digestOf hash512_224

/-- `vg_sha512_256_digest`, as emitted. -/
def digest512_256 : Prog isa := digestOf hash512_256

end VG.Impl.Sha512.RISCV64.Fn
