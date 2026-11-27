module

public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
public import VerifiedGarbage.Impl.MdStream.RISCV64.Digest
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Spec.Sha256.Contract

/-!
# SHA-224 and SHA-256 on RISC-V, as emitted

Each streaming function, then its cleanup (`Impl.Scrub.RISCV64.scrubAll rb W`):
the zeroing of the `W` bytes of stack its frames use (none for `init`, the
144-byte frame of `update` and `finalize`), and the clearing of the
caller-saved registers, `a0` included (none returns a value), so that it
returns without secret residue.

`digest` is the generic one-shot digest (`Impl.MdStream.RISCV64.Digest`)
over the streaming functions (`hash256`, `hash224`), then its cleanup
(`Impl.Scrub.RISCV64.scrubSel rb fs`): the caller-saved registers cleared,
and, of the 288 bytes of stack it and its callees use, only the runs of
doublewords `fs` states, those the residue analysis (`RISCV64.rtaint`) finds
may differ between two runs: the code wipes most of its own scratch space.
-/

@[expose] public section

namespace VG.Impl.Sha256.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll scrubSel)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-- `vg_sha256_init`, as emitted. -/
def init : Prog isa := scrubAll 0 0 Stream.init

/-- `vg_sha224_init`, as emitted. -/
def init224 : Prog isa := scrubAll 0 0 Stream.init224

/-- `vg_sha256_update`, which SHA-224 shares, as emitted. -/
def update : Prog isa := scrubAll 0 144 Stream.update

/-- `vg_sha256_finalize`, as emitted. -/
def finalize : Prog isa := scrubAll 0 144 Stream.finalize

/-- `vg_sha224_finalize`, as emitted. -/
def finalize224 : Prog isa := scrubAll 0 144 Stream.finalize224

/-- SHA-256's streaming functions, as the one-shot digest calls them, under
the internal names `vg_sha256_init_core`, …: a 64-byte block, a 32-byte hash
value and digest, and 144 bytes of stack for `update` and `finalize`. -/
def hash256 : Hash where
  b := 6
  N := 32
  D := 32
  F := 144
  initN := Spec.Sha256.initApi.name ++ "_core"
  initC := Stream.init
  updN := Spec.Sha256.updateApi.name ++ "_core"
  updC := Stream.update
  finN := Spec.Sha256.finalizeApi.name ++ "_core"
  finC := Stream.finalize

/-- SHA-224's: its own `init` and `finalize`, and SHA-256's `update`, with a
28-byte digest. -/
def hash224 : Hash where
  b := 6
  N := 32
  D := 28
  F := 144
  initN := Spec.Sha256.init224Api.name ++ "_core"
  initC := Stream.init224
  updN := Spec.Sha256.updateApi.name ++ "_core"
  updC := Stream.update
  finN := Spec.Sha256.finalize224Api.name ++ "_core"
  finC := Stream.finalize224

/-- `vg_sha256_digest`, as emitted. -/
def digest : Prog isa := scrubSel 0 [(288, [(0, 18), (30, 6)])] (Impl.MdStream.RISCV64.Digest.digest hash256)

/-- `vg_sha224_digest`, as emitted. -/
def digest224 : Prog isa := scrubSel 0 [(288, [(0, 18), (30, 6)])] (Impl.MdStream.RISCV64.Digest.digest hash224)

end VG.Impl.Sha256.RISCV64.Fn
