module

public import VerifiedGarbage.Impl.Sha1.RISCV64.Stream
public import VerifiedGarbage.Impl.MdStream.RISCV64.Digest
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Spec.Sha1.Contract

/-!
# SHA-1 on RISC-V, as emitted

Each streaming function, then its cleanup (`Impl.Scrub.RISCV64.scrubAll rb W`):
the zeroing of the `W` bytes of stack its frames use (none for `init`, the
144-byte frame of `update` and `finalize`), and the clearing of the
caller-saved registers, `a0` included (none returns a value), so that it
returns without secret residue.

`digest` is the generic one-shot digest (`Impl.MdStream.RISCV64.Digest`)
over SHA-1's streaming functions (`hash`), then its cleanup
(`Impl.Scrub.RISCV64.scrubSel rb fs`): the caller-saved registers cleared,
and, of the 288 bytes of stack it and its callees use, only the runs of
doublewords `fs` states, those the residue analysis (`RISCV64.rtaint`) finds
may differ between two runs: the code wipes most of its own scratch space.
-/

@[expose] public section

namespace VG.Impl.Sha1.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll scrubSel)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-- `vg_sha1_init`, as emitted. -/
def init : Prog isa := scrubAll 0 0 Stream.init

/-- `vg_sha1_update`, as emitted. -/
def update : Prog isa := scrubAll 0 144 Stream.update

/-- `vg_sha1_finalize`, as emitted. -/
def finalize : Prog isa := scrubAll 0 144 Stream.finalize

/-- SHA-1's streaming functions, as the one-shot digest calls them, under
the internal names `vg_sha1_init_core`, …: a 64-byte block, a 20-byte hash
value and digest, and 144 bytes of stack for `update` and `finalize`. -/
def hash : Hash where
  b := 6
  N := 20
  D := 20
  F := 144
  initN := Spec.Sha1.initApi.name ++ "_core"
  initC := Stream.init
  updN := Spec.Sha1.updateApi.name ++ "_core"
  updC := Stream.update
  finN := Spec.Sha1.finalizeApi.name ++ "_core"
  finC := Stream.finalize

/-- `vg_sha1_digest`, as emitted. -/
def digest : Prog isa := scrubSel 0 [(288, [(0, 18), (29, 7)])] (Impl.MdStream.RISCV64.Digest.digest hash)

end VG.Impl.Sha1.RISCV64.Fn
