module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64

/-!
# The one-shot digest over any streaming hash function: RISC-V implementation

`digest(data = a0, len = a1, out = a2)` hashes the `len` bytes at `data` with
a hash function's streaming `init`, `update` and `finalize` (`Hash`, as HMAC's
code calls them, `VG.Impl.Hmac.Stream.RISCV64`), as HMAC's `init` hashes a
long key (`Hash.longKey`): into a streaming state at the start of a frame of
its own (`alloc`), with the digest written straight to `out`. The frame also
holds the return address and our caller's `s7`–`s11` (at `dso`); across the
calls `s8` = the frame, `s9` = `out`, `s10` = `data` and `s11` = `len`. Last,
it zeroes the streaming state, a doubleword at a time. Every address and
branch depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Impl.MdStream.RISCV64.Digest

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)

variable (H : Hash)

/-- Where we keep our caller's registers in the frame (8-byte aligned), after
the streaming state. -/
def dso : Nat := (H.S + 7) / 8 * 8

/-- The bytes of the frame (16-byte aligned). -/
def dbytes : Nat := (dso H + 48 + 15) / 16 * 16

/-- Zero the streaming state (the first `dso` bytes of the frame), a
doubleword at a time. -/
def wipe : List Instr := .li .t1 0 :: (List.range (dso H / 8)).map fun k => .store .d .t1 .s8 (8 * k)

/-- `digest`, in its frame. -/
def digestMain : Prog isa :=
  .seq (.block (Hash.saveAt (dso H) ++ [mov .s8 .t0, mov .s9 .a2, mov .s10 .a0, mov .s11 .a1, mov .a0 .s8]))
  (.seq H.callInit
  (.seq (.block [mov .a0 .s8, .li .a1 0, mov .a2 .s10, mov .a3 .s11])
  (.seq H.callUpd
  (.seq (.block [mov .a0 .s8, mov .a1 .s11, mov .a2 .s9])
  (.seq H.callFin
    (.block (wipe H ++ Hash.restoreAt (dso H))))))))

/-- `vg_<hash>_digest`. -/
def digest : Prog isa := .frame (.alloc (dbytes H)) (digestMain H) (.free (dbytes H))

end VG.Impl.MdStream.RISCV64.Digest
