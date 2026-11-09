module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# The one-shot digest over any streaming hash function: PPC64LE implementation

`digest(data = r3, len = r4, out = r5, scratch = r6)` hashes the `len` bytes
at `data` with a hash function's streaming `init`, `update` and `finalize`
(`Hash`, as HMAC's code calls them, `VG.Impl.Hmac.Stream.PPC64LE`) and writes
its `D`-byte digest to `out`. Its scratch space is laid out as HMAC's
`initLong`'s (`Hash.lbytes` bytes): the working space of the functions we
call (`W` bytes, then 48 that we do not use), the streaming state (at
`lst`), what `finalize` writes (at `ldg`, `FD` bytes, of which the digest is
the first `D`), and our caller's `r20`–`r25` (at `lsv`). Across the calls,
`r20` = the streaming state, `r21` = `scratch`, `r22` = `out`, `r23` =
`data` and `r24` = `len`. The digest is copied to `out` a 32-bit word at a
time. `code` runs it in a frame of its own holding its working space, which
it zeroes before returning. Every address and branch depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Impl.MdStream.PPC64LE.Digest

open VG.PPC64LE
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.Hmac.Stream.PPC64LE.Hash (cp32)

variable (H : Hash)

/-- The digest from `scratch[ldg..)` to `out`. -/
def copyOut : List Instr := (List.range (H.D / 4)).flatMap (cp32 .r21 .r22 H.ldg 0)

/-- `digest`, but for saving the link register. -/
def digestMain : Prog isa :=
  .seq (.block (Hash.saveAt H.lsv .r6 ++
      [mov .r21 .r6, mov .r22 .r5, mov .r23 .r3, mov .r24 .r4, .addi .r20 .r6 H.lst, mov .r3 .r20]))
  (.seq H.callInit
  (.seq (.block [mov .r3 .r20, .li .r4 0, mov .r5 .r23, mov .r6 .r24, mov .r7 .r21])
  (.seq H.callUpd
  (.seq (.block [mov .r3 .r20, mov .r4 .r24, .addi .r5 .r21 H.ldg, mov .r6 .r21])
  (.seq H.callFin
    (.block (copyOut H ++ Hash.restoreAt H.lsv)))))))

/-- The one-shot digest with its working space as an argument. -/
def digest : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) (digestMain H) (.pop .r0)) (.block [.mtlr .r0]))

/-- The bytes of the frame holding the working space and its 32-byte header. -/
def frameBytes : Nat := (H.lbytes + 32 + 15) / 16 * 16

/-- `vg_<hash>_digest`: `digest` with its working space in a frame of its own,
which it zeroes before returning. -/
def code : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchWiped (frameBytes H) .r6 (H.lbytes / 8) (digest H)

end VG.Impl.MdStream.PPC64LE.Digest
