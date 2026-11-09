module

public import VerifiedGarbage.Impl.Pbkdf2.Stream.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# The one-shot digest over any streaming hash function: 32-bit ARM implementation

`digest(data = r0, len = r1, out = r2)` hashes the `len` bytes at `data` with
a hash function's streaming `init`, `update` and `finalize` (`Hash`, as HMAC's
and PBKDF2's code calls them, `VG.Impl.Pbkdf2.Stream.Arm`), as HMAC's `init`
hashes a long key (`Fns.hashKey`, `Impl/Pbkdf2/Whole/Arm.lean`).

Its working space, `scratch`, is a frame of its own (`dbytes` bytes), whose
address `withRegScratchWiped` passes in `r3` and which it zeroes after the
code. `scratch` holds the working space of the functions we call (`8 W`
bytes), then our caller's registers and our return address (`Hash.save`),
then the streaming state (at `stO`) and what `finalize` writes (at `dgO`),
whose first `D` bytes, the digest, are copied to `out` last. Across the calls
`r11` is `scratch`, `r4` the streaming state, `r5` `out`, `r8` `data` and
`r9` `len`. Every address and branch depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Impl.MdStream.Arm.Digest

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt copy)

variable (H : Hash)

/-- Where the streaming state is in `scratch`. -/
def stO : Nat := H.buf

/-- Where `finalize` writes in `scratch`. -/
def dgO : Nat := H.buf + H.S

/-- The bytes of `scratch` (a multiple of 8). -/
def dbytes : Nat := (H.buf + H.S + H.F + 7) / 8 * 8

/-- Our caller's registers into `scratch`, which `r11` then holds; `data`,
`len` and `out` in `r8`, `r9` and `r5`, and the streaming state's address in
`r4`. -/
def prologue : List Instr :=
  ([.mov .r12 (.reg .r3)] : List Instr) ++ H.save ++
    ([.mov .r11 (.reg .r12), .mov .r8 (.reg .r0), .mov .r9 (.reg .r1), .mov .r5 (.reg .r2)] : List Instr) ++
    scrAt .r4 (stO H)

/-- `update`'s arguments: the streaming state, the count (0), `data`, `len`
and `scratch`. -/
def updArgs : List Instr :=
  [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11), .mov .r2 (.imm 0),
    .mov .r3 (.imm 0)]

/-- `digest`, with `scratch` in `r3`. -/
def digestMain : Prog isa :=
  .seq (.block (prologue H))
  (.seq (H.callInit .r4)
  (.seq (.block updArgs)
  (.seq (.frame (.push [.r1, .r7, .r10, .r12]) (.call H.updN H.updC) (.pop .r1 16))
  (.seq (H.callFin [.mov .r0 (.reg .r4)] [.mov .r2 (.reg .r9), .mov .r3 (.imm 0)] (dgO H))
  (.seq (copy .r11 (dgO H) .r5 0 H.D)
    (.block H.restore))))))

/-- `vg_<hash>_digest`: `digestMain` with `scratch` in a frame of its own,
zeroed after it. -/
def digest : Prog isa :=
  Impl.StackScratch.Arm.withRegScratchWiped (dbytes H) .r3 (dbytes H / 4) (digestMain H)

end VG.Impl.MdStream.Arm.Digest
