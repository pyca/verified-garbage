module

public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# One-shot Merkle–Damgård digests: AArch64 implementation

`digest(data = x0, len = x1, out = x2)` hashes a message in memory in one
call, in a frame of its own (`frameBytes P` bytes at `sp`):

* `[0, N + B)`: a streaming state;
* `[scO, scO + so + 48)`: the scratch space of the streaming code;
* at `slO`: our caller's `x25`, `x26` and `x30`.

It saves those registers, keeps `len` in `x25` and `out` in `x26`, runs the
initial hash value's code `init` on the state, then the streaming `update`'s
body (`updateMain P`) on the whole message: every whole block is compressed
straight from `data` by a call of the compression function, and the rest is
copied into the state's buffer. It then runs the body of a streaming
`finalize` (`finalizeMain PF`, whose `PF.out` writes the digest), which pads
the buffer, compresses it and writes the digest to `out`; zeroes the state
(`StackScratch.wipe`), as the Rust streaming code does when a state is
dropped; and restores the registers.

The bodies keep our caller's `x19`–`x24` (they save and restore them) and never
write `x25`–`x28`; every address we form is `sp` plus a constant, or `out`,
in `x26`, so every address and branch depends only on `data`, `len`, `out`
and `sp`.
-/

@[expose] public section

namespace VG.Impl.MdStream.AArch64.OneShot

open VG.AArch64

variable (P : Params)

/-- Where the scratch space is in the frame, after the state. -/
def scO : Nat := P.N + P.B

/-- Where our caller's `x25`, `x26` and `x30` are saved. -/
def slO : Nat := scO P + P.so + 48

/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := (slO P + 24 + 15) / 16 * 16

/-- Save `x25`, `x26` and `x30`, keep `len` and `out`, and point `x0` at the
state for `init`, with `update`'s `data` and `len` in `x2` and `x3`. -/
def setup : List Instr :=
  [.addSp .x10 0, .str .x .x25 .x10 (slO P), .str .x .x26 .x10 (slO P + 8),
    .str .x .x30 .x10 (slO P + 16), mov .x25 .x1, mov .x26 .x2, mov .x2 .x0, mov .x3 .x1,
    .addSp .x0 0]

/-- `update(state, 0, data, len, scratch)`'s other arguments. -/
def updArgs : List Instr := [.movz .x .x1 0 0, .addSp .x4 (scO P)]

/-- `finalize(state, len, out, scratch)`'s arguments. -/
def finArgs : List Instr := [.addSp .x0 0, mov .x1 .x25, mov .x2 .x26, .addSp .x3 (scO P)]

/-- Restore `x25`, `x26` and `x30` (after `wipe`, which leaves `sp` in `x16`). -/
def restore : List Instr :=
  [.ldr .x .x25 .x16 (slO P), .ldr .x .x26 .x16 (slO P + 8), .ldr .x .x30 .x16 (slO P + 16)]

/-- Zero the state and restore `x25`, `x26` and `x30`. -/
def finish : List Instr := StackScratch.AArch64.wipe ((P.N + P.B) / 8) ++ restore P

/-- The body, inside the frame. -/
def body (PF : Params) (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (setup P))
  (.seq init
  (.seq (.seq (.block (updArgs P)) (updateMain P name code))
  (.seq (.seq (.block (finArgs P)) (finalizeMain PF name code))
    (.block (finish P)))))

/-- The one-shot digest: `init` stores the initial hash value at `x0` (using
only `x9`), `P` is the streaming parameters and `PF` those of the `finalize`
writing the digest (`P` with another `out`). -/
def digest (PF : Params) (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc (frameBytes P)) (body P PF init name code) (.free (frameBytes P))

end VG.Impl.MdStream.AArch64.OneShot
