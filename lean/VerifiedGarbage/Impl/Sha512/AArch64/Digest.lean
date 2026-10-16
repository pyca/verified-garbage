module

public import VerifiedGarbage.Impl.Sha512.AArch64.Stream

/-!
# One-shot SHA-512 family digests: AArch64 implementation

`digest(data = x0, len = x1, out = x2)` of a member of the SHA-512 family,
with initial hash value `iv` and the digest its finalization parameters `P`
write (`Stream.params`, `params384`, …), in one call and one frame of its
own:

* it stores `iv` in a streaming state in the frame;
* it runs the streaming `update`'s body (`updateMain`) on the whole message:
  every whole block is compressed straight from `data`, by calling the
  compression function, and the rest is copied into the state's buffer;
* it runs the streaming `finalize`'s body (`finalizeMain` of `P`) with the
  count `len`: it pads the buffer (one or two blocks), compresses it and
  writes the digest straight to `out`;
* it zeroes the streaming state, which the Rust streaming code zeroes when
  the state is dropped.

The bodies are the streaming functions' own, inlined rather than called, so
there is one call from Rust, one frame and no copy of the state.

The frame (`frameBytes` bytes at `sp`):

* `[0, 192)`: the streaming state;
* `[192, 192 + scratchBytes + 48)`: the scratch space of the bodies (the
  compression function's, then our caller's registers);
* `data`, `len` and `out` at `argOff`, `argOff + 8` and `argOff + 16`, which
  the bodies do not keep.

The return address is saved by the frame's push of `x30`. Every address and
branch depends only on `data`, `len`, `out` and `sp`.
-/

@[expose] public section

namespace VG.Impl.Sha512.AArch64.Digest

open VG.AArch64
open VG.Impl.Sha512.AArch64 (movImm64 scratchBytes)
open VG.Impl.MdStream.AArch64 (Params updateMain finalizeMain)

/-- Where the scratch space is in the frame. -/
def scratchOff : Nat := 192

/-- Where `data`, `len` and `out` are saved. -/
def argOff : Nat := scratchOff + scratchBytes + 48

/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := (argOff + 24 + 15) / 16 * 16

/-- Save the arguments, store `iv` in the state at `sp`, and set up
`update`'s arguments: `(state, 0, data, len, scratch)`. -/
def setup (iv : Spec.Sha512.HashValue) : List Instr :=
  [.addSp .x10 0, .str .x .x0 .x10 argOff, .str .x .x1 .x10 (argOff + 8),
    .str .x .x2 .x10 (argOff + 16), mov .x3 .x1, mov .x2 .x0, .addSp .x0 0] ++
  (List.range 8).flatMap (fun k => movImm64 .x9 iv[k]! ++ ([.str .x .x9 .x0 (8 * k)] : List Instr)) ++
  [.movz .x .x1 0 0, .addSp .x4 scratchOff]
where
  mov (d n : Reg) : Instr := .addImm .x d n 0

/-- `finalize`'s arguments: `(state, len, out, scratch)`. -/
def finArgs : List Instr :=
  [.addSp .x0 0, .ldrSp .x1 (argOff + 8), .ldrSp .x2 (argOff + 16), .addSp .x3 scratchOff]

/-- Zero the streaming state. -/
def wipeState : List Instr :=
  [.addSp .x10 0, .movz .x .x9 0 0] ++ (List.range 24).map fun k => .str .x .x9 .x10 (8 * k)

/-- The one-shot digest, with the finalization parameters `P` (which write
the digest), calling the compression function `name` (`code`). -/
def digestWith (P : Params) (iv : Spec.Sha512.HashValue) (name : String) (code : Prog isa) :
    Prog isa :=
  .frame (.push .x30)
    (.frame (.alloc frameBytes)
      (.seq (.block (setup iv))
      (.seq (updateMain Stream.params name code)
      (.seq (.block finArgs)
      (.seq (finalizeMain P name code)
        (.block wipeState)))))
      (.free frameBytes))
    (.pop .x30)

end VG.Impl.Sha512.AArch64.Digest
