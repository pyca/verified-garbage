module

public import VerifiedGarbage.Impl.Sha512.AArch64.Stream

/-!
# One-shot SHA-512 family digests: AArch64 implementation

`digest(data = x0, len = x1, out = x2)` of a member of the SHA-512 family
with initial hash value `iv` and a `D`-byte digest, composed of the streaming
functions it calls: it keeps a streaming state, the final hash value and the
streaming functions' scratch space in a frame of its own, stores `iv` in the
state, calls `update_scratch` with the whole message, then
`finalize_scratch` (with the count `len`) into the final hash value, copies
its first `D` bytes to `out` and zeroes the state, as the Rust streaming code
zeroes its state on drop.

The frame (`frameBytes` bytes at `sp`):

* `[0, 192)`: the streaming state;
* `[192, 256)`: the final hash value;
* `[256, 256 + scratchBytes + 48)`: the scratch space of `update` and
  `finalize`;
* `data`, `len` and `out` at `argOff`, `argOff + 8` and `argOff + 16`, which
  the calls do not keep.

The return address is saved by the frame's push of `x30`. Every address and
branch depends only on `data`, `len`, `out` and `sp`.
-/

@[expose] public section

namespace VG.Impl.Sha512.AArch64.Digest

open VG.AArch64
open VG.Impl.Sha512.AArch64 (movImm64 scratchBytes)
open VG.Impl.MdStream.AArch64 (mov)

/-- Where the final hash value is in the frame. -/
def hashOff : Nat := 192

/-- Where the scratch space is in the frame. -/
def scratchOff : Nat := 256

/-- Where `data`, `len` and `out` are saved. -/
def argOff : Nat := scratchOff + scratchBytes + 48

/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := (argOff + 24 + 15) / 16 * 16

/-- Save the arguments, point `x0` at the state and store `iv` in it. -/
def setup (iv : Spec.Sha512.HashValue) : List Instr :=
  [.addSp .x10 0, .str .x .x0 .x10 argOff, .str .x .x1 .x10 (argOff + 8),
    .str .x .x2 .x10 (argOff + 16), .addSp .x0 0] ++
  (List.range 8).flatMap fun k => movImm64 .x9 iv[k]! ++ ([.str .x .x9 .x0 (8 * k)] : List Instr)

/-- `update(state, 0, data, len, scratch)`'s arguments (`x0` is the state). -/
def updArgs : List Instr :=
  [.movz .x .x1 0 0, .ldrSp .x2 argOff, .ldrSp .x3 (argOff + 8), .addSp .x4 scratchOff]

/-- `finalize(state, len, hash, scratch)`'s arguments. -/
def finArgs : List Instr :=
  [.addSp .x0 0, .ldrSp .x1 (argOff + 8), .addSp .x2 hashOff, .addSp .x3 scratchOff]

/-- Copy the first `D` bytes of the final hash value to `out`: whole
doublewords, then a word (`D = 28`). -/
def copyOut (D : Nat) : List Instr :=
  [.ldrSp .x10 (argOff + 16), .addSp .x11 hashOff] ++
  (List.range (D / 8)).flatMap (fun k => [.ldr .x .x9 .x11 (8 * k), .str .x .x9 .x10 (8 * k)]) ++
  (if D % 8 = 4 then [.ldr .w .x9 .x11 (8 * (D / 8)), .str .w .x9 .x10 (8 * (D / 8))] else [])

/-- Zero the streaming state. -/
def wipeState : List Instr :=
  [.addSp .x10 0, .movz .x .x9 0 0] ++ (List.range 24).map fun k => .str .x .x9 .x10 (8 * k)

/-- The one-shot digest, calling `update` (`updN`, `updC`) and `finalize`
(`finN`, `finC`). -/
def digest (iv : Spec.Sha512.HashValue) (D : Nat) (updN : String) (updC : Prog isa)
    (finN : String) (finC : Prog isa) : Prog isa :=
  .frame (.push .x30)
    (.frame (.alloc frameBytes)
      (.seq (.block (setup iv ++ updArgs))
      (.seq (.call updN updC)
      (.seq (.block finArgs)
      (.seq (.call finN finC)
        (.block (copyOut D ++ wipeState))))))
      (.free frameBytes))
    (.pop .x30)

end VG.Impl.Sha512.AArch64.Digest
