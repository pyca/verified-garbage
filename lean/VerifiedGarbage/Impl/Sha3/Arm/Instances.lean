module

public import VerifiedGarbage.Impl.Sha3.Arm.Stream

/-!
# SHA-3 and SHAKE on ARMv7: the functions of each instance

Each instance's functions call the sponge's (`Stream`), with the rate (and
suffix) as constants. The sponge's functions take more arguments than fit
in `r0`–`r3`, the rest on the stack, so each allocates a frame (`.alloc`),
with the callee's stack arguments at its base, `sp`, then the return
address `lr` (which the call replaces), and, but for `update`, the callee's
working space (640 bytes) after them; stores them there (through `r12`, the
frame's base, and `lr`), sets the callee's register arguments, calls it, and
restores `lr`.

* `update rate (state = r0, pos = r1, data = r2, len = r3, scratch = [sp])`
  calls `absorb(state, rate, pos, data, len, scratch)`, and returns what it
  returns.
* `xofFinalize rate (state = r0, pos = r1)` calls `pad(state, rate, pos,
  0x1f, scratch)` (SHAKE's suffix).
* `xofSqueeze rate (state = r0, pos = r1, out = r2, outlen = r3)` calls
  `squeeze(state, rate, pos, out, outlen, scratch)`, and returns what it
  returns.
* `finalize rate len (state = r0, pos = r1, out = r2)` (SHA-3) calls
  `pad(state, rate, pos, 0x06, scratch)` (SHA-3's suffix), then
  `squeeze(state, rate, 0, out, len, scratch)`, keeping `state` and `out` in
  the frame across the first call.

Every address is `sp` or `r12` (`sp`) and an offset.
-/

@[expose] public section

namespace VG.Impl.Sha3.Arm.Instances

open VG.Arm

/-- `d = n`, for `n < 256`. -/
def li (d : Reg) (n : Nat) : Instr := .mov d (.imm (BitVec.ofNat 32 n))

/-- `absorb`'s arguments, from `update`'s, in a frame of 16 bytes: `len` and
`scratch` at `sp`, `lr` at `sp + 8`. -/
def updateArgs (rate : Nat) : List Instr :=
  [.addSp .r12 0, .str .lr .r12 8, .str .r3 .r12 0, .ldrSp .lr 16, .str .lr .r12 4,
    .mov .r3 (.reg .r2), .mov .r2 (.reg .r1), li .r1 rate]

def update (rate : Nat) : Prog isa :=
  .frame (.alloc 16)
    (.seq (.block (updateArgs rate)) <|
     .seq (.call "vg_keccak_absorb_scratch" Stream.absorb) (.block [.ldrSp .lr 8]))
    (.free 16)

/-- `pad`'s arguments, from SHAKE's `finalize`'s, in a frame of 648 bytes:
`scratch = sp + 8` at `sp`, `lr` at `sp + 4`, the working space at `sp + 8`. -/
def xofPadArgs (rate : Nat) : List Instr :=
  [.addSp .r12 0, .str .lr .r12 4, .addSp .lr 8, .str .lr .r12 0, .mov .r2 (.reg .r1), li .r1 rate,
    li .r3 0x1f]

def xofFinalize (rate : Nat) : Prog isa :=
  .frame (.alloc 648)
    (.seq (.block (xofPadArgs rate)) <|
     .seq (.call "vg_keccak_pad_scratch" Stream.pad) (.block [.ldrSp .lr 4]))
    (.free 648)

/-- `squeeze`'s arguments, from SHAKE's `squeeze`'s, in a frame of 656 bytes:
`outlen` and `scratch = sp + 16` at `sp`, `lr` at `sp + 8`, the working
space at `sp + 16`. -/
def xofSqueezeArgs (rate : Nat) : List Instr :=
  [.addSp .r12 0, .str .lr .r12 8, .str .r3 .r12 0, .addSp .lr 16, .str .lr .r12 4,
    .mov .r3 (.reg .r2), .mov .r2 (.reg .r1), li .r1 rate]

def xofSqueeze (rate : Nat) : Prog isa :=
  .frame (.alloc 656)
    (.seq (.block (xofSqueezeArgs rate)) <|
     .seq (.call "vg_keccak_squeeze_scratch" Stream.squeeze) (.block [.ldrSp .lr 8]))
    (.free 656)

/-- `pad`'s arguments, from SHA-3's `finalize`'s, in a frame of 664 bytes:
`scratch = sp + 24` at `sp`, `lr` at `sp + 8`, `state` at `sp + 12`, `out`
at `sp + 16`, the working space at `sp + 24`. -/
def finPadArgs (rate : Nat) : List Instr :=
  [.addSp .r12 0, .str .lr .r12 8, .str .r0 .r12 12, .str .r2 .r12 16, .addSp .lr 24,
    .str .lr .r12 0, .mov .r2 (.reg .r1), li .r1 rate, li .r3 0x06]

/-- `squeeze(state, rate, 0, out, len, scratch = sp + 24)`. -/
def finSqzArgs (rate len : Nat) : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 12, .ldrSp .r3 16, li .r1 rate, li .r2 0, li .lr len,
    .str .lr .r12 0, .addSp .lr 24, .str .lr .r12 4]

def finalize (rate len : Nat) : Prog isa :=
  .frame (.alloc 664)
    (.seq (.block (finPadArgs rate)) <|
     .seq (.call "vg_keccak_pad_scratch" Stream.pad) <|
     .seq (.block (finSqzArgs rate len)) <|
     .seq (.call "vg_keccak_squeeze_scratch" Stream.squeeze) (.block [.ldrSp .lr 8]))
    (.free 664)

end VG.Impl.Sha3.Arm.Instances
