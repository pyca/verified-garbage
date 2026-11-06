module

public import VerifiedGarbage.Impl.Sha3.AArch64
public import VerifiedGarbage.Impl.Sha3.AArch64.Callee
public import VerifiedGarbage.Impl.Sha3.AArch64.Stream
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# SHA-3 and SHAKE on AArch64: the functions of each instance

As on x86-64 (`Impl/Sha3/X86_64/Instances.lean`): each instance's functions
are the sponge's (`Stream`), with the permutation `c`, after a block that
moves the arguments into the registers the sponge's code takes them in and
sets the rate (and suffix) as constants.

* `update c rate (state = x0, pos = x1, data = x2, len = x3, scratch = x4)`
  runs `absorb(state, rate, pos, data, len, scratch)`.
* `xofFinalize c rate (state = x0, pos = x1)` runs `pad(state, rate, pos,
  0x1f, scratch)` (SHAKE's suffix), with its working space on the stack
  (`withStackScratch`, which passes it in `x2`).
* `xofSqueeze c rate (state = x0, pos = x1, out = x2, outlen = x3)` runs
  `squeeze(state, rate, pos, out, outlen, scratch)`, with its working space
  on the stack (passed in `x4`, then moved up with the others, as
  `update`'s).
* `finalize c rate len (state = x0, pos = x1, out = x2)` (SHA-3) calls
  `pad(state, rate, pos, 0x06, scratch)` (SHA-3's suffix), then
  `squeeze(state, rate, 0, out, len, scratch)`, with its working space on
  the stack (passed in `x3`): 640 bytes for the calls, and four more
  doublewords, where it saves `x19`–`x21`, which keep `state`, `out` and
  `scratch` across the calls, and its return address (`x30`, which each
  call replaces).
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Instances

open VG.AArch64
open VG.Impl.Sha3.AArch64 (mov Callee)

/-- `d = n`, for `n < 2 ^ 16`. -/
def li (d : Reg) (n : Nat) : Instr := .movz .x d (BitVec.ofNat 16 n) 0

/-- `update`'s arguments, moved up a register, and `rate` in `x1`. -/
def updateArgs (rate : Nat) : List Instr :=
  [mov .x5 .x4, mov .x4 .x3, mov .x3 .x2, mov .x2 .x1, li .x1 rate]

def update (c : Callee) (rate : Nat) : Prog isa := .seq (.block (updateArgs rate)) (Stream.absorbWith c)

/-- SHAKE's `finalize`'s arguments, with the working space in `x2`, moved to
`pad`'s: the working space to `x4`, `pos` to `x2`, `rate` into `x1` and
SHAKE's suffix into `x3`. -/
def xofPadArgs (rate : Nat) : List Instr := [mov .x4 .x2, mov .x2 .x1, li .x1 rate, li .x3 0x1f]

def xofFinalize (c : Callee) (rate : Nat) : Prog isa :=
  StackScratch.AArch64.withStackScratch 640 .x2 (.seq (.block (xofPadArgs rate)) (Stream.padWith c))

def xofSqueeze (c : Callee) (rate : Nat) : Prog isa :=
  StackScratch.AArch64.withStackScratch 640 .x4
    (.seq (.block (updateArgs rate)) (Stream.squeezeWith c))

/-- Save `x30` and `x19`–`x21` in `scratch[640..672)`, keep `state` in
`x19`, `out` in `x20` and `scratch` in `x21`, and move the arguments to
`pad`'s: `pos` to `x2`, `rate` into `x1`, SHA-3's suffix into `x3` and
`scratch` into `x4`. -/
def finPadArgs (rate : Nat) : List Instr :=
  [.str .x .x30 .x3 664, .str .x .x19 .x3 640, .str .x .x20 .x3 648, .str .x .x21 .x3 656,
    mov .x19 .x0, mov .x20 .x2, mov .x21 .x3, mov .x2 .x1, li .x1 rate, li .x3 0x06, mov .x4 .x21]

/-- `squeeze`'s arguments: `state` (from `x19`), `rate`, position 0, `out`
(from `x20`), `len` bytes, and `scratch` (from `x21`). -/
def finSqzArgs (rate len : Nat) : List Instr :=
  [mov .x0 .x19, li .x1 rate, li .x2 0, mov .x3 .x20, li .x4 len, mov .x5 .x21]

/-- Restore `x30`, then `x19`–`x21` (`x21`, the base, last). -/
def finRestore : List Instr :=
  [.ldr .x .x30 .x21 664, .ldr .x .x19 .x21 640, .ldr .x .x20 .x21 648, .ldr .x .x21 .x21 656]

def finBody (c : Callee) (rate len : Nat) : Prog isa :=
  .seq (.block (finPadArgs rate)) <|
  .seq (.call ("vg_keccak_pad_scratch" ++ c.suffix) (Stream.padWith c)) <|
  .seq (.block (finSqzArgs rate len)) <|
  .seq (.call ("vg_keccak_squeeze_scratch" ++ c.suffix) (Stream.squeezeWith c)) (.block finRestore)

def finalize (c : Callee) (rate len : Nat) : Prog isa :=
  StackScratch.AArch64.withStackScratch 672 .x3 (finBody c rate len)

end VG.Impl.Sha3.AArch64.Instances
