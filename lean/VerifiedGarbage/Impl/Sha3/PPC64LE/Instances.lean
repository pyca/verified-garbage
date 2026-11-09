module

public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# SHA-3 and SHAKE on PPC64LE: the functions of each instance

As on x86-64 (`Impl/Sha3/X86_64/Instances.lean`): each instance's functions
are the sponge's (`Stream`), after a block that moves the arguments into the
registers the sponge's code takes them in and sets the rate (and suffix) as
constants.

* `update rate (state = r3, pos = r4, data = r5, len = r6, scratch = r7)`
  runs `absorb(state, rate, pos, data, len, scratch)`.
* `xofFinalize rate (state = r3, pos = r4)` runs `pad(state, rate, pos,
  0x1f, scratch)` (SHAKE's suffix), with its working space on the stack
  (`withStackScratch`, which passes it in `r5`).
* `xofSqueeze rate (state = r3, pos = r4, out = r5, outlen = r6)` runs
  `squeeze(state, rate, pos, out, outlen, scratch)`, with its working space
  on the stack (passed in `r7`, then moved up with the others, as
  `update`'s).
* `finalize rate len (state = r3, pos = r4, out = r5)` (SHA-3) calls
  `pad(state, rate, pos, 0x06, scratch)` (SHA-3's suffix), then
  `squeeze(state, rate, 0, out, len, scratch)`, with its working space on
  the stack (passed in `r6`): 640 bytes for the calls, and four more
  doublewords, where it saves `r29`–`r31`, which keep `state`, `out` and
  `scratch` across the calls, and its return address (the link register,
  which each call replaces).
-/

@[expose] public section

namespace VG.Impl.Sha3.PPC64LE.Instances

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- `update`'s arguments, moved up a register, and `rate` in `r4`. -/
def updateArgs (rate : Nat) : List Instr :=
  [mov .r8 .r7, mov .r7 .r6, mov .r6 .r5, mov .r5 .r4, .li .r4 rate]

def update (rate : Nat) : Prog isa := .seq (.block (updateArgs rate)) Stream.absorb

/-- SHAKE's `finalize`'s arguments, with the working space in `r5`, moved to
`pad`'s: the working space to `r7`, `pos` to `r5`, `rate` into `r4` and
SHAKE's suffix into `r6`. -/
def xofPadArgs (rate : Nat) : List Instr := [mov .r7 .r5, mov .r5 .r4, .li .r4 rate, .li .r6 0x1f]

def xofFinalize (rate : Nat) : Prog isa :=
  StackScratch.PPC64LE.withStackScratch 672 .r5 (.seq (.block (xofPadArgs rate)) Stream.pad)

def xofSqueeze (rate : Nat) : Prog isa :=
  StackScratch.PPC64LE.withStackScratch 672 .r7 (.seq (.block (updateArgs rate)) Stream.squeeze)

/-- Save the link register (through `r0`) and `r29`–`r31` in
`scratch[640..672)`, keep `state` in `r29`, `out` in `r30` and `scratch` in
`r31`, and move the arguments to `pad`'s: `pos` to `r5`, `rate` into `r4`,
SHA-3's suffix into `r6` and `scratch` into `r7`. -/
def finPadArgs (rate : Nat) : List Instr :=
  [.mflr .r0, .store .d .r0 .r6 664, .store .d .r29 .r6 640, .store .d .r30 .r6 648,
    .store .d .r31 .r6 656, mov .r29 .r3, mov .r30 .r5, mov .r31 .r6, mov .r5 .r4, .li .r4 rate,
    .li .r6 0x06, mov .r7 .r31]

/-- `squeeze`'s arguments: `state` (from `r29`), `rate`, position 0, `out`
(from `r30`), `len` bytes, and `scratch` (from `r31`). -/
def finSqzArgs (rate len : Nat) : List Instr :=
  [mov .r3 .r29, .li .r4 rate, .li .r5 0, mov .r6 .r30, .li .r7 len, mov .r8 .r31]

/-- Restore the link register, then `r29`–`r31` (`r31`, the base, last). -/
def finRestore : List Instr :=
  [.load .d .r0 .r31 664, .mtlr .r0, .load .d .r29 .r31 640, .load .d .r30 .r31 648,
    .load .d .r31 .r31 656]

def finBody (rate len : Nat) : Prog isa :=
  .seq (.block (finPadArgs rate)) <|
  .seq (.call "vg_keccak_pad_scratch" Stream.pad) <|
  .seq (.block (finSqzArgs rate len)) <|
  .seq (.call "vg_keccak_squeeze_scratch" Stream.squeeze) (.block finRestore)

def finalize (rate len : Nat) : Prog isa :=
  StackScratch.PPC64LE.withStackScratch 704 .r6 (finBody rate len)

end VG.Impl.Sha3.PPC64LE.Instances
