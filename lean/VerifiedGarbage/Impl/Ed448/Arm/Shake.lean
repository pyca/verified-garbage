module

public import VerifiedGarbage.Impl.Ed448.Arm.PublicKey

/-!
# Ed448 on ARMv7: SHAKE256 of `dom4(0, C) ‖ …` in Ed25519's frame

The blocks with which a complete Ed448 operation in Ed25519's frame on this
target (`Impl/Ed25519/Arm/Whole`) hashes, with the sponge functions
(`vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch`, `vg_keccak_squeeze_scratch`, rate 136,
SHAKE's suffix): the Keccak state at `scratch` and their working space at
`scratch + 208`, `scratch` the saved word `sc` (`.caller sc`).

* `hdrAt j off`: the first ten bytes of `dom4(0, context)`
  (`"SigEd448" ‖ 0 ‖ ctxlen`) in the frame at `off`, from the saved word
  `j`, `ctxlen` (below 256): the word `ctxlen · 2^8` (the bytes
  `0 ‖ ctxlen`) at `off + 8`, then `"SigEd448"` in the two words before it.
* `zeroState sc`: the Keccak state zeroed.
* `firstArgs`, `nextArgs`: an absorption's arguments, from position 0, or
  from the position the previous one returned in `r0` (moved to `r2`);
  `padArgs` likewise; `sqzArgs`: 114 bytes squeezed into the frame.

Every address depends only on `sp` and `scratch`.
-/

@[expose] public section

namespace VG.Impl.Ed448.Arm.Shake

open VG.Arm
open VG.Impl.Ed25519.Arm.Whole

/-- Where in `scratch` the sponge functions' working space is. -/
def KSCR : Nat := 208

def hdrAt (j off : Nat) : List Instr :=
  [.ldrSp .r0 (248 + 4 * j), .mov .r0 (.shifted .r0 .lsl 8), .addSp .r12 off, .str .r0 .r12 8,
    .movw .r0 0x6953, .movt .r0 0x4567, .str .r0 .r12 0,
    .movw .r0 0x3464, .movt .r0 0x3834, .str .r0 .r12 4]

/-- `scratch` into `r0`, `0` into `r1`. -/
def zeroArgs (sc : Nat) : List Instr := setup [(.r0, .caller sc 0), (.r1, .const 0)] []

/-- The Keccak state at `scratch`, zeroed. -/
def zeroState (sc : Nat) : Prog isa := .seq (.block (zeroArgs sc)) (.block PublicKey.zeroStores)

/-- `absorb(state = scratch, rate = 136, pos = 0, data = src, len, scratch + 208)`. -/
def firstArgs (sc : Nat) (src len : Value) : List Instr :=
  setup [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, src)] [len, .caller sc KSCR]

/-- `absorb(state = scratch, rate = 136, pos = r0, data = src, len,
scratch + 208)`: at the position the previous absorption returned. -/
def nextArgs (sc : Nat) (src len : Value) : List Instr :=
  .mov .r2 (.reg .r0) :: setup [(.r0, .caller sc 0), (.r1, .const 136), (.r3, src)] [len, .caller sc KSCR]

/-- `pad(state = scratch, rate = 136, pos = r0, suffix = 0x1f, scratch + 208)`. -/
def padArgs (sc : Nat) : List Instr :=
  .mov .r2 (.reg .r0) :: setup [(.r0, .caller sc 0), (.r1, .const 136), (.r3, .const 0x1f)] [.caller sc KSCR]

/-- `squeeze(state = scratch, rate = 136, pos = 0, out = sp + d, len = 114,
scratch + 208)`. -/
def sqzArgs (sc d : Nat) : List Instr :=
  setup [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame d)] [.const 114, .caller sc KSCR]

def absorb (args : List Instr) : Prog isa :=
  callWith args Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb

def pad (sc : Nat) : Prog isa := callWith (padArgs sc) Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad

def squeeze (sc d : Nat) : Prog isa :=
  callWith (sqzArgs sc d) Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze

end VG.Impl.Ed448.Arm.Shake
