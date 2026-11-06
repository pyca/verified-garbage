module

public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Spec.Sha3.Contract

/-!
# SHA-3 and SHAKE on RISC-V: the functions of each instance

As on x86-64 (`Impl/Sha3/X86_64/Instances.lean`): each instance's functions
are the sponge's (`Stream`), after a block that moves the arguments into the
registers the sponge's code takes them in and sets the rate (and suffix) as
constants. `pad` and `squeeze` keep their working space in a frame of their
own.

* `update rate (state = a0, pos = a1, data = a2, len = a3, scratch = a4)`
  runs `absorbWs(state, rate, pos, data, len, scratch)`.
* `xofFinalize rate (state = a0, pos = a1)` runs `pad(state, rate, pos,
  0x1f)` (SHAKE's suffix).
* `xofSqueeze rate (state = a0, pos = a1, out = a2, outlen = a3)` runs
  `squeeze(state, rate, pos, out, outlen)`.
* `finalize rate len (state = a0, pos = a1, out = a2)` (SHA-3) calls
  `pad(state, rate, pos, 0x06)` (SHA-3's suffix), then `squeeze(state, rate,
  0, out, len)`, in a frame of 32 bytes (`withStackScratch`, which passes it
  in `a3`) where it saves its return address (which each call replaces) and
  `s2`–`s4`, which keep `state`, `out` and the frame's address across the
  calls.
-/

@[expose] public section

namespace VG.Impl.Sha3.RISCV64.Instances

open VG.RISCV64
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-- `update`'s arguments, moved up a register, and `rate` in `a1`. -/
def updateArgs (rate : Nat) : List Instr :=
  [mov .a5 .a4, mov .a4 .a3, mov .a3 .a2, mov .a2 .a1, .li .a1 rate]

def update (rate : Nat) : Prog isa := .seq (.block (updateArgs rate)) Stream.absorbWs

/-- SHAKE's `finalize`'s arguments, moved to `pad`'s: `pos` to `a2`, `rate`
into `a1` and SHAKE's suffix into `a3`. -/
def xofPadArgs (rate : Nat) : List Instr := [mov .a2 .a1, .li .a1 rate, .li .a3 0x1f]

def xofFinalize (rate : Nat) : Prog isa := .seq (.block (xofPadArgs rate)) Stream.pad

/-- SHAKE's `squeeze`'s arguments, moved up a register, and `rate` in `a1`. -/
def xofSqueezeArgs (rate : Nat) : List Instr := [mov .a4 .a3, mov .a3 .a2, mov .a2 .a1, .li .a1 rate]

def xofSqueeze (rate : Nat) : Prog isa := .seq (.block (xofSqueezeArgs rate)) Stream.squeeze

/-- Save the return address and `s2`–`s4` in the frame at `a3`, keep
`state` in `s2`, `out` in `s3` and the frame in `s4`, and move the arguments
to `pad`'s: `pos` to `a2`, `rate` into `a1` and SHA-3's suffix into `a3`. -/
def finPadArgs (rate : Nat) : List Instr :=
  [.store .d .ra .a3 0, .store .d .s2 .a3 8, .store .d .s3 .a3 16, .store .d .s4 .a3 24,
    mov .s2 .a0, mov .s3 .a2, mov .s4 .a3, mov .a2 .a1, .li .a1 rate, .li .a3 0x06]

/-- `squeeze`'s arguments: `state` (from `s2`), `rate`, position 0, `out`
(from `s3`) and `len` bytes. -/
def finSqzArgs (rate len : Nat) : List Instr :=
  [mov .a0 .s2, .li .a1 rate, .li .a2 0, mov .a3 .s3, .li .a4 len]

/-- Restore the return address and `s2`–`s4` (`s4`, the base, last). -/
def finRestore : List Instr :=
  [.load .d .ra .s4 0, .load .d .s2 .s4 8, .load .d .s3 .s4 16, .load .d .s4 .s4 24]

def finBody (rate len : Nat) : Prog isa :=
  .seq (.block (finPadArgs rate)) <|
  .seq (.call Spec.Sha3.padApi.name Stream.pad) <|
  .seq (.block (finSqzArgs rate len)) <|
  .seq (.call Spec.Sha3.squeezeApi.name Stream.squeeze) (.block finRestore)

def finalize (rate len : Nat) : Prog isa :=
  StackScratch.RISCV64.withStackScratch 32 .a3 (finBody rate len)

end VG.Impl.Sha3.RISCV64.Instances
