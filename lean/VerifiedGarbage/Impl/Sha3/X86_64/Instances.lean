module

public import VerifiedGarbage.Impl.Sha3.X86_64.Stream
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# SHA-3 and SHAKE on x86-64: the functions of each instance

Each instance's functions are the sponge's (`Stream`), with the instance's
rate (and suffix) set in their code rather than passed: a block moves the
arguments into the registers the sponge's code takes them in, and sets the
rate (and suffix) as constants.

* `update rate (state = rdi, pos = rsi, data = rdx, len = rcx, scratch = r8)`
  runs `absorb(state, rate, pos, data, len, scratch)`.
* `xofFinalize rate (state = rdi, pos = rsi)` runs `pad(state, rate, pos,
  0x1f, scratch)` (SHAKE's suffix), with its working space on the stack
  (`withStackScratch`, which passes it in `rdx`).
* `xofSqueeze rate (state = rdi, pos = rsi, out = rdx, outlen = rcx)` runs
  `squeeze(state, rate, pos, out, outlen, scratch)`, with its working space
  on the stack (passed in `r8`, then moved up with the others, as
  `update`'s).
* `finalize rate len (state = rdi, pos = rsi, out = rdx)` (SHA-3) calls
  `pad(state, rate, pos, 0x06, scratch)` (SHA-3's suffix), then
  `squeeze(state, rate, 0, out, len, scratch)`, with its working space on
  the stack (`withStackScratch`, which passes it in `rcx`): 640 bytes for
  the calls, and two more words, where it saves `r12` and `rbp`, which keep
  `scratch` and `out` across the first call (`rdi`, which the sponge's
  functions never write, keeps `state`).
-/

@[expose] public section

namespace VG.Impl.Sha3.X86_64.Instances

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)

/-- `update`'s arguments, moved up a register, and `rate` in `rsi`. -/
def updateArgs (rate : Nat) : List Instr :=
  [.mov .r9 (.reg .r8), .mov .r8 (.reg .rcx), .mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi),
    .mov32 .rsi (.imm (BitVec.ofNat 32 rate))]

def update (rate : Nat) : Prog isa := .seq (.block (updateArgs rate)) Stream.absorb

/-- SHAKE's `finalize`'s arguments, with the working space in `rdx`, moved to
`pad`'s: the working space to `r8`, `pos` to `rdx`, `rate` into `rsi` and
SHAKE's suffix into `rcx`. -/
def xofPadArgs (rate : Nat) : List Instr :=
  [.mov .r8 (.reg .rdx), .mov .rdx (.reg .rsi), .mov32 .rsi (.imm (BitVec.ofNat 32 rate)),
    .mov32 .rcx (.imm 0x1f)]

def xofFinalize (rate : Nat) : Prog isa :=
  StackScratch.X86_64.withStackScratch 648 .rdx (.seq (.block (xofPadArgs rate)) Stream.pad)

def xofSqueeze (rate : Nat) : Prog isa :=
  StackScratch.X86_64.withStackScratch 648 .r8 (.seq (.block (updateArgs rate)) Stream.squeeze)

/-- Save `r12` and `rbp` in `scratch[640..656)`, keep `scratch` in `r12` and
`out` in `rbp`, and move the arguments to `pad`'s: `pos` to `rdx`, `rate`
into `rsi`, SHA-3's suffix into `rcx` and `scratch` into `r8`. -/
def finPadArgs (rate : Nat) : List Instr :=
  [.store (at_ .rcx 640) .r12, .store (at_ .rcx 648) .rbp, .mov .r12 (.reg .rcx),
    .mov .rbp (.reg .rdx), .mov .rdx (.reg .rsi), .mov32 .rsi (.imm (BitVec.ofNat 32 rate)),
    .mov32 .rcx (.imm 0x06), .mov .r8 (.reg .r12)]

/-- `squeeze`'s arguments: `state` is still in `rdi`, `rate` into `rsi`,
position 0, `out` (from `rbp`), `len` bytes, and `scratch` (from `r12`). -/
def finSqzArgs (rate len : Nat) : List Instr :=
  [.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm 0), .mov .rcx (.reg .rbp),
    .mov32 .r8 (.imm (BitVec.ofNat 32 len)), .mov .r9 (.reg .r12)]

/-- Restore `rbp` and `r12`. -/
def finRestore : List Instr := [.mov .rbp (.mem (at_ .r12 648)), .mov .r12 (.mem (at_ .r12 640))]

def finBody (rate len : Nat) : Prog isa :=
  .seq (.block (finPadArgs rate)) <|
  .seq (.call "vg_keccak_pad_scratch" Stream.pad) <|
  .seq (.block (finSqzArgs rate len)) <|
  .seq (.call "vg_keccak_squeeze_scratch" Stream.squeeze) (.block finRestore)

def finalize (rate len : Nat) : Prog isa :=
  StackScratch.X86_64.withStackScratch 664 .rcx (finBody rate len)

end VG.Impl.Sha3.X86_64.Instances
