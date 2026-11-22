module

public import VerifiedGarbage.Impl.Modes.X86.Wide

/-!
# ECB on x86 (32-bit), for any block cipher with blocks of 8 or 16 bytes

`ecbLevels core gs` (SP 800-38A §6.1): the blocks of the data through a
block cipher's core (`Core`, `Seq.lean`), whose `crypt` applies the cipher,
or its inverse, to the blocks of its buffer. The function takes, cdecl, the
key, the data, its length in blocks and the scratch buffer:
`f(key, data, n, scratch)`, the key the core's `ka` arguments. It is `seqLevels`
(`Wide.lean`) without an initialization vector:

* The callee-saved registers are saved in their slots, `core.prepare` makes
  the key ready, and the data pointer and `n` go to their slots.
* A loop of steps for each group size `g` of `gs` in turn (`Core.levels`),
  each step `g` blocks copied to the buffer, `core.crypt`, and the blocks
  copied back (`ecbWide`, the mode `ecbMode` over `g` blocks), then the
  steps of one block each for the rest (`Core.steps`).
* The registers are restored.

The mode's slot of a chaining value is not used. Only the pointers and `n`
are public: no address or branch depends on the key or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.X86

open VG.X86
open VG.Impl.Modes

/-- ECB (SP 800-38A §6.1): the block to the buffer, the block cipher (or its
inverse), and back to the data. -/
def ecbMode (bw : Nat) : Mode where
  pre := copyBlk bw .buf .dat
  post := copyBlk bw .dat .buf
  step := 4 * bw
  ivOut := false

/-- ECB, `G` blocks at a time. -/
def ecbWide (bw G : Nat) : Mode := Mode.widen G (4 * bw) (ecbMode bw)

namespace Core

variable (c : Core)

/-- The scratch buffer (argument `ka + 2`) to `sb`, the callee-saved
registers to their slots first. -/
def ecbEntry : List Instr :=
  ([.mov .eax (.mem (argOp (c.ka + 2)))] : List Instr) ++
    (List.range 4).map (fun i => .store (at_ .eax (4 * c.savedSlot i)) (savedRegs.getD i .ebx)) ++
    [.mov sb (.reg .eax)]

/-- The data pointer and `n` (arguments `ka` and `ka + 1`) to their slots. -/
def ecbArgs : List Instr :=
  [.mov .eax (.mem (argOp c.ka)), .store (slotAt c.dSlot) .eax, .mov .eax (.mem (argOp (c.ka + 1))),
   .store (slotAt c.nSlot) .eax]

/-- The function, with `loops` for its loops of steps. -/
def ecbWith (loops : Prog isa) : Prog isa :=
  .seq (.block c.ecbEntry) (.seq c.prepare (.seq (.block c.ecbArgs) (.seq loops (.block c.restore))))

/-- The whole function: a wide loop for each of `gs`, then the blocks left,
one at a time. -/
def ecbLevels (gs : List Nat) : Prog isa :=
  c.ecbWith (c.levels (ecbWide c.bw) gs (c.steps (ecbMode c.bw)))

end Core

end VG.Impl.Modes.X86
