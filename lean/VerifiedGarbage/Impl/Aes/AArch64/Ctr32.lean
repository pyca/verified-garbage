module

public import VerifiedGarbage.Impl.Aes.AArch64.Linear
public import VerifiedGarbage.Impl.Aes.AArch64.Vperm

/-!
# AES counter mode (GCM's `inc₃₂`) on AArch64

`vg_aes_ctr32(schedule = x0, rounds = x1, counter = x2, data = x3, n = x4, scratch = x5)`,
and its out-of-place form, the internal `vg_aes_ctr32_to(…, src = x3, …,
dst = x6)` (`Proof.Aes.ctr32ToAArch64`).

`vg_aes_ctr32` is `ctr32N`, and `vg_aes_ctr32_to` is `ctr32ToN`, the same
out of place: they return at once for no block (`n = 0`, as AES-GCM gives it
for a text with no whole block, or with no bytes after them) and take every
block one at a time by vector permutations (`Vperm.lean`, `ctrFew`): the
counter block is incremented where it is (`ctrOneLoad`), enciphered, and
XORed with the block of the data. Nothing is written to `scratch`.

`savedRegs`, `saveRegs` and `restoreRegs` are the callee-saved registers
`x19`–`x28` and their slots 48–57 of a scratch buffer, for the functions
that save them there (SM4's, Blowfish's and CAST5's).
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.x19, 48), (.x20, 49), (.x21, 50), (.x22, 51), (.x23, 52), (.x24, 53), (.x25, 54), (.x26, 55),
   (.x27, 56), (.x28, 57)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => ldS r k

/-- The counter block at `x2` into `v0`, and `inc₃₂` of it written back:
its last four bytes, a big-endian integer, plus one. -/
def ctrOneLoad : List Instr :=
  [.ldrq .v0 .x2 0, .ldr .w .x6 .x2 12, .rev32 .x6 .x6, .addImm .w .x6 .x6 1, .rev32 .x6 .x6,
    .str .w .x6 .x2 12]

/-- One block of `ctrFew`: the counter block, incremented where it is,
enciphered and XORed with the block at `x3` into the block at `x8`; on to
the next, and `x0` and `x1`, which the cipher writes, back from `x9` and
`x10`. -/
def ctrFewBody : Prog isa :=
  .seq (.block ctrOneLoad)
    (.seq Vperm.core (.block [.ldrq .v1 .x3 0, .vop (.logic .eor .v0 .v0 .v1), .strq .v0 .x8 0,
      .addImm .x .x3 .x3 16, .addImm .x .x8 .x8 16, .subImm .x .x4 .x4 1, movR .x0 .x9,
      movR .x1 .x10]))

/-- The `x4` blocks at `x3` (one at least) in counter mode, one at a time,
into the blocks where they are, or out of place (`to`) into those at `x6`:
a few blocks cost less so than a bitsliced batch. -/
def ctrFew (to : Bool) : Prog isa :=
  .seq (.block [movR .x8 (cond to .x6 .x3), movR .x9 .x0, movR .x10 .x1])
    (.loop ctrFewBody (.nonzero .x .x4))

/-- `vg_aes_ctr32`: nothing for no block (some callers have none), else
each block by vector permutations, one at a time. -/
def ctr32N : Prog isa :=
  .ite (.zero .x .x4) (.block []) (ctrFew false)

/-- `vg_aes_ctr32_to`: as `ctr32N`, out of place. -/
def ctr32ToN : Prog isa :=
  .ite (.zero .x .x4) (.block []) (ctrFew true)

end VG.Impl.Aes.AArch64
