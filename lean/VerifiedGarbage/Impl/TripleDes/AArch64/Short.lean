module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc

/-!
# Triple DES on AArch64: a few blocks, one at a time

The bitsliced batch (`Bitsliced.lean`) takes the same time for one block as
for 128, about what the table block (`Impl/CmacTripleDes/AArch64/Round.lean`:
`prep` once, then `enc` or `dec` on each block) takes for eleven. So a call
for fewer than eleven blocks (`few`: the count is public) runs the table
block on each, and any other call the batch.

`ecb d` (schedule = x0, data = x1, n = x2, scratch = x3): the table block on
each block of the data, in place. Its working space is the first 57 words of
the scratch buffer, as CBC encryption's (`TablesCbc.encrypt`).
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64.Short

open VG.AArch64
open VG.Impl.CmacTripleDes.AArch64 (mov prep enc dec)
open VG.Spec.TripleDes (Direction)

/-- `short` for fewer than eleven blocks (in `n`, which is public), `long`
otherwise: `(n + 5) / 16` is zero. (`n + 5` wraps only for an `n` no buffer
has; the two are the same function of every `n`.) -/
def few (n : Reg) (short long : Prog isa) : Prog isa :=
  .seq (.block [.addImm .x .x13 n 5, .lsr .x .x13 .x13 4]) (.ite (.zero .x .x13) short long)

/-- The table block of the direction `d`, after `prep`. -/
def crypt : Direction → Prog isa
  | .encrypt => enc
  | .decrypt => dec

/-- The block at `x1`, as a big-endian integer, into `x5`. -/
def load : List Instr := [.ldr .x .x5 .x1 0, .rev .x5 .x5]

/-- `x5` to the block at `x1`, and on to the next. -/
def store : List Instr :=
  [.rev .x5 .x5, .str .x .x5 .x1 0, .addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1]

/-- ECB over the table block. -/
def ecb (d : Direction) : Prog isa :=
  .seq (.block [mov .x14 .x0, mov .x15 .x3]) <|
  .ite (.zero .x .x2) (.block []) <|
  .seq prep <| .seq (.loop (.seq (.block load) (.seq (crypt d) (.block store))) (.nonzero .x .x2))
    (.block VG.Impl.CmacTripleDes.AArch64.blockRestore)

/-- `vg_triple_des_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := few .x2 (ecb .encrypt) BitsliceNeon.encrypt

/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := few .x2 (ecb .decrypt) BitsliceNeon.decrypt

end VG.Impl.TripleDes.AArch64.Short
