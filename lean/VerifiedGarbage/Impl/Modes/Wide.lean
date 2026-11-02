module

public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# Block cipher modes, a group of blocks at a time, for any target

`Mode.widen G L M`: the mode `M` (one block of `L` bytes a step) over `G`
blocks a step, for a block cipher that enciphers `G` blocks of its buffer
at once: `M`'s `pre` for each block of the group (each moved to its block of
the data and of the buffer, `Op.shift`), the block cipher on the `G` blocks,
then `M`'s `post` for each block. It computes `G` steps of `M` when no
block's `pre` reads what an earlier block's `post` writes, as in the modes
that decrypt whose blocks can be deciphered independently:

* CBC decryption (`Mode.cbcDecChained`, unchanged): `pre` copies `Cⱼ` to the
  buffer, and `post` XORs the chaining value in, makes `Cⱼ` the chaining
  value, and writes `Pⱼ`.
* CFB decryption, with the chaining value updated in `pre`
  (`Mode.cfbDecEarly`): `pre` copies `Cⱼ₋₁` (the chaining value) to the
  buffer and makes `Cⱼ` the chaining value, and `post` XORs the enciphered
  block into the data.
-/

@[expose] public section

namespace VG.Impl.Modes

/-- Where block `j` starts in each area: the data's blocks are of `st`
bytes, the buffer's of `L`; the chaining value stays where it is. -/
def shOff (L st j : Nat) : Loc → Nat
  | .dat => st * j
  | .buf => L * j
  | .chn => 0

/-- The operation on block `j` of the data and of the buffer. -/
def Op.shift (L st j : Nat) (o : Op) : Op :=
  { o with dOff := o.dOff + shOff L st j o.dst, sOff := o.sOff + shOff L st j o.src,
           xr := o.xr.map fun (l, off) => (l, off + shOff L st j l) }

namespace Mode

/-- `M` over groups of `G` blocks of `L` bytes. -/
def widen (G L : Nat) (M : Mode) : Mode where
  pre := (List.range G).flatMap fun j => M.pre.map (Op.shift L M.step j)
  post := (List.range G).flatMap fun j => M.post.map (Op.shift L M.step j)
  step := G * M.step
  ivOut := M.ivOut

variable (bw : Nat)

/-- CFB decryption (§6.3) with the chaining value updated before the block
cipher: `buf := Cⱼ₋₁`, `Cⱼ` to the chaining value, and `Pⱼ = Cⱼ ⊕
CIPH_K(buf)` to the data. -/
def cfbDecEarly : Mode where
  pre := copyBlk bw .buf .chn ++ copyBlk bw .chn .dat
  post := xorBlk bw .dat .dat .buf
  step := 4 * bw
  ivOut := true

/-- CBC decryption, `G` blocks at a time. -/
def cbcDecWide (G : Nat) : Mode := widen G (4 * bw) (cbcDecChained bw)

/-- CFB decryption, `G` blocks at a time. -/
def cfbDecWide (G : Nat) : Mode := widen G (4 * bw) (cfbDecEarly bw)

end Mode

end VG.Impl.Modes
