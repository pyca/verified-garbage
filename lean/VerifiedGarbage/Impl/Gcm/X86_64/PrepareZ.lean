module

public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ

/-!
# Preparing a key context's powers in place, on 512-bit registers

`vg_aes_gcm_prepare` for CPUs with AVX-512: `H'`–`H'¹⁶` from the hash subkey
at `ctx + 240`, as the stitched loops on 256-bit registers compute them
(`Stitch.setupG`), stored as pairs 0–7, as `Prepare16.prepare16` does; then,
with `r11` at pair 0, the sixteen powers loaded four at a time and multiplied
by `H'¹⁶` (pair 7), then by `H'³²` (pair 15, just computed), in each lane
(`StitchZ.powLoad`, as `StitchZ.pow48` computes the tables of the 48-block
loops), for pairs 8–15 and 16–23: half the multiplications of two 256-bit
passes over the eight pairs. No calls, no stack.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.PrepareZ

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (setupG storesK pregs)
open VG.Impl.Gcm.X86_64.StitchZ (powLoad)

/-- The table at `r11 + d` (pairs `8 + d / 32`–…): the sixteen powers at
`r11` times the power at `r11 + h`, in each lane. -/
def table (d h : Nat) : List Instr :=
  .vbroadcasti32x4 .xmm12 (at_ .r11 h) :: (List.range 4).flatMap (powLoad d)

/-- The 48 prepared powers into the context at `rdi`, from its hash subkey:
pairs 0–7 as `Prepare16.prepare16` stores them, the reduction constant in every
lane of `zmm1`, `r11` at pair 0, then pairs 8–15 (times `H'¹⁶`, the first
power of pair 7) and 16–23 (times `H'³²`, the first of pair 15). -/
def prepare : Prog isa :=
  .block (setupG ++ storesK .rdi pregs.reverse 8 ++
    ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr) ++
    ([.mov .r11 (.reg .rdi), .alu .add .r11 (.imm 256)] : List Instr) ++
    table 256 224 ++ table 512 480 ++ ([.vop .vzeroupper] : List Instr))

end VG.Impl.Gcm.X86_64.PrepareZ
