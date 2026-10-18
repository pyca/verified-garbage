module

public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch

/-!
# Preparing a key context's powers in place, on 256-bit registers

`vg_aes_gcm_prepare`: `H'`–`H'¹⁶` from the hash subkey at `ctx + 240`, as the
stitched loops compute them (`Stitch.setupG`), already in the prepared form
and paired as the context holds them; stored as pairs 0–7, then multiplied
by `H'¹⁶` twice, each time eight independent pairs at once, for pairs 8–15
and 16–23. No calls, no stack.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Prepare

open VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (setupG storesK pregs)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16 mulPair)

/-- Each of the eight pairs of powers times `H'¹⁶` (in both lanes of
`ymm7`), in place. -/
def times16 : List Instr := (List.range 8).flatMap fun k => mulPair (preg16 k) (preg16 k)

/-- The 48 prepared powers into the context at `rdi`, from its hash subkey:
the registers of `setupG` hold pairs 7–0 (`pregs`), so their reverse is
stored from pair 0. -/
def prepare : Prog isa :=
  .block (setupG ++ storesK .rdi pregs.reverse 8 ++
    ([.vop (.vinserti128 .xmm7 .xmm3 .xmm3 1)] : List Instr) ++
    times16 ++ storesK .rdi pregs.reverse 16 ++ times16 ++ storesK .rdi pregs.reverse 24 ++
    ([.vop .vzeroupper] : List Instr))

end VG.Impl.Gcm.X86_64.Prepare
