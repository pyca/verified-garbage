module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR

/-!
# The VAES interleaved decryption loop, out of place

`Stitch.dec` for `vg_aes_gcm_decrypt_blocks_to`, which reads the ciphertext
from one buffer and writes the plaintext to another, for a prepared key
context (`StitchR`): `(ctx = rdi, rounds = rsi, counter = rdx, y = rcx,
src = r8, n = r9, dst = r10, scratch = r11)`, for a number of blocks that is
a multiple of 16, at least 16.

The setup ends with `setupCFrom` in place of `Stitch.setupC`: it points
`rdx` at `src`, as `Stitch.setupC` does at the data, and computes
`r8 ← dst - src` before `r10` becomes the last round key's address. `r8`
then stays constant: the ciphertext blocks are loaded from `[rdx + 32 j]`,
by the GHASH loads too, as in place, and each pair of plaintext blocks is
stored to `[rdx + r8 + 32 j]`, so that the GHASH loads read the ciphertext,
which nothing writes: the loop is `StitchR.decR`'s, `Stitch.dbody`, out of
place.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchFrom

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs dbody storeCtr storeY)

/-- `Y`, the counter pair, the increment, `src` in `rdx`, `dst - src` in
`r8` and the last round key's address in `r10`. -/
def setupCFrom : List Instr :=
  [.vmovdquLoad .l128 .xmm2 (at_ .rcx 0), .vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
   .movImm64 .rax 1, .vop (.vmovq .xmm15 .rax),
   .vmovdquLoad .l128 .xmm14 (at_ .rdx 0), .vop (.vbin .vpshufb .l128 .xmm14 .xmm14 .xmm0),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm15), .vop (.vinserti128 .xmm14 .xmm14 .xmm13 1),
   .movImm64 .rax 2, .vop (.vmovq .xmm15 .rax), .vop (.vinserti128 .xmm15 .xmm15 .xmm15 1),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r8), .alu .sub .r10 (.reg .r8), .mov .r8 (.reg .r10),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

/-- `StitchR.setup`, out of place. -/
def setup : List Instr := StitchZR.setupGP ++ storesK .r11 pregs 0 ++ setupCFrom

/-- `StitchR.decR`, out of place: `n` (a multiple of 16, at least 16)
blocks. -/
def decR : Prog isa :=
  .seq (.block setup) (.seq (.loop (dbody true) .ae) (.block (storeCtr ++ storeY)))

end VG.Impl.Gcm.X86_64.StitchFrom
