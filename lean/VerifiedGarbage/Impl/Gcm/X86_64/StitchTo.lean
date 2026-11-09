module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo

/-!
# The VAES interleaved encryption loop, out of place

`Stitch.enc` for `vg_aes_gcm_encrypt_blocks_to`, which reads the plaintext
from one buffer and writes the ciphertext to another: `(ctx = rdi,
rounds = rsi, counter = rdx, y = rcx, src = r8, n = r9, dst = r10,
scratch = r11)`.

The setup ends with `StitchZTo.setupCTo` in place of `Stitch.setupC`: it
computes `r8 ← src - dst` before `r10` becomes the last round key's address,
and points `rdx` at `dst`. `r8` then stays constant: each pair of plaintext
blocks is loaded from `[rdx + r8 + 32 j]` (the plaintext at the offset of
the output blocks the pair is written to), and the ciphertext stored to
`[rdx + 32 j]`, where the GHASH loads read it back, as in place: the loop is
`Stitch.enc`'s, `Stitch.first true` and `Stitch.body true`.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchTo

open VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupG first body storeCtr lastG storeY)
open VG.Impl.Gcm.X86_64.StitchZTo (setupCTo)

/-- `Stitch.setup`, out of place. -/
def setup : List Instr := setupG ++ storesK .r11 pregs 0 ++ setupCTo

/-- The first group, encrypted only, from `rdx + r8` to `rdx`. -/
abbrev firstTo : Prog isa := first true

/-- A group encrypted (from `rdx + r8 + 256` to `rdx + 256`) and the previous
one hashed (at `rdx`). -/
abbrev bodyTo : Prog isa := body true

/-- `Stitch.enc`, out of place: `n` (a multiple of 16, at least 16) blocks. -/
def enc : Prog isa :=
  .seq (.block setup)
    (.seq firstTo
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop bodyTo .ae))
          (.block (storeCtr ++ lastG ++ storeY)))))

end VG.Impl.Gcm.X86_64.StitchTo
