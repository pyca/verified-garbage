module

public import VerifiedGarbage.Impl.AesXts.X86_64
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# XTS-AES of whole blocks on x86-64, out of place, by a copy

`vg_aes_xts_encrypt_to(schedule = rdi, rounds = rsi, tweak = rdx, src = rcx,
n = r8, scratch = r9, dst = r10)` and `vg_aes_xts_decrypt_to` with the same
arguments, for an implementation of `vg_aes_xts_encrypt` and
`vg_aes_xts_decrypt` that has no out-of-place loop of its own: the `n`
blocks at `src` are copied to `dst` (`copyBytes`, 16 bytes at a time with
SSE2's `movdqu`), and transformed there in place by a call of the in-place
function (`copyThen`). The copy keeps every register but `rax`, `r8` and
`r10`, so `schedule`, `rounds` and `n` wait in the scratch buffer, which the
call then uses as its working space.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64To

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (at_)

/-- `schedule`, `rounds` and `n` into the scratch buffer, and the copy's
arguments: `src` in `rsi`, `dst` in `rdi` and `16 n` bytes in `rcx`. -/
def stash : List Instr :=
  [.store (at_ .r9 0) .rdi, .store (at_ .r9 8) .rsi, .store (at_ .r9 16) .r8,
   .mov .rsi (.reg .rcx), .mov .rdi (.reg .r10), .mov .rcx (.reg .r8), .shift .shl .rcx 4]

/-- The arguments of the in-place call: `dst` (still in `rdi`) in `rcx`, and
`schedule`, `rounds` and `n` back from the scratch buffer. -/
def unstash : List Instr :=
  [.mov .rcx (.reg .rdi), .mov .rdi (.mem (at_ .r9 0)), .mov .rsi (.mem (at_ .r9 8)),
   .mov .r8 (.mem (at_ .r9 16))]

/-- The blocks copied from `src` to `dst`, then transformed there by `f`. -/
def copyThen (f : Blocks) : Prog isa :=
  .seq (.block stash)
    (.seq (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .x16) (.seq (.block unstash) (.call f.name f.code)))

end VG.Impl.AesXts.X86_64To
