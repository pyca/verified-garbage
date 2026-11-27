module

public import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Aes.X86_64.AesNi
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES on x86-64: the functions as emitted

`vg_aes_expand_key` and `vg_aes_expand_key_aesni`, then their cleanup
(`Impl.Scrub.X86_64.scrubSel v rb n rs`): every vector register at the level
`v` and every caller-saved register cleared, and of the `n` bytes of stack
their frames use, the runs of granules `rs` that the residue analysis
(`X86_64.RTaint`) finds may differ between two runs zeroed.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel)

/-- `Spec.Aes.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel .sse 0 520 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.expandKey)

/-- `Spec.Aes.expandKeyApi`'s function (`_aesni`) as emitted. -/
def expandKeyAesni : Prog isa := scrubSel .sse 0 0 [] Impl.Aes.X86_64.AesNi.expandKey

end VG.Impl.Aes.X86_64.Fn
