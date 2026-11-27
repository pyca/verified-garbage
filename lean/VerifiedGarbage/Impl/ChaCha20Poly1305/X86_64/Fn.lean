module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.OpenTo
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealSplit
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # ChaCha20-Poly1305 on x86-64: the functions as emitted

Each function over the implementation `x` of `vg_chacha20_xor` and `b` of
`vg_poly1305_blocks`, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`):
every vector register at the level `v` and every caller-saved register but
the `rb` bits of the result cleared, and the `n` bytes of stack its frames
use zeroed, its working space among them.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width byLim sealGatherBy sealGatherWhole)

/-- `Spec.ChaCha20Poly1305.sealApi`'s function as emitted. -/
def «seal» (v : VecLevel) (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  scrubAll v 0 1768 (Shared.sealCode x b)

/-- `Spec.ChaCha20Poly1305.openZeroApi`'s function as emitted. -/
def «open» (v : VecLevel) (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  scrubAll v 32 1784 (Shared.openCode x b)

/-- `Spec.ChaCha20Poly1305.openToApi`'s function as emitted. -/
def openTo (v : VecLevel) (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  scrubAll v 32 1800 (OpenTo.openToCode x b)

/-- `vg_chacha20_poly1305_seal_split`'s code, with its working space in a
frame of its own. -/
def splitCode (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  StackScratch.X86_64.withStackArgScratchWipedX 1736 3 42 (SealSplit.sealSplitFor x b)

/-- `vg_chacha20_poly1305_seal_gather`'s code, calling `seal`'s code
without its cleanup as `sealName` and, for many bytes where `b` is the
AVX-512 or IFMA implementation, `splitCode` as `splitName`. -/
def gatherCode (sealName splitName : String) (x : ChaCha20.X86_64.Callee) :
    Poly1305.X86_64.Blocks → Prog isa
  | .avx512 => sealGatherBy (byLim .avx512) (.ofBlocks .avx512) sealName (Shared.sealCode x .avx512)
      splitName (splitCode x .avx512)
  | .ifma => sealGatherBy (byLim .ifma) (.ofBlocks .ifma) sealName (Shared.sealCode x .ifma)
      splitName (splitCode x .ifma)
  | b => sealGatherWhole (.ofBlocks b) sealName (Shared.sealCode x b)

/-- `Spec.ChaCha20Poly1305.sealGatherApi`'s function as emitted. -/
def sealGather (v : VecLevel) (sealName splitName : String) (x : ChaCha20.X86_64.Callee)
    (b : Poly1305.X86_64.Blocks) : Prog isa :=
  scrubAll v 0 1880 (gatherCode sealName splitName x b)

end VG.Impl.ChaCha20Poly1305.X86_64.Fn
