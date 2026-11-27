module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Sha3.X86_64.Instances
public import VerifiedGarbage.Spec.Sha3.Instances

/-! # Sha3 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Sha3.finalizeShake128Api`'s function as emitted. -/
def finalizeShake128 : Prog isa :=
  scrubSel .sse 0 656 [(8, 13), (456, 13)]
    (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate)

/-- `Spec.Sha3.squeezeShake128Api`'s function as emitted. -/
def squeezeShake128 : Prog isa :=
  scrubSel .sse 64 656 [(8, 41)]
    (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate)

/-- `Spec.Sha3.finalizeShake256Api`'s function as emitted. -/
def finalizeShake256 : Prog isa :=
  scrubSel .sse 0 656 [(8, 13), (456, 13)]
    (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate)

/-- `Spec.Sha3.squeezeShake256Api`'s function as emitted. -/
def squeezeShake256 : Prog isa :=
  scrubSel .sse 64 656 [(8, 41)]
    (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate)

/-- `Spec.Sha3.finalizeSha3_224Api`'s function as emitted. -/
def finalizeSha3_224 : Prog isa :=
  scrubAll .sse 0 680
    (Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)

/-- `Spec.Sha3.finalizeSha3_256Api`'s function as emitted. -/
def finalizeSha3_256 : Prog isa :=
  scrubAll .sse 0 680
    (Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)

/-- `Spec.Sha3.finalizeSha3_384Api`'s function as emitted. -/
def finalizeSha3_384 : Prog isa :=
  scrubAll .sse 0 680
    (Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)

/-- `Spec.Sha3.finalizeSha3_512Api`'s function as emitted. -/
def finalizeSha3_512 : Prog isa :=
  scrubAll .sse 0 680
    (Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)

/-- `Spec.Sha3.updateSha3_224Api`'s function as emitted. -/
def absorbSha3_224 : Prog isa :=
  scrubSel .sse 64 656 [(8, 41)]
    (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_224.rate)

/-- `Spec.Sha3.updateSha3_256Api`'s function as emitted. -/
def absorbSha3_256 : Prog isa :=
  scrubSel .sse 64 656 [(8, 41)]
    (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_256.rate)

/-- `Spec.Sha3.updateSha3_384Api`'s function as emitted. -/
def absorbSha3_384 : Prog isa :=
  scrubSel .sse 64 656 [(8, 41)]
    (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_384.rate)

/-- `Spec.Sha3.updateSha3_512Api`'s function as emitted. -/
def absorbSha3_512 : Prog isa :=
  scrubSel .sse 64 656 [(8, 41)]
    (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_512.rate)

/-- `Spec.Sha3.updateShake128Api`'s function as emitted. -/
def absorbShake128 : Prog isa :=
  scrubSel .sse 64 656 [(8, 41)]
    (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.xofShake128.rate)

end VG.Impl.Sha3.X86_64.Fn
