module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
public import VerifiedGarbage.Impl.TripleDes.X86_64.EcbCall
public import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
public import VerifiedGarbage.Impl.TripleDes.X86_64.FbFinal

/-! # TripleDes on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.TripleDes.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel .sse 0 520 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.TripleDes.X86_64.Key.expandKey)

/-- `Spec.TripleDes.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncrypt : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcEncryptChained)

/-- `Spec.TripleDes.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt)

/-- `Spec.TripleDes.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncryptFinal)

/-- `Spec.TripleDes.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecryptFinal)

/-- `Spec.TripleDes.cfb8EncryptApi`'s function as emitted. -/
def cfb8Encrypt : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Encrypt)

/-- `Spec.TripleDes.cfb8DecryptApi`'s function as emitted. -/
def cfb8Decrypt : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Decrypt)

/-- `Spec.TripleDes.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofb)

/-- `Spec.TripleDes.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubSel .sse 0 984 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofbFinal)

/-- `Spec.TripleDes.ecbEncryptApi`'s function (`_avx512`) as emitted. -/
def ecbEncryptAvx512 : Prog isa :=
  scrubSel .avx 0 1040 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 (Impl.TripleDes.X86_64.EcbCall.avx512 .encrypt))

/-- `Spec.TripleDes.ecbEncryptApi`'s function (`_avx2`) as emitted. -/
def ecbEncryptAvx2 : Prog isa :=
  scrubSel .avx 0 1040 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 (Impl.TripleDes.X86_64.EcbCall.avx2 .encrypt))

/-- `Spec.TripleDes.ecbEncryptApi`'s function as emitted. -/
def ecbEncryptSse : Prog isa :=
  scrubSel .sse 0 1040 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 (Impl.TripleDes.X86_64.EcbCall.sse .encrypt))

/-- `Spec.TripleDes.ecbDecryptApi`'s function (`_avx512`) as emitted. -/
def ecbDecryptAvx512 : Prog isa :=
  scrubSel .avx 0 1040 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 (Impl.TripleDes.X86_64.EcbCall.avx512 .decrypt))

/-- `Spec.TripleDes.ecbDecryptApi`'s function (`_avx2`) as emitted. -/
def ecbDecryptAvx2 : Prog isa :=
  scrubSel .avx 0 1040 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 (Impl.TripleDes.X86_64.EcbCall.avx2 .decrypt))

/-- `Spec.TripleDes.ecbDecryptApi`'s function as emitted. -/
def ecbDecryptSse : Prog isa :=
  scrubSel .sse 0 1040 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 (Impl.TripleDes.X86_64.EcbCall.sse .decrypt))

end VG.Impl.TripleDes.X86_64.Fn
