module

public import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
public import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
public import VerifiedGarbage.Impl.Camellia.X86_64.CtrFinal
public import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
public import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Camellia.X86_64.Fb
public import VerifiedGarbage.Impl.Camellia.X86_64.FbFinal
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # Camellia on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Camellia.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel .sse 0 3216 []
    (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 Impl.Camellia.X86_64.expandKey)

/-- `Spec.Camellia.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubSel .sse 0 3216 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .encrypt))

/-- `Spec.Camellia.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubSel .sse 0 3216 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .decrypt))

/-- `Spec.Camellia.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncrypt : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcEncryptChained)

/-- `Spec.Camellia.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecrypt : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcDecryptChained)

/-- `Spec.Camellia.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncrypt)

/-- `Spec.Camellia.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncryptFinal)

/-- `Spec.Camellia.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecrypt)

/-- `Spec.Camellia.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecryptFinal)

/-- `Spec.Camellia.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofb)

/-- `Spec.Camellia.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofbFinal)

/-- `Spec.Camellia.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  scrubSel .sse 0 3288 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ctr)

/-- `Spec.Camellia.ctrFinalApi`'s function as emitted. -/
def ctrFinal : Prog isa :=
  scrubAll .sse 0 3368
    (Impl.StackScratch.X86_64.withStackScratchWiped 72 .r9 8 Impl.Camellia.X86_64.ctrFinal)

end VG.Impl.Camellia.X86_64.Fn
