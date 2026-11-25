module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
public import VerifiedGarbage.Impl.Sm4.X86_64.CtrFinal
public import VerifiedGarbage.Impl.Sm4.X86_64.Ecb
public import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Sm4.X86_64.Fb
public import VerifiedGarbage.Impl.Sm4.X86_64.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # Sm4 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- The key expansion core also called by SM4-GCM. Its frame is wiped by
its caller. -/
def keyCore : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 3144 .rdx Impl.Sm4.X86_64.expandKey

/-- Call the shared core with the System V stack alignment. -/
def keyCall : Prog isa :=
  .frame (.alloc 8) (.call "vg_sm4_expand_key_core" keyCore) (.free 8)

/-- `Spec.Sm4.expandKeyApi`'s function as emitted, clearing the core's
frame, return-address slot and alignment slot. -/
def expandKey : Prog isa := scrubAll .sse 0 3160 keyCall

/-- `Spec.Sm4.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubSel .sse 0 3144 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .encrypt))

/-- `Spec.Sm4.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubSel .sse 0 3144 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .decrypt))

/-- `Spec.Sm4.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncrypt : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcEncryptChained)

/-- `Spec.Sm4.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecrypt : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcDecryptChained)

/-- `Spec.Sm4.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncrypt)

/-- `Spec.Sm4.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncryptFinal)

/-- `Spec.Sm4.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecrypt)

/-- `Spec.Sm4.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecryptFinal)

/-- `Spec.Sm4.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofb)

/-- `Spec.Sm4.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofbFinal)

/-- `Spec.Sm4.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  scrubSel .sse 0 3216 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr)

/-- `Spec.Sm4.ctrFinalApi`'s function as emitted. -/
def ctrFinal : Prog isa :=
  scrubAll .sse 0 3296
    (Impl.StackScratch.X86_64.withStackScratchWiped 72 .r8 8 Impl.Sm4.X86_64.ctrFinal)

end VG.Impl.Sm4.X86_64.Fn
