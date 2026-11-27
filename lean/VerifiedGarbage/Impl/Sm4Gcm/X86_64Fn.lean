module

public import VerifiedGarbage.Impl.Sm4Gcm.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # SM4-GCM on x86-64: the functions as emitted

Each function, over the callees `c` (of which it calls only `vg_ghash`), in
its frame, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every
vector register at the level `v` and every caller-saved register but the
`rb` bits of the result cleared, and the `n` bytes of stack its frames and
calls use wiped.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.AesGcm.X86_64 (Callees)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

/-- `Spec.Sm4.Gcm.initApi`'s function as emitted. -/
def init : Prog isa := scrubAll .sse 0 5792 (withStackScratch 2568 .rdx Impl.Sm4Gcm.X86_64.init)

/-- `Spec.Sm4.Gcm.sealApi`'s function as emitted. -/
def «seal» (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 0 5816 (withStackArgScratch 2592 2 (Impl.Sm4Gcm.X86_64.«seal» c))

/-- `Spec.Sm4.Gcm.openApi`'s function as emitted. -/
def «open» (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 32 5824 (withStackArgScratch 2600 3 (Impl.Sm4Gcm.X86_64.«open» c))

/-- `Spec.Sm4.Gcm.streamEncryptApi`'s function as emitted. -/
def streamEncrypt (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 0 4008 (withStackArgScratch 784 0 (Impl.Sm4Gcm.X86_64.streamEncrypt c))

/-- `Spec.Sm4.Gcm.streamDecryptApi`'s function as emitted. -/
def streamDecrypt (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 0 4008 (withStackArgScratch 784 0 (Impl.Sm4Gcm.X86_64.streamDecrypt c))

/-- `Spec.Sm4.Gcm.streamFinishApi`'s function as emitted. -/
def streamFinish (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 0 4000 (withStackScratch 776 .r9 (Impl.Sm4Gcm.X86_64.streamFinish c))

/-- `Spec.Sm4.Gcm.streamVerifyApi`'s function as emitted. -/
def streamVerify (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 32 4008 (withStackArgScratch 784 0 (Impl.Sm4Gcm.X86_64.streamVerify c))

end VG.Impl.Sm4Gcm.X86_64.Fn
