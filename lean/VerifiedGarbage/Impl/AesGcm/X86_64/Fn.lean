module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-GCM on x86-64: the functions as emitted

Each function, over the callees `c`, in a frame whose size its
implementations decide (`n` bytes of stack in all), then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`): every vector register at the level
`v` and every caller-saved register but the `rb` bits of the result
cleared, and the `n` bytes of stack its frames and calls use wiped.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

/-- `Spec.Gcm.initApi`'s function as emitted, in `n` bytes of stack. -/
def init (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackScratch (n - 8) .rcx (Impl.AesGcm.X86_64.init c))

/-- `Spec.Gcm.streamInitApi`'s function as emitted, in `n` bytes of stack. -/
def streamInit (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackScratch (n - 8) .r8 (Impl.AesGcm.X86_64.streamInit c))

/-- `Spec.Gcm.streamAadApi`'s function as emitted, in `n` bytes of stack. -/
def streamAad (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackScratch (n - 8) .r9 (Impl.AesGcm.X86_64.streamAad c))

/-- `Spec.Gcm.streamFinishApi`'s function as emitted, in `n` bytes of stack. -/
def streamFinish (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackArgScratch (n - 8) 0 (Impl.AesGcm.X86_64.streamFinish c))

/-- `Spec.Gcm.streamVerifyApi`'s function as emitted, in `n` bytes of stack. -/
def streamVerify (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 32 n (withStackArgScratch (n - 8) 1 (Impl.AesGcm.X86_64.streamVerify c))

end VG.Impl.AesGcm.X86_64.Fn
