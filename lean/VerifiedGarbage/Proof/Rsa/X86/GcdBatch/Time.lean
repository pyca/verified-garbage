module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Body
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
public import VerifiedGarbage.Proof.Framework.Taint
public import Init.Data.Option.Basic
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Constant-time batched GCD in the caller's workspace -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Rsa.X86.GcdBatch VG.Proof.Mont VG.Proof.Mont.X86

theorem body_trace {s t sf tf : State} {base : Addr} {size n : Nat} {tr ur : List Leak}
    (hs : Scr s base size) (ht : Scr t base size) (hn : 16 ≤ n) (hnMax : n ≤ 1024)
    (hz : offset n 15 ≤ size) (sp : s.gpr .esp=t.gpr .esp)
    (hm : val32 s.mem base (offset n 8) n%2=1) (hm' : val32 t.mem base (offset n 8) n%2=1)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (hc : (VG.Taint.check taint (WorkspaceTaint.dom (offset n 15)) (body n)
      hint).isSome=true)
    (es : Exec isa (body n) s tr sf) (et : Exec isa (body n) t ur tf) : tr=ur :=
  WorkspaceTaint.trace_eq hs ht hz sp hc
    (WP.mono (body_ok (WorkspaceTaint.view_scr hs) hn hnMax hz hm) fun _ _ => trivial)
    (WP.mono (body_ok (WorkspaceTaint.view_scr ht) hn hnMax hz hm') fun _ _ => trivial) es et

end VG.Proof.Rsa.X86.GcdBatch
