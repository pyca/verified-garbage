module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Native array copies share the established CRT constant-time proof. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem copy_ct {a b : Nat} (left : a<8) (right : b<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW,ldh .x16 (sArr b),ldh .x17 (sArr a)]) hc).isSome=true) :
 RelCT isa (Two GoodW) (VG.Impl.Ffdh.AArch64.Cached.copy a b) (fun _ _ => True) := by
 change RelCT isa (Two GoodW) (seqs (VG.Impl.Rsa.AArch64.Crt.copyArr a b)) _
 exact copyArr_ct left right check

end VG.Proof.Ffdh.AArch64.Cached
