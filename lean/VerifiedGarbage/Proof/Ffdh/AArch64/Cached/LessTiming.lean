module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Less
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Strict comparison has a public limb count and no predicate-dependent trace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem less_ct {a b : Nat} (left : a<8) (right : b<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0])
  (.block [ldh .x16 (sArr a),ldh .x17 (sArr b),ldh .x14 sW,movi .x7 0,.subs .x .x3 .x7 .x7]) hc).isSome=true) :
 RelCT isa (Two GoodW) (Generate.less a b) (fun _ _ => True) := by
 unfold Generate.less
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x16=off q.B (slot q.w a) ∧
  s.gpr .x17=off q.B (slot q.w b) ∧ s.gpr .x14=BitVec.ofNat 64 q.w) [.x0] pins_goodW check ?_)
  (two_taint [.x16,.x17,.x14] ?_ (by taint_decide))
 · rintro q s ⟨mi,good,room⟩
   refine WP.mono (lessHead_ok good room left right) ?_
   rintro t ⟨⟨ptrA,ptrB,count,_,_,_⟩,_⟩
   exact ⟨ptrA,ptrB,count⟩
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached
