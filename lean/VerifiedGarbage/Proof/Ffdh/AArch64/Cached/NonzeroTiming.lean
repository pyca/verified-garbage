module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Nonzero
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! The zero test's complete trace depends only on public workspace geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem nonzero_ct : RelCT isa (Two GoodW) Generate.nonzero (fun _ _ =>True) := by
 unfold Generate.nonzero
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x0=q.B ∧ s.gpr .x8=off q.B (slot q.w 1) ∧
  s.gpr .x12=BitVec.ofNat 64 q.w) [.x0] pins_goodW (by taint_decide) ?_)
  (two_taint [.x0,.x8,.x12] ?_ (by taint_decide))
 · rintro q s ⟨mi,good,room⟩
   brun [good.x0,hdr_enc (show sArr 1<32 by decide),hdr_enc (show sW<32 by decide),
    header_read good room (show sArr 1<32 by decide),header_read good room (show sW<32 by decide),
    good.hdr.harr 1 (by decide),good.hdr.hw]
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached
