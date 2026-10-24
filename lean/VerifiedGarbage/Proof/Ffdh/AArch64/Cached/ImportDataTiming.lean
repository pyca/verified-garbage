module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportTimingState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Both imported limb ranges and inverse reconstruction have fixed public schedules. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem prefixCopy_ct (i a : Nat) : RelCT isa (Two fun q s =>PrefixCopyReady q i a s) copyWords (fun _ _ =>True) :=
 two_taint [.x16,.x17,.x12] (fun q s t hs ht r hr =>by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide)

theorem importInverse_ct : RelCT isa (Two GoodW)
 (.block ([ldh .x8 (sArr 0),ld .x3 .x8]++minv++[sth .x15 sMinv])) (fun _ _ =>True) := by
 change RelCT isa (Two GoodW) (.block ([ldh .x8 (sArr 0)]++([ld .x3 .x8]++minv++[sth .x15 sMinv]))) _
 apply RelCT.block_append
 refine RelCT.seq (two_piece (Ψ:=fun p s =>s.gpr .x0=p.B ∧ s.gpr .x8=off p.B (slot p.w 0)) [.x0] pins_goodW (by taint_decide) ?_)
  (two_taint [.x0,.x8] (fun _ s t hs ht r hr =>by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.trans ht.2.symm) (by taint_decide))
 rintro p s ⟨mi,good,room⟩
 brun [good.x0,hdr_enc (show sArr 0<32 by decide),header_read good room (show sArr 0<32 by decide),good.hdr.harr 0 (by decide)]

def PrefixSecond (q : ImportPublic) (s : State) : Prop :=
 ImportDataReady q s ∧ s.gpr .x16=off q.ctx (24+8*q.workspace.w)

theorem importData_ct : RelCT isa (Two ImportDataReady) importData (fun _ _ =>True) := by
 unfold importData
 simp only [seqs]
 refine RelCT.seq (two_piece (Ψ:=fun q s =>PrefixCopyReady q 0 0 s) [.x0]
  (fun q s t hs ht =>pins_goodW _ s t hs.good ht.good) (by taint_decide) ?_) ?_
 · intro q s h
   obtain ⟨mi,good,_⟩:=h.good
   refine WP.mono (WP.keep [.x16,.x17,.x12] (Q:=fun t =>
    t.gpr .x16=off q.ctx 24 ∧ t.gpr .x17=off q.workspace.B (slot q.workspace.w 0) ∧
    t.gpr .x12=BitVec.ofNat 64 q.workspace.w ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sArr 0<32 by decide),hdr_enc (show sW<32 by decide),
      header_read good q.room (show sCtx<32 by decide),header_read good q.room (show sArr 0<32 by decide),
      header_read good q.room (show sW<32 by decide),h.context,good.hdr.harr 0 (by decide),good.hdr.hw]
   · rintro t ⟨⟨ptr,dst,count,mem⟩,rest⟩
     exact ⟨⟨⟨mi,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,q.room⟩,
      mem ▸ h.context,fun i hi =>by rw [rest.rd,rest.wr];exact h.readable i hi,h.outside⟩,
      by simpa only [Nat.mul_zero,Nat.add_zero] using ptr,dst,count⟩
 · refine RelCT.seq (two_post (Ψ:=PrefixSecond) (prefixCopy_ct 0 0) ?_) ?_
   · intro q s h
     refine WP.mono (prefixCopy_ok h (by decide : 0<8) (by decide : 0<2)) ?_
     rintro t ⟨ready,_,ptr⟩
     exact ⟨ready,by simpa only [Nat.mul_zero,Nat.add_zero] using ptr⟩
   · refine RelCT.seq (two_piece (Ψ:=fun q s =>PrefixCopyReady q 1 4 s) [.x0]
      (fun q s t hs ht =>pins_goodW _ s t hs.1.good ht.1.good) (by taint_decide) ?_) ?_
     · rintro q s ⟨h,src⟩
       obtain ⟨mi,good,_⟩:=h.good
       refine WP.mono (WP.keep [.x17,.x12] (Q:=fun t =>
        t.gpr .x17=off q.workspace.B (slot q.workspace.w 4) ∧ t.gpr .x12=BitVec.ofNat 64 q.workspace.w ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
       · brun [good.x0,hdr_enc (show sArr 4<32 by decide),hdr_enc (show sW<32 by decide),
          header_read good q.room (show sArr 4<32 by decide),header_read good q.room (show sW<32 by decide),
          good.hdr.harr 4 (by decide),good.hdr.hw]
       · rintro t ⟨⟨dst,count,mem⟩,rest⟩
         exact ⟨⟨⟨mi,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,q.room⟩,
          mem ▸ h.context,fun i hi =>by rw [rest.rd,rest.wr];exact h.readable i hi,h.outside⟩,
          by simpa only [Nat.mul_one] using (rest.gpr .x16 (by decide)).trans src,dst,count⟩
     · refine RelCT.seq (two_post (Ψ:=fun q s =>GoodW q.workspace s) (prefixCopy_ct 1 4) ?_)
        (two_map ImportPublic.workspace (fun _ _ h =>h) importInverse_ct)
       intro q s h
       exact WP.mono (prefixCopy_ok h (by decide : 4<8) (by decide : 1<2)) (fun _ ⟨ready,_,_⟩ =>ready.good)

end VG.Proof.Ffdh.AArch64.Cached
