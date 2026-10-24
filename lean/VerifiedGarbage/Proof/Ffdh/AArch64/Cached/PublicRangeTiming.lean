module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LessTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CopyTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SetLowBit
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Result-range checks have no data-dependent branch or address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure RangePublic where
 workspace : Ws
 positive : 0<workspace.w
 size : workspace.w<2^31

def RangeReady (p : RangePublic) (s : State) : Prop := GoodW p.workspace s

theorem setLowBit_ct : RelCT isa (Two GoodW)
 (.block [ldh .x8 (sArr 1),ld .x3 .x8,movi .x4 1,.logic .orr .x .x3 .x3 .x4,st .x3 .x8]) (fun _ _ =>True) := by
 change RelCT isa (Two GoodW) (.block ([ldh .x8 (sArr 1)]++[ld .x3 .x8,movi .x4 1,.logic .orr .x .x3 .x3 .x4,st .x3 .x8])) _
 apply RelCT.block_append
 refine RelCT.seq (two_piece (Ψ:=fun p s =>s.gpr .x8=off p.B (slot p.w 1)) [.x0] pins_goodW (by taint_decide) ?_)
  (two_taint [.x8] (fun p s t hs ht r hr =>by
   have eq : r= .x8 := by simpa using hr
   subst r;exact hs.trans ht.symm) (by taint_decide))
 rintro p s ⟨mi,good,room⟩
 brun [good.x0,hdr_enc (show sArr 1<32 by decide),header_read good room (show sArr 1<32 by decide),good.hdr.harr 1 (by decide)]

theorem publicRange_ct : RelCT isa (Two RangeReady) Generate.publicRange (fun _ _ =>True) := by
 unfold Generate.publicRange
 simp only [seqs]
 refine RelCT.seq (two_post (Ψ:=RangeReady)
  (two_map RangePublic.workspace (fun _ _ h =>h) (less_ct (by decide : 7<8) (by decide : 6<8) (by taint_decide))) ?_) ?_
 · rintro p s ⟨mi,good,room⟩
   refine WP.mono (less_ok good room p.positive p.size (by decide : 7<8) (by decide : 6<8)) ?_
   rintro t ⟨_,mem,rest⟩
   exact ⟨mi,good_after_mem good mem rest ((rest.gpr .x0 (by simp [mmRegs])).trans good.x0),room⟩
 · refine RelCT.seq (two_post (Ψ:=RangeReady) (two_taint [.x0]
    (fun _ s t hs ht =>pins_goodW _ s t hs ht) (by taint_decide)) ?_) ?_
   · rintro p s ⟨mi,good,room⟩
     exact WP.mono (store_control_ok good room (by decide : 16≤sTmp) (by decide : sTmp<32) .x9)
      (fun _ ⟨good,_,_,_⟩ =>⟨mi,good,room⟩)
   · refine RelCT.seq (two_post (Ψ:=RangeReady)
      (two_map RangePublic.workspace (fun _ _ h =>h) (copy_ct (by decide : 1<8) (by decide : 6<8) (by taint_decide))) ?_) ?_
     · rintro p s ⟨mi,good,room⟩
       exact WP.mono (copy_ok good room p.positive p.size (by decide : 1<8) (by decide : 6<8) (by decide))
        (fun _ ⟨good,_,_,_⟩ =>⟨mi,good,room⟩)
     · refine RelCT.seq (two_post (Ψ:=RangeReady)
        (two_map RangePublic.workspace (fun _ _ h =>h) setLowBit_ct) ?_) ?_
       · rintro p s ⟨mi,good,room⟩
         exact WP.mono (setLowBit_ok good room p.positive) (fun _ ⟨good,_,_,_⟩ =>⟨mi,good,room⟩)
       · refine RelCT.seq (two_post (Ψ:=RangeReady)
          (two_map RangePublic.workspace (fun _ _ h =>h) (less_ct (by decide : 1<8) (by decide : 0<8) (by taint_decide))) ?_)
          (two_taint [.x0] (fun _ s t hs ht =>pins_goodW _ s t hs ht) (by taint_decide))
         rintro p s ⟨mi,good,room⟩
         refine WP.mono (less_ok good room p.positive p.size (by decide : 1<8) (by decide : 0<8)) ?_
         rintro t ⟨_,mem,rest⟩
         exact ⟨mi,good_after_mem good mem rest ((rest.gpr .x0 (by simp [mmRegs])).trans good.x0),room⟩

end VG.Proof.Ffdh.AArch64.Cached
