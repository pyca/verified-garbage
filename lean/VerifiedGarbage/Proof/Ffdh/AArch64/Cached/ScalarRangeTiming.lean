module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ScalarTimingState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LessTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! The complete scalar rejection predicate scans a fixed public geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def ScalarLoadReady (q : ScalarPublic) (s : State) : Prop :=
 ScalarReady q s ∧ s.gpr .x1=q.p.src ∧ s.gpr .x2=BitVec.ofNat 64 q.p.k

theorem scalarRange_ct : RelCT isa (Two ScalarReady) Generate.scalarRange (fun _ _ =>True) := by
 unfold Generate.scalarRange
 simp only [seqs]
 refine RelCT.seq (two_piece (Ψ:=ScalarLoadReady) [.x0] ?_ (by taint_decide) ?_) ?_
 · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.initial.good.x0.trans ht.initial.good.x0.symm
 · rintro q s ⟨bs,h⟩
   have good := h.initial.good
   have x := h.initial.controls.source
   have len := h.initial.controls.length
   rw [h.length] at len
   refine WP.mono (WP.keep [.x1,.x2] (Q:=fun t =>
    t.gpr .x1=q.p.src ∧ t.gpr .x2=BitVec.ofNat 64 q.p.k ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
      header_read good q.p.room (show sX<32 by decide),header_read good q.p.room (show sLen<32 by decide),x,len]
   · rintro t ⟨⟨ptr,len,mem⟩,rest⟩
     exact ⟨⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by decide)).trans good.x0)⟩,ptr,len⟩
 · refine RelCT.seq (two_post (Ψ:=ScalarReady)
    (two_map (fun q =>(⟨scalarWs q,q.p.src,q.p.k⟩ : LoadPublic))
     (fun q s h =>by obtain ⟨⟨bs,h⟩,ptr,len⟩:=h;exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,ptr,len⟩)
     (load_ct (by decide : 1<8) (by taint_decide))) ?_) ?_
   · rintro q s ⟨⟨bs,h⟩,ptr,len⟩
     refine WP.mono (loadArray_ok h.initial.good q.p.room q.words q.positive q.size (by decide : 1<8)
      (source_src h.initial.reads.source h.initial.reads.scalarOutside) h.length ptr len) ?_
     rintro t ⟨good,_,frame,rest⟩
     exact ⟨bs,h.after good (Frm.of_arrays frame (by simp [scalarRanges])) rest⟩
   · refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩) nonzero_ct)
      (fun _ _ h =>scalarReady_nonzero h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarBoundPublic (fun _ _ h =>scalarReady_bound h) scalarBound_ct)
      (fun _ _ h =>scalarReady_bound_ok h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩)
       (less_ct (by decide : 1<8) (by decide : 5<8) (by taint_decide))) ?_)
      (two_taint [.x0] ?_ (by taint_decide))
     · rintro q s ⟨bs,h⟩
       refine WP.mono (less_ok h.initial.good q.p.room (by have :=q.p.positive;omega) q.p.width
        (by decide : 1<8) (by decide : 5<8)) ?_
       rintro t ⟨_,mem,rest⟩
       exact ⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by simp [mmRegs])).trans h.initial.good.x0)⟩
     · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
       have eq : r= .x0 := by simpa using hr
       subst r
       exact hs.initial.good.x0.trans ht.initial.good.x0.symm

end VG.Proof.Ffdh.AArch64.Cached
