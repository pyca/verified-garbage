module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTCore
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedSave
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedSave
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem save_post (p : XPub) (s : State) (h : FastPre p s) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowShared.save) s (FastPre p) := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  refine WP.mono (save_ok s) fun t ⟨⟨hm,_⟩,kt⟩ => ?_
  have hf : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem t.mem := by rw [hm]; exact Frm.refl _ _ _
  exact ⟨mi,X,Xc,v,hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),hm ▸ ht,hw,hw',hd,hv,hm ▸ hn⟩

theorem work_post (p : XPub) (s : State) (h : FastPre p s) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.work s fun t => t.gpr .x0 = off p.B p.o := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  exact WP.mono (work_ok hc ht hw hw' hd hv hn) fun _ ⟨ct,_⟩ => ct.good.x0

theorem fast_ct : RelCT isa (Two FastPre)
    VG.Impl.Rsa.AArch64.WindowShared.fast (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.fast
  refine RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => by simp at h)
    (by taint_decide) save_post) ?_
  refine RelCT.seq (two_post work_ct work_post) ?_
  refine RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => by simp at h) (by taint_decide))
    (fun p s h => WP.mono (restore_ok s) (fun _ ⟨_,kt⟩ => (kt.gpr .x0 (by decide)).trans h))) ?_
  exact two_taint [.x0] (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ h => h)) (by taint_decide)

end VG.Proof.Bignum.AArch64.WindowShared
