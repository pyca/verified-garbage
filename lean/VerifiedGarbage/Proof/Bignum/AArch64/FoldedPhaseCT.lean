module
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedDispatchCT
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFinish
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixed
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp
meta import VerifiedGarbage.Impl.Rsa.AArch64.Folded
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedDispatchCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedDispatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixed
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def isFast (a : EPub) : Prop := a.len=3 ∧ Spec.Rsa.os2ip a.eb=65537
instance (a : EPub) : Decidable (isFast a) := inferInstanceAs (Decidable (_ ∧ _))
def FinishPre (a : EPub) (s : State) : Prop :=
  if isFast a then GoodL a.L s ∧ word s.mem a.L.B (8*sStarted)=2
  else FPre ⟨a.L,a.N,Spec.Rsa.os2ip a.eb⟩ s

theorem FinishPre.good {a : EPub} {s : State} (h : FinishPre a s) : GoodL a.L s := by
  unfold FinishPre at h
  split at h
  · exact h.1
  · obtain ⟨_,_,hc,_,hz,_⟩ := h; exact ⟨hc.good,hz⟩

theorem FinishPre.mem {a : EPub} {s t : State} (h : FinishPre a s)
    (hm : t.mem=s.mem) (hk : Keep [.x3] s t) : FinishPre a t := by
  unfold FinishPre at h ⊢
  split at h
  · rename_i hf
    rw [ite_eq_left hf]
    exact ⟨⟨⟨h.1.1.scr.congr hk.wr,(hk.gpr .x0 (by decide)).trans h.1.1.x0,hm ▸ h.1.1.hdr⟩,h.1.2⟩,
      by rw [hm]; exact h.2⟩
  · rename_i hf
    rw [ite_eq_right hf]
    obtain ⟨X,x,hc,hy,hz,hw,hw'⟩ := h
    exact ⟨X,x,hc.mem hm hk (by decide),by rw [hm]; exact hy,hz,hw,hw'⟩

theorem fastLoop_fw (M : Mont) (a : EPub) (s : State) (h : PExpPre a s) :
    WP isa (Folded.fastLoop M.mm) s (FinishPre a) := by
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := h
  have src : Src s a.L.B a.L.Z a.ep a.eb :=
    ⟨fun i hi => hs.2.2.1 i (by rw [← hs.1]; exact hi),
     fun i hi => hs.bytes i (by rw [← hs.1]; exact hi),
     fun i hi => hs.2.2.2.2 i (by rw [← hs.1]; exact hi)⟩
  apply fastLoop_dispatch M hc.good hf.1 hs.2.1 he hl src hs.1
  · intro t hm hk h3 h65
    have ct := hc.mem hm hk (by decide)
    refine WP.mono (fixedLoop_ok M ct hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
      hf.2.2.2.2.1 hf.2.2.2.2.2 rfl) fun u ⟨cu,_,mu,_⟩ => ?_
    simp only [FinishPre,ite_eq_left (show isFast a from ⟨h3,h65⟩)]
    exact ⟨⟨cu.good,hf.1⟩,mu⟩
  · intro t hm hk hn
    have ct := hc.mem hm hk (by decide)
    refine WP.mono (pExpLoop_ok (M := M) ct hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
      hf.2.2.2.2.1 hf.2.2.2.2.2 (by rw [hm]; exact he) (by rw [hm]; exact hl)
      hs.1 hL hs.2.1 (by rw [hk.rd,hk.wr]; exact hs.2.2.1)
      (by rw [hm]; exact hs.bytes) hs.2.2.2.2) fun u ⟨cu,yu,_⟩ => ?_
    simp only [FinishPre,ite_eq_right (show ¬ isFast a from hn)]
    exact ⟨X,x,cu,yu,hf.1,hf.2.1,hf.2.2.1⟩

theorem finishTest_fw (a : EPub) (s : State) (h : FinishPre a s) :
    WP isa (.block [ldh .x3 sStarted,.subImm .x .x3 .x3 2]) s fun t =>
      FinishPre a t ∧ isa.eval (.zero .x .x3) t = some (decide (isFast a)) := by
  have orig := h
  unfold FinishPre at h
  split at h
  · rename_i hf
    exact WP.mono (finishTest_ok h.1.1 h.1.2 h.2) fun t ⟨ht,hm,hk⟩ =>
      ⟨orig.mem hm hk,by simpa only [hf,show (2 : BitVec 64)=2#64 from rfl,decide_true] using ht⟩
  · rename_i hf
    obtain ⟨X,x,hc,hy,hz,_⟩ := h
    refine WP.mono (finishTest_ok hc.good hz hy.started) fun t ⟨ht,hm,hk⟩ => ⟨orig.mem hm hk,?_⟩
    rw [ht]
    by_cases he : Spec.Rsa.os2ip a.eb=0 <;> simp only [he,ite_true,ite_false,hf,decide_false] <;> rfl

theorem finishFused_ct (M : Mont) :
    RelCT isa (Two FinishPre) (Folded.finishFused M.mm) (fun _ _ => True) := by
  unfold Folded.finishFused
  refine RelCT.seq (two_piece [.x0] (fun a s t hs ht => pins_good a.L s t hs.good ht.good)
    (by taint_decide) finishTest_fw) ?_
  refine two_ite (fun a s t hs ht => by rw [hs.2,ht.2])
    (RelCT.block_nil (fun _ _ _ => trivial)) ?_
  refine two_map (fun a : EPub => (⟨a.L,a.N,Spec.Rsa.os2ip a.eb⟩ : FPub)) ?_ (finish_ct (M := M))
  intro a s h
  have hn := h.2
  rw [h.1.2] at hn
  have hf : ¬ isFast a := by simpa using hn
  simpa only [FinishPre,ite_eq_right hf] using h.1.1

theorem phase_ct (M : Mont) : RelCT isa (Two PExpPre)
    (.seq (Folded.fastLoop M.mm) (Folded.finishFused M.mm)) (fun _ _ => True) :=
  RelCT.seq (two_post (fastLoop_ct M) (fastLoop_fw M)) (finishFused_ct M)

end VG.Proof.Bignum.AArch64.FoldedPublic
