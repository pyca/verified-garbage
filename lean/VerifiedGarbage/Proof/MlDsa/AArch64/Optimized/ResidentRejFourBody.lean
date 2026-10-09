import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdvance
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej


theorem fourBody_ok {s : State} {p : Addr} {L : List Zq}
    (hc : Constants s) (h17 : s.gpr .x17=4) (h0 : s.gpr .x0=0)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length+4≤256)
    (hst : Stored s.mem p L)
    (hw : ∀i<256,InRegions s.wr (coeffAddr p i) 4)
    (hw16 : InRegions s.wr (s.gpr .x3) 16) :
    WP isa vectorBody s fun t =>
      Keep bodyRegs s t ∧ Frame [polyR p] s.mem t.mem ∧ Constants t ∧
      t.gpr .x2=s.gpr .x2+12 ∧ t.gpr .x5=s.gpr .x5-4 ∧
      t.gpr .x3=coeffAddr p (candidateFold s.mem (s.gpr .x2) 4 L).length ∧
      (t.gpr .x4).toNat=256-(candidateFold s.mem (s.gpr .x2) 4 L).length ∧
      t.gpr .x16=(if 4≤(t.gpr .x4).toNat then t.gpr .x5 else 0) ∧
      Stored t.mem p (candidateFold s.mem (s.gpr .x2) 4 L) := by
  unfold vectorBody
  refine WP.assoc (WP.seq (WP.mono (fourStep_ok hc hr h3 h4 hL hst hw hw16)
    fun a ⟨ha,haf,hac,hp,hcount,hstored⟩ => ?_))
  have he : fourResult s.mem (s.gpr .x2) L=candidateFold s.mem (s.gpr .x2) 4 L := by
    unfold candidateFold
    change fourResult s.mem (s.gpr .x2) L=
      VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc
       (VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc
        (VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc
         (VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc L (candidate s.mem (s.gpr .x2+0)))
          (candidate s.mem (s.gpr .x2+3))) (candidate s.mem (s.gpr .x2+6)))
        (candidate s.mem (s.gpr .x2+9))
    rw [show s.gpr .x2+0=s.gpr .x2 by bv_omega]
    rfl
  rw [he] at hp hcount hstored
  rw [WP.block_append_iff]
  refine WP.mono (advance_ok 4 (by decide) (s := a)) fun b ⟨hb,hbv,h2,h5⟩ => ?_
  refine WP.mono (guard_ok (s := b)
    (by rw [hb.get .x17,ha.get .x17]; exact h17)
    (by rw [hb.get .x0,ha.get .x0]; exact h0)) fun t ⟨ht,htv,hguard⟩ => ?_
  refine ⟨((ha.trans hb.keep).trans ht.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.mem,hb.mem]; exact haf
  · exact (hac.of_keep hb.keep (by decide) (by decide) hbv).of_keep ht.keep
      (by decide) (by decide) htv
  · rw [ht.get .x2,h2,ha.get .x2]; rfl
  · rw [ht.get .x5,h5,ha.get .x5]; rfl
  · rw [ht.get .x3,hb.get .x3]; exact hp
  · rw [ht.get .x4,hb.get .x4]; exact hcount
  · rw [hguard,ht.get .x4,ht.get .x5]
  · rw [ht.mem,hb.mem]; exact hstored

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
