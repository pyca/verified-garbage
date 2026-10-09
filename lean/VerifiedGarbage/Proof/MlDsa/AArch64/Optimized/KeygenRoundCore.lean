import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep repeatedWord_lane)

theorem setup_ok (s : State) :
    WP isa (.block (vc .v16 8380417 ++ vc .v17 4095)) s fun t =>
      SetupKeep [.v16,.v17] s t ∧ Ready t := by
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v16 8380417) fun a ha => ?_
  refine WP.mono (HighPack.vc_ok a .v17 4095) fun t ht => ?_
  refine ⟨(SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst ht.1),?_,?_⟩
  · intro e he
    rw [ht.1.vec .v16 (by decide),ha.2,repeatedWord_lane _ he]
  · intro e he
    rw [ht.2,repeatedWord_lane _ he]

theorem run_ok (s : State)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa power2Round s fun t =>
      t.mem=roundRun s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64 := by
  unfold power2Round loop
  refine WP.seq (WP.mono (setup_ok s) fun a ⟨hk,hr⟩ => ?_)
  refine WP.seq (WP.mono (Response.counter_ok a) fun b ⟨⟨hc,hm⟩,hv⟩ => ?_)
  have hb : Ready b := ⟨by rw [hv]; exact hr.q,by rw [hv]; exact hr.bias⟩
  have h0 : b.gpr .x0=s.gpr .x0 := (hm.get .x0).trans (hk.gpr .x0 (by decide))
  have h1 : b.gpr .x1=s.gpr .x1 := (hm.get .x1).trans (hk.gpr .x1 (by decide))
  have h2 : b.gpr .x2=s.gpr .x2 := (hm.get .x2).trans (hk.gpr .x2 (by decide))
  refine WP.mono (roundLoop_ok hb hc.1 ?_ ?_ ?_) fun t ht => ?_
  · simpa only [hm.rd,hm.wr,hk.rd,hk.wr,h0] using ha
  · simpa only [hm.wr,hk.wr,h1] using hh
  · simpa only [hm.wr,hk.wr,h2] using hl
  · simpa only [h0,h1,h2,hc.2,hk.mem] using ht.2.2.2.2.2

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
