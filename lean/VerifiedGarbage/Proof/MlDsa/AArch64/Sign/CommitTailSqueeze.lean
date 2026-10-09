import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSqueezeRate

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (RateBlock)
open VG.Proof.Sha3.AArch64 (wp_addImm)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

/-- The cached mask stream emits the same five rate blocks used by the
ordinary two-lane sampler, into its private workspace. -/
theorem squeeze_ok {s : State} {A B : Spec.Sha3.State} (n : Nat) (hn : n<5)
    (hp : Pairs s A B)
    (hout : ∀i<8, InRegions s.wr
      (s.gpr .x19+BitVec.ofNat 64 (256+136*n)+BitVec.ofNat 64 (16*i)) 16)
    (hlast : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (256+136*n)+128) 8) :
    WP isa (.block (squeeze n)) s fun t =>
      RegKeep [.x6,.x7,.x10] s t ∧ Pairs t A B ∧
      RateBlock t.mem (s.gpr .x19+BitVec.ofNat 64 (256+136*n)) 8 B ∧
      Frame [⟨s.gpr .x19+BitVec.ofNat 64 (256+136*n),136⟩] s.mem t.mem := by
  unfold squeeze
  change WP isa (.block (.addImm .x .x10 .x19 (256+136*n) :: _)) s _
  refine wp_addImm (by omega) fun a ha => ?_
  have hpa : Pairs a A B := by intro i hi; rw [ha.vec]; exact hp i hi
  refine WP.mono (highRate_ok hpa ha.gpr (fun i hi => by rw [ha.wr]; exact hout i hi)
    (by rw [ha.wr]; exact hlast)) fun t ht => ?_
  refine ⟨⟨fun r hr => ?_,ht.1.rd.trans ha.rd,ht.1.wr.trans ha.wr,ht.1.sp.trans ha.sp⟩,
    ht.2.1,ht.2.2.1,?_⟩
  · have h6 : r≠.x6 := fun h => hr (by simp [h])
    have h7 : r≠.x7 := fun h => hr (by simp [h])
    have h10 : r≠.x10 := fun h => hr (by simp [h])
    exact (ht.1.gpr r h6 h7).trans (ha.other r h10)
  · rw [← ha.mem]
    exact ht.2.2.2

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
