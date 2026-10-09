import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarPair

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Sample (rbBody)

def scalarRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x12,.x13,.x14]

structure ScalarBodyPost (η : Nat) (s t : State) (p : Addr) (L : List Zq) : Prop where
 keep : Keep scalarRegs s t
 frame : Frame [polyR p] s.mem t.mem
 input : t.gpr .x2=s.gpr .x2+1
 bytes : t.gpr .x5=s.gpr .x5-1
 output : t.gpr .x3=coeffAddr p (rbStep η L (s.mem (s.gpr .x2))).length
 remaining : (t.gpr .x4).toNat=256-(rbStep η L (s.mem (s.gpr .x2))).length
 stored : Stored t.mem p (rbStep η L (s.mem (s.gpr .x2)))

theorem scalarBody_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr} {L : List Zq}
    (hC : ScalarConsts η s) (hL : L.length≤256) (hS : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (hR : InRegions (s.rd++s.wr) (s.gpr .x2) 1)
    (hW : ∀j<256,InRegions s.wr (coeffAddr p j) 4) :
    WP isa (rbBody η) s fun t=>ScalarBodyPost η s t p L := by
  change WP isa (.seq (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) (scalarPair η)) s _
  refine WP.seq (WP.mono (scalarLoad_ok hC.x11 hR) fun a ⟨hak,ha2,ha5,ha6,ha7⟩=>?_
    )
  refine WP.mono (scalarPair_ok hη (hC.keep hak.keep (by decide)) hL
    (by rw [hak.mem]; exact hS)
    (by rw [hak.get .x3]; exact h3) (by rw [hak.get .x4]; exact h4) ha6 ha7
    (fun j hj=>by rw [hak.wr]; exact hW j hj)) fun t ht=>?_
  refine ⟨(hak.keep.trans ht.keep).mono (by decide),?_,?_,?_,ht.output,ht.remaining,ht.stored⟩
  · rw [←hak.mem]; exact ht.frame
  · rw [ht.keep.gpr .x2 (by decide),ha2]
  · rw [ht.keep.gpr .x5 (by decide),ha5]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
