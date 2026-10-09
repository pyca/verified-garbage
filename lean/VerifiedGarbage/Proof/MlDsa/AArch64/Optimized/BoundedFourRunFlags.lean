import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRound
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64

theorem SamplerRun.only {σ s t : State} {A : Nat→Spec.Sha3.State} {L : Nat→List Zq}
    (h : SamplerRun σ s A L) {rs : List Reg} (ht : Only rs s t)
    (hr : ∀r∈[Reg.x19,.x20,.x21,.x30],r∉rs) : SamplerRun σ t A L := by
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp)
    ht.rd ht.wr ht.sp (fun r h=>ht.get r (hr r h)),?_,?_,?_,?_⟩ <;>
    rw [ht.mem]
  · exact h.pair0
  · exact h.pair1
  · exact h.table
  · exact h.fields

def countFlag (L : Nat→List Zq) : BitVec 64 := foldedFlags (fun i=>BitVec.ofNat 64 (256-(L i).length)) 3

theorem countFlag_zero {L : Nat→List Zq} (h : ∀i<4,(L i).length≤256) :
    countFlag L=0#64 ↔∀i<4,(L i).length=256 := by
  rw [countFlag,ResidentRej.foldedFlags_zero]
  constructor
  · intro hz i hi
    have hh:=congrArg BitVec.toNat (hz i hi)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hh
    change 256-(L i).length=0 at hh
    have:=h i hi
    omega
  · intro hz i hi
    rw [hz i hi]

theorem flagsStage_ok {σ s : State} (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State}
    {L : Nat→List Zq} (hs : SamplerRun σ s A L) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags) s fun t=>
      SamplerRun σ t A L ∧t.gpr .x27=countFlag L := by
  refine WP.mono (flags_ok hs.env.x19 hs.fields.count
    (fun i hi=>sampler_work_read hp hs.env.wr (by omega))) fun t ⟨⟨ht,hflag⟩,_⟩=>?_
  exact ⟨hs.only ht (by decide),hflag⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
