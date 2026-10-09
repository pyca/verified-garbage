import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowAccess
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowReturnComplete

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)

theorem preparedLow_data {s a b u : State} (ha : Arguments s a)
    (hk : Keep [.x17,.x7] a b) (hm : b.mem=a.mem)
    (hp : Prepared b u) (hl : LowSetup (Round.arg32 s .x5) b u) :
    dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,u.v .v14⟩ := by
  unfold dataAt
  rw [hp.mem,hm,hk.get .x0 (by decide),hk.get .x13 (by decide),hk.get .x14 (by decide),
    ha.work,ha.common,ha.secret,hl.flags]

theorem bound_sub_one (w : BitVec 32) (hw : 1≤w.toNat) :
    w-1=BitVec.ofNat 32 (w.toNat-1) := by
  have h := BitVec.ofNat_sub_ofNat_of_le (w:=32) w.toNat 1 (by decide) hw
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.ofNat_eq_ofNat] using h

theorem bound_width (w : BitVec 32) (hw : 1≤w.toNat) :
    w+(w-1)=BitVec.ofNat 32 (2*w.toNat-1) := by
  rw [bound_sub_one w hw]
  have he : w=BitVec.ofNat 32 w.toNat := by simp
  conv => lhs; lhs; rw [he]
  rw [←BitVec.ofNat_add]
  congr 1
  omega

theorem preparedLow_constants {s a b u : State} (ha : Arguments s a)
    (hk : Keep [.x17,.x7] a b) (hl : LowSetup (Round.arg32 s .x5) b u)
    (hB : 1≤Round.arg32 s .x6) :
    (∀e<4,vword (lowConstantsAt u).scale e=BitVec.ofNat 32 (2*Round.arg32 s .x5)) ∧
    (∀e<4,vword (lowConstantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x6-1)) ∧
    (∀e<4,vword (lowConstantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x6-1)) := by
  refine ⟨hl.scale,?_,?_⟩
  · intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,hk.get .x8 (by decide),ha.bound]
    exact bound_sub_one _ hB
  · intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,hk.get .x8 (by decide),ha.bound]
    exact bound_width _ hB

end VG.Proof.MlDsa.AArch64.Optimized.Paired
