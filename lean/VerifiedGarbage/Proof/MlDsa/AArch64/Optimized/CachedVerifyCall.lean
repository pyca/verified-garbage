module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {s : State}

theorem sScrV_sub (p : Params) (s : State) :
    Region.Sub ⟨s.gpr .x6, sScr p⟩ ⟨s.gpr .x6, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [sScr, oE]; omega)

theorem sv_sScrV {p : Params} (hp : p ∈ params) (s : State) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨(cachedLay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .x6, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ _
  rw [add_add, add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega) (by omega)

theorem mu_sScrV {p : Params} (hp : p ∈ params) (s : State) :
    Region.Disjoint ⟨(cachedLay p s).MU, 64⟩ ⟨s.gpr .x6, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ _
  rw [add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega) (by omega)

theorem mu_withinV (p : Params) (s : State) : Within ⟨(cachedLay p s).MU, 64⟩ ⟨s.gpr .x6, mScrLen p⟩ :=
  (within_off (cachedLay p s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (cachedLay_X p s)

end

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
