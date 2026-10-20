module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameStore
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! # Copy incoming stack arguments into the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


theorem frameCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) {k src : Nat} (hk : k < nW)
    (hs : src % 8 = 0 ∧ src < 32768)
    (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F src) 8) :
    WP isa (.block [.ldrSp .x3 src, .strSp .x3 (8 * k)]) s fun t =>
      Rep t.mem F S V (upd W k (VG.Proof.Bignum.word s.mem F src)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hw : InRegions s.wr (VG.Proof.Bignum.off F (8 * k)) 8 :=
    hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.off F (8 * k)) (VG.Proof.Bignum.word s.mem F src))
    (by brun [exec_ldrSp hs, exec_storeSp (by unfold nW frameBytes at hk; omega : 8 * k % 8 = 0 ∧ 8 * k < 32768), hsp, hr, hw, VG.Proof.Bignum.off, VG.Proof.Bignum.word]) rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

end VG.Proof.Dsa.AArch64.Generation
