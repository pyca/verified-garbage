module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameStore
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Initialize workspace pointers and cursors in the native generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


theorem frameDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) (hbase : W 5 = B)
    {k offset : Nat} (hk : k < nW) (hd : offset < 65536) :
    WP isa (.block [.ldrSp .x3 40, VG.Impl.Bignum.AArch64.movi .x4 offset, .add .x .x3 .x3 .x4,
      .strSp .x3 (8 * k)]) s fun t =>
      Rep t.mem F S V (upd W k (VG.Proof.Bignum.off B offset)) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hw : InRegions s.wr (VG.Proof.Bignum.off F (8 * k)) 8 :=
    hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F 40) 8 :=
    Covers.right hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have hread : s.mem.readW (F + BitVec.ofNat 64 40) 64 = B := (R.fr 5 (by decide)).trans hbase
  have hv : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.off F (8 * k)) (VG.Proof.Bignum.off B offset))
    (by brun [exec_ldrSp (off := 40) (by decide), exec_storeSp (by unfold nW frameBytes at hk; omega : 8 * k % 8 = 0 ∧ 8 * k < 32768), hsp, hr, hw, VG.Proof.Bignum.off, hread, hv]) rfl rfl rfl)
    fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

theorem frameZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) {k : Nat} (hk : k < nW) :
    WP isa (.block [VG.Impl.Bignum.AArch64.movi .x3 0, .strSp .x3 (8 * k)]) s fun t =>
      Rep t.mem F S V (upd W k 0) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hw : InRegions s.wr (VG.Proof.Bignum.off F (8 * k)) 8 :=
    hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.off F (8 * k)) (0 : BitVec 64))
    (by brun [exec_storeSp (by unfold nW frameBytes at hk; omega : 8 * k % 8 = 0 ∧ 8 * k < 32768), hsp, hw, VG.Proof.Bignum.off]; rfl) rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

end VG.Proof.Dsa.AArch64.Generation
