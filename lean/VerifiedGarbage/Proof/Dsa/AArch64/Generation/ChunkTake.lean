module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Advance one complete chunk and retain its input pointer -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem chunkTake_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots) {width used : Nat}
    (hb : slots.base < 34) (hu : slots.used < 34) (hp : slots.pointer < 34)
    (hu12 : slots.used ≠ 12) (hp12 : slots.pointer ≠ 12) (hw : width < 65536)
    (hused : W slots.used = BitVec.ofNat 64 used) :
    WP isa (.block (tapeTake slots width)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd (upd W slots.pointer (VG.Proof.Bignum.off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x15] s t := by
  have hadd : BitVec.ofNat 64 used + BitVec.ofNat 64 width = BitVec.ofNat 64 (used + width) :=
    (BitVec.ofNat_add _ _).symm
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x15] (Q := fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.off F (8 * slots.pointer)) (VG.Proof.Bignum.off (W slots.base) used)).writeW
        (VG.Proof.Bignum.off F (8 * slots.used)) (BitVec.ofNat 64 (used + width))) (by
    have himm : (BitVec.ofNat 16 width).setWidth 64 = BitVec.ofNat 64 width := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    have hwb : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.base)) 64 = W slots.base := R.fr slots.base hb
    have hwu : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.used)) 64 = BitVec.ofNat 64 used :=
      (R.fr slots.used hu).trans hused
    unfold tapeTake Impl.Dsa.AArch64.Random.store
    brun [exec_ldrSp (off := 8 * slots.base) ⟨by omega, by omega⟩,
      exec_ldrSp (off := 8 * slots.used) ⟨by omega, by omega⟩,
      exec_addSp (show 8 * slots.pointer < 4096 by omega), exec_addSp (show 8 * slots.used < 4096 by omega), L.sp,
      L.ld (d := 8 * slots.base) (n := 8) (by unfold frameBytes; omega),
      L.ld (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega),
      L.st (d := 8 * slots.pointer) (n := 8) (by unfold frameBytes; omega),
      L.st (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega), hwb, hwu, himm, hadd]) rfl rfl rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V
      (upd (upd W slots.pointer (VG.Proof.Bignum.off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) := by
    rw [hm]
    exact (R.wf L.geo hp _).wf L.geo hu _
  refine ⟨lay_of_rep L R Rt (by simp [upd, Ne.symm hu12, Ne.symm hp12])
    hk.sp hk.wr, Rt, ?_, hk⟩
  have ff : Outside F 0 frameBytes s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ F _ (d := 8 * slots.pointer) (by omega)).mono (by omega) (by unfold frameBytes; omega)).trans
      ((writeW_outside _ F _ (d := 8 * slots.used) (by omega)).mono (by omega) (by unfold frameBytes; omega))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega

end VG.Proof.Dsa.AArch64.Generation
