module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Complete-chunk checking from the retained hash-frame representation. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem chunkCheck_frame_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots) {width used total : Nat}
    (ht : slots.total < 34) (hu : slots.used < 34) (hw : width < 65536)
    (hused : W slots.used = BitVec.ofNat 64 used) (htotal : W slots.total = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) :
    WP isa (.block (chunkCheck slots width)) s fun t =>
      t.gpr .x0 = (if width ≤ total - used then 0 else 1) ∧ t.mem = s.mem ∧
      Keep [.x0, .x3, .x4, .x5] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have himm : (BitVec.ofNat 16 width).setWidth 64 = BitVec.ofNat 64 width := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hwt : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.total)) 64 = BitVec.ofNat 64 total :=
    (R.fr slots.total ht).trans htotal
  have hwu : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.used)) 64 = BitVec.ofNat 64 used :=
    (R.fr slots.used hu).trans hused
  refine WP.mono (WP.keep [.x0, .x3, .x4, .x5] (Q := fun t =>
    t.gpr .x0 = (if width ≤ total - used then 0 else 1) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩
  unfold chunkCheck
  brun [exec_ldrSp (off := 8 * slots.total) ⟨by omega, by omega⟩,
    exec_ldrSp (off := 8 * slots.used) ⟨by omega, by omega⟩, L.sp,
    L.ld (d := 8 * slots.total) (n := 8) (by unfold frameBytes; omega),
    L.ld (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega), hwt, hwu, hsub, himm,
    subs_ge (show total - used < 2 ^ 64 by omega) (show width < 2 ^ 64 by omega)]
  simp only [decide_eq_true_eq]
  rfl

end VG.Proof.Dsa.AArch64.Generation
