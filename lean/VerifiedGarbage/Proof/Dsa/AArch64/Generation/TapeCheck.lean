module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # A complete-chunk test cannot wrap a tape cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem chunkCheck_ok (slots : TapeSlots) {s : State} {B : Addr} {Z total used width : Nat}
    (hs : Scr s B Z) (hsp : s.sp = B)
    (ht : 8 * slots.total + 8 ≤ Z) (hu : 8 * slots.used + 8 ≤ Z)
    (hit : 8 * slots.total < 32768) (hiu : 8 * slots.used < 32768)
    (hwidth : width < 65536) (htotal : total < 2 ^ 64) (hused : used ≤ total)
    (hwt : word s.mem B (8 * slots.total) = BitVec.ofNat 64 total)
    (hwu : word s.mem B (8 * slots.used) = BitVec.ofNat 64 used) :
    WP isa (.block (chunkCheck slots width)) s fun t =>
      t.gpr .x0 = (if width ≤ total - used then 0 else 1) ∧ t.mem = s.mem ∧
      Keep [.x0, .x3, .x4, .x5] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hw64 : width < 2 ^ 64 := by omega
  have himm : (BitVec.ofNat 16 width).setWidth 64 = BitVec.ofNat 64 width := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x0, .x3, .x4, .x5] (Q := fun t =>
    t.gpr .x0 = (if width ≤ total - used then 0 else 1) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨h0, hm⟩, hk⟩ => ⟨h0, hm, hk⟩
  unfold chunkCheck
  brun [exec_ldrSp ⟨by omega, hit⟩, exec_ldrSp ⟨by omega, hiu⟩,
    hsp, hs.ld ht, hs.ld hu, hwt, hwu, hsub, himm,
    subs_ge (show total - used < 2 ^ 64 by omega) hw64]
  simp only [decide_eq_true_eq]
  rfl

end VG.Proof.Dsa.AArch64.Generation
