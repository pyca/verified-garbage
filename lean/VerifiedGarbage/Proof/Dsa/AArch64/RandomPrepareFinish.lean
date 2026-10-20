module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomMask
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The public q>1 decision and mask store at the end of initialization. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Bignum.AArch64

private theorem compare_ok (s : State) :
    WP isa (.block [movi .x0 0, movi .x4 1, movi .x3 2, .subs .x .x3 .x9 .x3,
      .csel .x .x0 .x4 .x0, movi .x3 2, .subs .x .x3 .x10 .x3,
      .csel .x .x0 .x4 .x0]) s fun t =>
      t.gpr .x0 = (if 2 ≤ (s.gpr .x10).toNat then 1#64
        else if 2 ≤ (s.gpr .x9).toNat then 1#64 else 0#64) ∧ t.mem = s.mem := by
  brun [random_sub_carry, Bool.toNat_true, decide_eq_true_eq]
  rfl

private theorem finishTail_ok {s : State} {B : Addr} {w : Nat} {b : Byte} {m : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (h8 : s.gpr .x8 = m) (h9 : s.gpr .x10 = b.setWidth 64)
    (h11 : s.gpr .x9 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa (.block (Random.store Random.oMask .x8 ++
      [movi .x0 0, movi .x4 1, movi .x3 2, .subs .x .x3 .x9 .x3,
       .csel .x .x0 .x4 .x0, movi .x3 2, .subs .x .x3 .x10 .x3,
       .csel .x .x0 .x4 .x0])) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) m ∧ Keep [.x0, .x3, .x4, .x15] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x15] (Q := fun u =>
    u.mem = s.mem.writeW (off B Random.oMask) m)
    (by unfold Random.store; brun [exec_addSp (show Random.oMask < 4096 by decide),
      hsp, hs.st (d := Random.oMask) (by decide), h8]) rfl rfl rfl)
    fun u ⟨hum, hku⟩ => ?_
  have hu9 := (hku.gpr .x9 (by decide)).trans h11
  have hu10 := (hku.gpr .x10 (by decide)).trans h9
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  refine WP.mono (WP.keep [.x0, .x3, .x4] (Q := fun t =>
    t.gpr .x0 = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧ t.mem = u.mem)
    ?_ rfl rfl rfl) fun t ⟨⟨hta, htm⟩, hkt⟩ =>
      ⟨hta, htm.trans hum, (hku.trans hkt).mono (by decide)⟩
  refine WP.mono (compare_ok u) fun t ⟨ht, hm⟩ => ⟨?_, hm⟩
  rw [ht, hu9, hu10, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  by_cases hw2 : w < 2 <;> by_cases hb2 : b.toNat < 2 <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> rfl


theorem random_prepareFinish_ok {s : State} {B : Addr} {w : Nat} {b : Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (ha : s.gpr .x0 = b.setWidth 64) (h11 : s.gpr .x9 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa Random.prepareFinish s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) (randomMaskValue b.toNat) ∧
      Keep [.x0, .x3, .x4, .x8, .x10, .x15] s t := by
  unfold Random.prepareFinish
  refine WP.seq (WP.mono (WP.keep [.x10] (Q := fun u => u.gpr .x10 = b.setWidth 64 ∧ u.mem = s.mem)
      (by brun [ha]) rfl rfl rfl) fun u ⟨⟨hu9, hum⟩, hku⟩ => ?_)
  refine WP.seq (WP.mono (random_mask_ok u) fun v ⟨hv8, hvm, hkv⟩ => ?_)
  have hua := (hku.gpr .x0 (by decide)).trans ha
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  rw [hua, hb] at hv8
  have hk := hku.trans hkv
  refine WP.mono (finishTail_ok (hs.congr hk.wr) (hk.sp.trans hsp)
      hv8 ((hkv.gpr .x10 (by decide)).trans hu9) ((hk.gpr .x9 (by decide)).trans h11) hw)
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hvm, hum], (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
