module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

/-! The public q>1 decision and mask store at the end of initialization. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

private theorem finishTail_ok {s : State} {B : Addr} {w : Nat} {b : Byte} {m : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (h8 : s.gpr .r8 = m) (h9 : s.gpr .r9 = b.setWidth 64)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa (.block [.store (Random.sp Random.oMask) .r8,
      .mov .rax (.imm 0), .mov .rcx (.imm 1),
      .alu .cmp .r11 (.imm 2), .cmov .ae .rax (.reg .rcx),
      .alu .cmp .r9 (.imm 2), .cmov .ae .rax (.reg .rcx)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) m ∧ Keep [.rax, .rcx, .r11, .r9] s t := by
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  refine WP.mono (WP.keep [.rax, .rcx, .r11, .r9] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) m) ?_ rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  by_cases hw2 : w < 2 <;> by_cases hb2 : b.toNat < 2 <;>
    xrun [execCmov, eval, random_ea_sp, hsp, hs.st (d := Random.oMask) (by decide),
      h8, h9, h11, BitVec.ult, show (2 : BitVec 64).toNat = 2 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, hb, hw2, hb2] <;> rfl

theorem random_prepareFinish_ok {s : State} {B : Addr} {w : Nat} {b : Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (ha : s.gpr .rax = b.setWidth 64) (h11 : s.gpr .r11 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa Random.prepareFinish s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if w < 2 ∧ b.toNat < 2 then 0 else 1) ∧
      t.mem = s.mem.writeW (off B Random.oMask) (randomMaskValue b.toNat) ∧
      Keep [.rax, .rcx, .r8, .r9, .r11] s t := by
  unfold Random.prepareFinish
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r9 = b.setWidth 64 ∧ u.mem = s.mem)
      (by xrun [ha]) rfl) fun u ⟨⟨hu9, hum⟩, hku⟩ => ?_)
  refine WP.seq (WP.mono (random_mask_ok u) fun v ⟨hv8, hvm, hkv⟩ => ?_)
  have hua := (hku.gpr (show Reg.rax ∉ [Reg.r9] by decide)).trans ha
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  rw [hua, hb] at hv8
  have hk := hku.trans hkv
  refine WP.mono (finishTail_ok (hs.congr hk.2.2) ((hk.gpr (by decide)).trans hsp)
      hv8 ((hkv.gpr (by decide)).trans hu9) ((hk.gpr (by decide)).trans h11) hw)
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hvm, hum], (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
