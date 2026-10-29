module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Spec.Dsa.Random
public import Aesop.BuiltinRules

import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.Words
/-! Initialization of the sampler, including its exact memory effects. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomPrepareFinish.lean`, which only this module imported.
section

/-! The public q>1 decision and mask store at the end of initialization. -/
section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomPrepareMem (m : Mem) (B p : Addr) (bs : List Byte) : Mem :=
  (((randomClearMem m B).writeW (off B Random.oQ)
    (p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1))).writeW
    (off B Random.oWidth) (BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1)).writeW
    (off B Random.oMask) (randomMaskValue (VG.Proof.Dsa.significant bs).2.toNat)

theorem random_prepare_ok {s : State} {B p : Addr} {bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hq : word s.mem B Random.oQ = p)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Random.frameBytes p bs)
    (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.prepare s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        (if (VG.Proof.Dsa.significant bs).1 < 2 ∧
          (VG.Proof.Dsa.significant bs).2.toNat < 2 then 0 else 1) ∧
      t.mem = randomPrepareMem s.mem B p bs ∧
      Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s t := by
  unfold Random.prepare
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.2.2
  have husp := (hku.gpr (show Reg.rsp ∉ [Reg.rax] by decide)).trans hsp
  have huq : word u.mem B Random.oQ = p := by
    rw [hum, (random_clear_outside s.mem B).word (by decide) (by decide)]; exact hq
  have hul : word u.mem B Random.oQLen = BitVec.ofNat 64 bs.length := by
    rw [hum, (random_clear_outside s.mem B).word (by decide) (by decide)]; exact hl
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun v =>
      v.gpr .r10 = p ∧ v.gpr .r11 = BitVec.ofNat 64 bs.length ∧ v.mem = u.mem)
      (by xrun [random_ea_sp, husp, hus.ld (d := Random.oQ) (by decide),
        hus.ld (d := Random.oQLen) (by decide), huq, hul]) rfl)
    fun v ⟨⟨hv10, hv11, hvm⟩, hkv⟩ => ?_
  have hk := hku.trans hkv
  have hvsrc := hsrc.congrK (show InScr B Random.frameBytes s.mem v.mem from by
    rw [hvm, hum]; exact InScr.of_outside (random_clear_outside s.mem B) (by decide)) hk
  refine WP.seq (WP.mono (random_significant_ok hv10 hv11 hvsrc hpos hbound)
    fun w ⟨hw10, hw11, hwa, hwm, hkw⟩ => ?_)
  have hkw' := hk.trans hkw
  have hws := hs.congr hkw'.2.2
  have hwsp := (hkw'.gpr (by decide)).trans hsp
  refine WP.seq (WP.mono (WP.keep [] (Q := fun x => x.mem =
      (w.mem.writeW (off B Random.oQ) (p + BitVec.ofNat 64
        (bs.length - (VG.Proof.Dsa.significant bs).1))).writeW
      (off B Random.oWidth) (BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1))
      (by xrun [random_ea_sp, hwsp, hws.st (d := Random.oQ) (by decide),
        hws.st (d := Random.oWidth) (by decide), hw10, hw11]) rfl)
    fun x ⟨hxm, hkx⟩ => ?_)
  have hkx' := hkw'.trans hkx
  refine WP.mono (random_prepareFinish_ok (hs.congr hkx'.2.2)
    ((hkx'.gpr (by decide)).trans hsp) ((hkx.gpr (by decide)).trans hwa)
    ((hkx.gpr (by decide)).trans hw11)
    (by have := VG.Proof.Dsa.significant_fits bs; omega))
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hxm, hwm, hvm, hum]; rfl,
    (hkx'.trans hkt).mono (by decide)⟩

/-- Initialization returns success exactly for the spec's admissible modulus. -/
theorem random_prepare_valid {s : State} {B p : Addr} {bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hq : word s.mem B Random.oQ = p)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Random.frameBytes p bs)
    (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.prepare s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if 1 < Spec.Dsa.decodeBE bs then 1 else 0) ∧
      t.mem = randomPrepareMem s.mem B p bs ∧
      Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s t := by
  refine WP.mono (random_prepare_ok hs hsp hq hl hsrc hpos hbound)
    fun t ⟨hta, htm, hkt⟩ => ⟨?_, htm, hkt⟩
  rw [hta]
  have hv := VG.Proof.Dsa.random_valid_scan_ge bs
  by_cases h : 1 < Spec.Dsa.decodeBE bs
  · have hn : ¬ ((VG.Proof.Dsa.significant bs).1 < 2 ∧
        (VG.Proof.Dsa.significant bs).2.toNat < 2) := by omega
    rw [ite_eq_right hn, ite_eq_left h]
  · have hn : (VG.Proof.Dsa.significant bs).1 < 2 ∧
        (VG.Proof.Dsa.significant bs).2.toNat < 2 := by omega
    rw [ite_eq_left hn, ite_eq_right h]

theorem random_prepare_width (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oWidth =
      BitVec.ofNat 64 (Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE bs)) := by
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self,
    VG.Proof.Dsa.random_drawBytes_scan]

theorem random_prepare_pointer (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oQ =
      p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) := by
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide),
    (writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]

theorem random_prepare_mask (m : Mem) (B p : Addr) (bs : List Byte) :
    word (randomPrepareMem m B p bs) B Random.oMask =
      randomMaskValue (VG.Proof.Dsa.significant bs).2.toNat := by
  unfold randomPrepareMem
  rw [word_writeW_self]

/-- All caller fields before q, and all memory after the nonce, are unchanged. -/
theorem random_prepare_outside (m : Mem) (B p : Addr) (bs : List Byte) :
    Outside B 168 64 m (randomPrepareMem m B p bs) := by
  unfold randomPrepareMem
  exact ((((random_clear_outside m B).mono (by decide) (by decide)).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))

theorem random_prepare_zero (m : Mem) (B p : Addr) (bs : List Byte)
    (i : Nat) (hi : i < 32) :
    randomPrepareMem m B p bs (off B (200 + i)) = 0 := by
  have ho : ofs B (off B (200 + i)) = 200 + i := by
    have he : off B (200 + i) + BitVec.ofNat 64 0 = off B (200 + i) := BitVec.add_zero _
    simpa only [he, Nat.add_zero] using ofs_off B (d := 200 + i) (i := 0) (by omega)
  unfold randomPrepareMem
  rw [(writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oMask]; omega),
    (writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oWidth]; omega),
    (writeW_outside _ B _ (by decide)) _ (by rw [ho]; right; simp only [Random.oQ]; omega)]
  exact random_clear_byte m B i hi

end VG.Proof.Dsa.X86_64
