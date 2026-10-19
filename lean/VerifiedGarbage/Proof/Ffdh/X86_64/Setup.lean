module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs

/-! # FFDH on x86-64: initialize an arbitrary odd modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Compute the negative inverse and prepare the operands of `setWord`. -/
theorem minvBlock_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hodd : (word s.mem B (slot w Public.aN)).toNat % 2 = 1) :
    WP isa (.block (([.mov .rbx (.mem (hdr (sArr Public.aN))), .mov .rbx (.mem (at0 .rbx))] : List Instr) ++ minv ++
      ([.store (hdr sMinv) .r15, .mov .r12 (.mem (hdr sW)), .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr))) s fun t =>
      ((word s.mem B (slot w Public.aN)).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 ∧
      t.mem = s.mem.writeW (off B (8 * sMinv)) (t.gpr .r15) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ (t.gpr .rdx).toNat = 1 ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧
      Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hN := Nat.le_trans (slot_le (w := w) (show Public.aN < 8 by decide)) hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = word s.mem B (slot w Public.aN) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, at0, show off B (slot w Public.aN) + BitVec.ofInt 64 0 = off B (slot w Public.aN) from by simp, hg.rdi, hdrOff, hl (sArr Public.aN) (by decide), hg.hdr.harr Public.aN (by decide),
      hg.scr.ld (show slot w Public.aN + 8 ≤ Z by omega)]) rfl) fun s₁ ⟨⟨hbx, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok s₁ (by rw [hbx]; exact hodd)) fun s₂ ⟨hinv, k₂, hm₂⟩ => ?_
  rw [hbx] at hinv
  have k12 := k₁.trans k₂
  have hdi₂ : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have hs₂ := hg.scr.congr k12.2.2
  have hw₂ : word (s₂.mem.writeW (off B (8 * sMinv)) (s₂.gpr .r15)) B (8 * sW) = BitVec.ofNat 64 w := by
    rw [(writeW_outside s₂.mem B (d := 8 * sMinv) _ (by decide)).word
      (by decide) (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega), hm₂, hm₁]
    exact hg.hdr.hw
  refine WP.mono (WP.keep [.r12, .rdx, .rcx] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (8 * sMinv)) (s₂.gpr .r15) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ (t.gpr .rdx).toNat = 1 ∧ t.gpr .rcx = BitVec.ofNat 64 0)
    (by xrun [State.ea, hdr, hdi₂, hdrOff,
      hs₂.st (d := 8 * sMinv) (by have := hdr_lt_slot w 8 (show sMinv < 32 by decide); omega),
      hs₂.ld (d := 8 * sW) (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega), hw₂]) rfl)
    fun t ⟨⟨hm, h12, hdx, hcx⟩, k⟩ => ?_
  have h15 : t.gpr .r15 = s₂.gpr .r15 := k.gpr (by decide)
  exact ⟨by rw [h15]; exact hinv, by rw [hm, hm₂, hm₁, h15], h12, hdx, hcx, (k12.trans k).mono (by decide)⟩

/-- Load a modulus of any supported length, with no primality or top-bit
assumption: the subgroup order can be much smaller than p. -/
theorem modSetup_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw28 : w < 2 ^ 28)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {p : Addr} {bs : List Byte}
    (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hkw : (bs.length + 7) / 8 ≤ wx)
    (hodd : Spec.Rsa.os2ip bs % 2 = 1) :
    WP isa (seqs (modSetup sp sl)) s fun t => ∃ mi', SubCtx t B Z o w wx mi' ∧
      XVals t B o wx mi' (Spec.Rsa.os2ip bs) ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2)), (slot wx Public.aOne, 8 * (wx + 2)), (8 * sMinv, 8)]
        s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hGn := hc.good.scr.nowrap
  have sN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have sO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  have sNO := Rsa.slot_lt (w := wx) (show Public.aN < Public.aOne by decide)
  have hk' : bs.length < 2 ^ 31 := by omega
  unfold modSetup
  refine wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (primeLoad_ok hc hw2 hwx (by omega) (show Public.aN < 8 by decide) hsp hsl hp hl hsrc hk1 hk' hkw)
    fun s₁ ⟨hc₁, hN₁, ho₁, k₁⟩ => ?_
  simp only [seqs]
  have hodd₁ : (word s₁.mem (off B o) (slot wx Public.aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ wx by omega), hN₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd
  refine WP.seq (WP.mono (minvBlock_ok hc₁.good (Nat.le_refl _) hodd₁)
    fun s₂ ⟨hinv, hm₂, h12, hdx, hcx, k₂⟩ => ?_)
  have o₂ := writeW_outside s₁.mem (off B o) (d := 8 * sMinv) (s₂.gpr .r15) (by decide)
  rw [← hm₂] at o₂
  have f₂ : Frm (off B o) [(8 * sMinv, 8)] s₁.mem s₂.mem := Frm.of_outside o₂ (by simp)
  have hc₂ := hc₁.of_minv f₂ (fun r hr => Or.inl (List.mem_singleton.mp hr)) k₂.2.2 (k₂.gpr (by decide))
  have hmi : word s₂.mem (off B o) (8 * sMinv) = s₂.gpr .r15 := by rw [hm₂]; exact word_writeW_self _ _ _ _
  rw [hmi] at hc₂
  refine WP.mono (setWord_ok hc₂.good.scr hc₂.rdi hc₂.hdr (Nat.le_refl _) h12 (by omega) (by omega)
    (o := Public.aOne) (by decide) (ri := .rcx) (by decide) (i := 0) (by omega) hcx)
    fun t ⟨hone, ho₃, k₃⟩ => ?_
  have f₃ : Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s₂.mem t.mem := Frm.of_outside ho₃ (by simp)
  have hc₃ := hc₂.of_frm f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨by unfold slot hdrBytes; omega, sO⟩)
    k₃.2.2 (k₃.gpr (by decide))
  have f₁ : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem := Frm.of_outside ho₁ (by simp)
  have hN : wv t.mem (off B o) (slot wx Public.aN) wx = Spec.Rsa.os2ip bs := by
    rw [f₃.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; omega) (by omega),
      f₂.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMinv slot hdrBytes; omega) (by omega)]
    exact hN₁
  have hword : word t.mem (off B o) (slot wx Public.aN) = word s₁.mem (off B o) (slot wx Public.aN) := by
    rw [f₃.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; omega) (by omega),
      f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMinv slot hdrBytes; omega) (by omega)]
  refine ⟨s₂.gpr .r15, hc₃, ⟨hN, by rw [hword]; exact hinv, by simpa [hdx] using hone⟩,
    ((f₁.append f₂).append f₃).mono (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]), ((k₁.trans k₂).trans k₃).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64
