module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import Mathlib.Data.Nat.GCD.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter candidates on x86-64: exact small remainders -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem residue_ok {s : State} {B : Addr} {Z w divisor : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hd : 1 < divisor) (hd' : divisor < 2 ^ 31) :
    WP isa (residue divisor) s fun t =>
      (t.gpr .rsi).toNat = wv s.mem B (slot w aN) w % divisor ∧ t.mem = s.mem ∧
      Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hb : (BitVec.ofNat 32 divisor).setWidth 64 = BitVec.ofNat 64 divisor := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  unfold residue
  refine WP.seq (WP.mono (WP.keep [.rbx, .r12, .r8, .rsi, .r14]
    (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 divisor ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .rsi = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hg.hdr.hw,
      hg.hdr.harr aN (by decide), hb]) rfl) fun u ⟨⟨hbx, h12, h8, hsi, h14, hm⟩, k⟩ => ?_)
  refine WP.mono (modWords_ok (hg.scr.congr k.2.2) h8 h12 h14 hw hw'
    (by have := slot_le (w := w) (show aN < 8 by decide); omega) hsi
    (by rw [hbx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hd))
    fun t ⟨hv, hm', k'⟩ => ?_
  exact ⟨by simpa only [hm, hbx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show divisor < 2 ^ 64 by omega)] using hv,
    hm'.trans hm, (k.trans k').mono (by decide)⟩

private theorem mod10_test {s : State} {r : Nat} (hr : r < 10) (hsi : s.gpr .rsi = BitVec.ofNat 64 r) :
    WP isa (.block [.alu .and .rsi (.imm 11), .alu .cmp .rsi (.imm 3)]) s fun t =>
      t.zf = some (decide (r = 3 ∨ r = 7)) ∧ t.mem = s.mem ∧ Keep [.rsi] s t := by
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.zf = some (decide (r = 3 ∨ r = 7)) ∧ t.mem = s.mem)
    ?_ rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> xrun [hsi]

theorem generator2_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa generator2 s fun t => t.zf = some (decide (wv s.mem B (slot w aN) w % 24 = 11)) ∧
      t.mem = s.mem ∧ Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  unfold generator2
  refine WP.seq (WP.mono (residue_ok hg hZ hw hw' (by decide : 1 < 24) (by decide))
    fun u ⟨hv, hm, k⟩ => ?_)
  have hsi : u.gpr .rsi = BitVec.ofNat 64 (wv s.mem B (slot w aN) w % 24) := by
    rw [← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (WP.keep [.rsi] (Q := fun t =>
    t.zf = some (decide (wv s.mem B (slot w aN) w % 24 = 11)) ∧ t.mem = u.mem)
    (by
      xrun [hsi, show BitVec.signExtend 64 (11 : BitVec 32) = BitVec.ofNat 64 11 from by decide]
      exact ofNat_sub_beq (by omega) (by decide)) rfl)
    fun t ⟨⟨hz, hm'⟩, k'⟩ => ⟨hz, hm'.trans hm, (k.trans k').mono (by decide)⟩

theorem generator5_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa generator5 s fun t => t.zf = some (decide (wv s.mem B (slot w aN) w % 10 = 3 ∨
      wv s.mem B (slot w aN) w % 10 = 7)) ∧ t.mem = s.mem ∧
      Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  unfold generator5
  refine WP.seq (WP.mono (residue_ok hg hZ hw hw' (by decide : 1 < 10) (by decide))
    fun u ⟨hv, hm, k⟩ => ?_)
  have hsi : u.gpr .rsi = BitVec.ofNat 64 (wv s.mem B (slot w aN) w % 10) := by
    rw [← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact WP.mono (mod10_test (Nat.mod_lt _ (by decide)) hsi)
    fun t ⟨hz, hm', k'⟩ => ⟨hz, hm'.trans hm, (k.trans k').mono (by decide)⟩

/-- The public generator selector implements generationShape after the candidate's exact-width proof. -/
theorem generatorCheck_ok {s : State} {B : Addr} {Z w bits generator : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hbits : Spec.RsaKeyGen.bitLength (wv s.mem B (slot w aN) w) = bits)
    (hgen : generator = 2 ∨ generator = 5) (hreg : s.gpr .rdx = BitVec.ofNat 64 generator) :
    WP isa generatorCheck s fun t => t.zf = some (Spec.Ffdh.generationShape bits generator (wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  rcases hgen with rfl | rfl
  · unfold generatorCheck
    refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some true ∧ u.mem = s.mem)
      (by xrun [hreg]) rfl) fun u ⟨⟨hz, hm⟩, k⟩ => ?_)
    have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
      by rw [hm]; exact hg.hdr⟩
    refine WP.ite true (by simp [eval, hz]) ?_ (fun h => by simp at h)
    intro _
    exact WP.mono (generator2_ok hgu hZ hw hw') fun t ⟨hz', hm', k'⟩ =>
      ⟨by simpa [Spec.Ffdh.generationShape, hb1, hb2, hbits, hm, Bool.decide_or, Bool.beq_eq_decide_eq] using hz',
        hm'.trans hm, (k.trans k').mono (by decide)⟩
  · unfold generatorCheck
    refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some false ∧ u.mem = s.mem)
      (by xrun [hreg]) rfl) fun u ⟨⟨hz, hm⟩, k⟩ => ?_)
    have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
      by rw [hm]; exact hg.hdr⟩
    refine WP.ite false (by simp [eval, hz]) (fun h => by simp at h) ?_
    intro _
    exact WP.mono (generator5_ok hgu hZ hw hw') fun t ⟨hz', hm', k'⟩ =>
      ⟨by simpa [Spec.Ffdh.generationShape, hb1, hb2, hbits, hm, Bool.decide_or, Bool.beq_eq_decide_eq] using hz',
        hm'.trans hm, (k.trans k').mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
