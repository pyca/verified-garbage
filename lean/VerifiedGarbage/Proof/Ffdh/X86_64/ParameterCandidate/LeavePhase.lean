module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter generation on x86-64: return to the retained outer state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem leavePhase_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = off p.B 256)
    (hl : word s.mem (off p.B 256) (8 * sLink) = p.B) :
    WP isa (.block [leave]) s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      t.mem = s.mem ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧
      Keep (.rdi :: mmRegs) s t := by
  have hrd : InRegions (s.rd ++ s.wr) (off (off p.B 256) (8 * sLink)) 8 := by
    have hx : off (off p.B 256) (8 * sLink) = off p.B 384 := by rw [off_off]; rfl
    rw [hx]
    exact h.base.scr.ld (by omega_using [h.base.room, h.base.widths.1])
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = p.B ∧ t.mem = s.mem)
    (by xrun [leave, State.ea, hdr, hdrOff, hdi, hl, hrd]) rfl)
    fun t ⟨⟨hdt, hm⟩, k⟩ => ?_
  obtain ⟨ht, hs, hf⟩ := h.same_mem hm k (by decide)
  exact ⟨ht, hdt, hm, hs, hf, k.mono (by decide)⟩

theorem status_ok {p : CandidateP} {used n : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (hn : n < 2 ^ 32) :
    WP isa (status n) s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * oStatus) = BitVec.ofNat 64 n ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have hst := h.base.scr.st (show 8 * oStatus + 8 ≤ p.Z by
    change 160 ≤ p.Z; omega_using [h.base.header_room])
  have hn64 : n < 2 ^ 64 := Nat.lt_trans hn (by decide)
  have hwide : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn64]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off p.B (8 * oStatus)) (BitVec.ofNat 64 n))
    (by xrun [status, State.ea, hdr, hdrOff, hdi, hst, hwide]) rfl)
    fun t ⟨hm, k⟩ => ?_
  have hf : Frm p.B [(8 * oStatus, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have hfit : ∀ r ∈ [(8 * oStatus, 8)], r.1 + r.2 ≤ p.Z := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    change 160 ≤ p.Z; omega_using [h.base.header_room]
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := by
    intro j hj
    rw [hm]
    exact hdrStore_hdr _ _ _ (by decide) (by omega) (by change 19 ≠ j; omega)
  have hf' := CandidateFrame.of_scr (InScr.of_frm hf hfit)
  exact ⟨h.keep hf' hh k ((k.gpr (by decide)).trans h.base.sp), (k.gpr (by decide)).trans hdi,
    by rw [hm]; exact word_writeW_self _ _ _ _, fun j hj => hh j (by omega), hf', k.mono (by decide)⟩

theorem leaveStatus_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = off p.B 256)
    (hl : word s.mem (off p.B 256) (8 * sLink) = p.B) :
    WP isa leaveStatus s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      t.zf = some (word s.mem p.B (8 * oStatus) == 1) ∧ t.mem = s.mem ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold leaveStatus
  change WP isa (.block ([leave] ++ [.mov .rax (.mem (hdr oStatus)), .alu .cmp .rax (.imm 1)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (leavePhase_ok h hdi hl) fun u ⟨hu, hdu, hm, hs, hf, ku⟩ => ?_
  have hrd := hu.base.scr.ld (show 8 * oStatus + 8 ≤ p.Z by
    change 160 ≤ p.Z; omega_using [h.base.header_room])
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (word s.mem p.B (8 * oStatus) == 1) ∧ t.mem = u.mem)
    (by xrun [State.ea, hdr, hdrOff, hdu, hrd, hm, sub_beq_zero]) rfl)
    fun t ⟨⟨hz, hmt⟩, kt⟩ => ?_
  obtain ⟨ht, hs', hf'⟩ := hu.same_mem hmt kt (by decide)
  exact ⟨ht, (kt.gpr (by decide)).trans hdu, hz, hmt.trans hm,
    hs.trans hs', hf.trans hf', (ku.trans kt).mono (by decide)⟩

theorem innerStatus_ok {p : CandidateP} {used n : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = off p.B 256)
    (hl : word s.mem (off p.B 256) (8 * sLink) = p.B) (hn : n < 2 ^ 32) :
    WP isa (innerStatus n) s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * oStatus) = BitVec.ofNat 64 n ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold innerStatus
  refine WP.seq (WP.mono (leavePhase_ok h hdi hl) fun u ⟨hu, hdu, _, hs, hf, ku⟩ => ?_)
  exact WP.mono (status_ok hu hdu hn) fun t ⟨ht, hdt, hst, hs', hf', kt⟩ =>
    ⟨ht, hdt, hst, hs.trans hs', hf.trans hf', (ku.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
