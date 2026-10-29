module
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # FFDH parameter generation on x86-64: public entry to the selected R² implementation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem preparePrefix_ok {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs [.block prepareHead, setWord aOne .rcx, .block [.mov .r10 (.mem (hdr (sArr aN)))]]) s
      fun t => ∃ mi', R2Pre ⟨⟨B, Z, w, mi'⟩, N⟩ t ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have hO8 := Nat.le_trans (slot_le (w := w) (show aOne < 8 by decide)) hZ
  have hw31 : w < 2 ^ 31 := by omega
  have hN8 := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := w) _ _ _ (by omega), hn, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact hodd
  simp only [seqs]
  refine WP.seq (WP.mono (msHead_ok hg hZ hodd0) fun s₁ ⟨hg₁, hinv₁, _, hcx₁, h12₁, hm₁, k₁⟩ => ?_)
  generalize hmi : s₁.gpr .r15 = mi' at hg₁ hinv₁ hm₁
  have hn₁ : wv s₁.mem B (slot w aN) w = N := by
    rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]; exact hn
  have hw0₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hm₁, hdrStore_word _ _ _ (by decide) (by decide) (by omega)]
  refine WP.seq (WP.mono (setWord_ok hg₁.scr hg₁.rdi hg₁.hdr hZ h12₁ (by omega) hw31 (o := aOne) (by decide) (ri := .rcx)
    (by decide) (i := 0) (by omega) hcx₁) fun s₂ ⟨_, ho₂, k₂⟩ => ?_)
  have ha₂ : Arrays B w [aOne] s₁.mem s₂.mem := Arrays.of_outside (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (Nat.le_refl _)
  have hg₂ : Good s₂ B Z w mi' := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, ha₂.hdr hg₁.hdr⟩
  have hn₂ : wv s₂.mem B (slot w aN) w = N := by rw [ha₂.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hn₁
  have hw0₂ : word s₂.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₂.word0_of_not_mem (by decide) (by decide) (by omega) (by omega)]; exact hw0₁
  have hl : InRegions (s₂.rd ++ s₂.wr) (off B (8 * sArr aN)) 8 :=
    hg₂.scr.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega)
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w aN) ∧ t.mem = s₂.mem)
    (by xrun [State.ea, hdr, hg₂.rdi, hdrOff, hl, hg₂.hdr.harr aN (by decide)]) rfl)
    fun t ⟨⟨h10, hm⟩, k⟩ => ?_
  have hgt : Good t B Z w mi' := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi, by rw [hm]; exact hg₂.hdr⟩
  exact ⟨mi', ⟨⟨hgt, hZ⟩, hw, hw', by rw [hm]; exact hn₂,
    by rw [hm, hw0₂]; exact hinv₁,
    ((k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12₁)), h10, hodd, hlo⟩,
    ((k₁.trans k₂).trans k).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
