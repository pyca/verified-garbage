module
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Setup

import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Enc
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Top
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey

/-!
# One-pass XTS-AES on x86-64: decryption

`decrypt_wp`: `Impl.AesXts.X86_64Vaes.decrypt` meets the contract of
`vg_aes_xts_decrypt`, by `crypt_wp` with the key schedule and the round keys
through `aesimc` as what the rounds need (`KPd`). `AesNi.imcKeys` writes those
at the start of the scratch buffer, below the tweaks (`ImcInv.lo`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0 modeX86_64)
open VG.Proof.Aes.X86_64.AesNi (Keys DKeys ImcInv imcKeys_ok dKeys_of_imc ofInt_natCast)
open VG.Impl.AesXts.X86_64Vaes (regs4)
open VG.Impl.AesXts.X86_64Vaes (bufOff)

/-- What decryption's rounds need: the key schedule, the round keys through
`aesimc` at the scratch buffer, `rounds` and the last round key. -/
def KPd (s₀ : State) (s : State) : Prop :=
  DKeys (R s₀) (wK s₀) s ∧ s.gpr .rdi = W s₀ ∧ s.gpr .rsi = s₀.gpr .rsi ∧ s.gpr .r8 = S s₀ ∧
    s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R s₀)

theorem kpd_stable {s₀ : State} (hp : UPre s₀) : Stable (KPd s₀) s₀ :=
  fun s s' ⟨hK, hrdi, hrsi, hr8, hr10⟩ g1 g2 g3 g4 hrd hwr hf => by
    have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
    refine ⟨Aes.X86_64.AesNi.Ecb.dkeys_congr hK g1 g3 hrd hwr (by
        rw [hrdi]
        exact AesCbc.X86_64.bytesAt_frame hf (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.sch_data.sub_left (Region.sub_prefix hR))
          · exact (hp.sch_scr.sub_left (Region.sub_prefix hR)).sub_right buf_scr) (by omega))
        fun j h1 h2 => ?_,
      by rw [g1, hrdi], by rw [g2, hrsi], by rw [g3, hr8], by rw [g4, g1, hr10]⟩
    have hj : 16 * j + 16 ≤ 224 := by rcases hp.rounds with h | h | h <;> omega
    rw [hr8, ofInt_natCast]
    exact hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 (16 * j), 16⟩) (w := 128) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.data_scr.sub_right (UPre.scr_sub (by omega))).symm
        · exact Offset.disjoint _ (by simp only [bufOff]; omega) (by omega) (by simp only [bufOff]; omega))
      (by decide)

/-- The round keys through `aesimc` at the scratch buffer, below the tweaks:
what decryption's rounds need. -/
theorem imc_pre {s₁ : State} (hp₁ : UPre s₁) {s : State} (h : SInvK s₁ s) :
    WP isa Impl.Aes.X86_64.AesNi.imcKeys s fun s' => SInvK s₁ s' ∧ KPd s₁ s' := by
  have hsw := hp₁.scr_wrap
  have hR : 16 * (R s₁ + 1) ≤ 240 := by rcases hp₁.rounds with h | h | h <;> omega
  have hrdi : s.gpr .rdi = W s₁ := h.1.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hrsi : s.gpr .rsi = s₁.gpr .rsi := h.1.keep _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hr8 : s.gpr .r8 = S s₁ := h.1.r8
  have hW : s.wr = [ivR s₁, dataR s₁, scrR s₁] := by rw [h.1.wr, hp₁.wr]
  have hscr : InRegions s.wr (s.gpr .r8) 2048 := ⟨scrR s₁, by rw [hW]; simp, by
    rw [hr8]; simpa using Offset.contains_base (S s₁) (d := 0) (n := 2048) (k := 2176) (by omega) (by omega)⟩
  have hsch : (⟨s.gpr .rdi, 240⟩ : Region) ∈ s.rd ++ s.wr :=
    List.mem_append_left _ (by rw [h.1.rd, hp₁.rd, hrdi]; simp)
  have hsep : Region.Disjoint ⟨s.gpr .rdi, 240⟩ ⟨s.gpr .r8, 2048⟩ := by
    rw [hrdi, hr8]; exact hp₁.sch_scr.sub_right (Region.sub_prefix (by decide))
  have hK : Keys (R s₁) (wK s₁) s :=
    Aes.X86_64.AesNi.Ecb.keys_congr (keys_entry hp₁) hrdi h.1.rd h.1.wr
      (AesCbc.X86_64.bytesAt_frame h.1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp₁.sch_scr.sub_left (Region.sub_prefix hR)) (by omega))
  refine WP.mono (imcKeys_ok hp₁.rounds (by rw [hrsi, rsi_ofNat]) hscr hsch hsep)
    fun s' ⟨S', hI, hS⟩ => ?_
  have hg := hI.gpr
  have fS : Frame [scrR s₁] s.mem s'.mem := hI.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₁, by simp, by rw [hr8]; exact Region.sub_prefix (by decide)⟩
  refine ⟨⟨⟨by rw [hg, h.1.r8], by rw [hg, h.1.r9], by rw [hg, h.1.r11],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg, h.1.keep r h1 h2 h3 h4 h5 h6 h7],
    by rw [hI.rd, h.1.rd], by rw [hI.wr, h.1.wr], h.1.frame.trans fS, fun j hj => ?_,
    by rw [hg, h.1.rdx], by rw [hg]; exact h.1.tw⟩, by rw [hg, h.2]⟩,
    dKeys_of_imc hK hscr hsep hI hS, by rw [hg, hrdi], by rw [hg, hrsi], by rw [hg, hr8],
    by rw [hg, h.2, hrdi]⟩
  rw [AesCbc.X86_64.bytesAt_frame hI.lo (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hr8]
      exact Offset.disjoint_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega))
    (by decide), h.1.buf j hj]

theorem decrypt_wp {s₀ : State} (h0 : (modeX86_64 (AesXts.xtsMode false)).pre s₀) :
    WP isa Impl.AesXts.X86_64Vaes.decrypt s₀ fun s' =>
      gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s₀ s' := by
  refine crypt_wp (KP := KPd) h0 (fun s₁ hp₁ => kpd_stable hp₁)
    (fun s₁ hp₁ => loop8_ok hp₁ (kpd_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => ?_)
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.VaesBlocks.aesDec_ok regs4 (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aesDec_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩
  · exact imc_pre hp₁ h

end VG.Proof.AesXts.X86_64.Vaes
