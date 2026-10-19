module
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Setup

import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Top
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey

/-!
# One-pass XTS-AES on x86-64: encryption

`encrypt_wp`: `Impl.AesXts.X86_64Vaes.encrypt` meets the contract of
`vg_aes_xts_encrypt`, by `crypt_wp` with the key schedule as what the rounds
need (`KPe`): `Vaes.aes` on `ymm0`–`ymm7` and `AesNi.aes` on 128-bit
registers compute the cipher.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0 modeX86_64)
open VG.Proof.Aes.X86_64.AesNi (Keys ofInt_natCast contains_offset)
open VG.Impl.AesXts.X86_64Vaes (regs4)

/-- What encryption's rounds need: the key schedule, `rounds` and its last
round key. -/
def KPe (s₀ : State) (s : State) : Prop :=
  Keys (R s₀) (wK s₀) s ∧ s.gpr .rdi = W s₀ ∧ s.gpr .rsi = s₀.gpr .rsi ∧
    s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R s₀)

theorem kpe_stable {s₀ : State} (hp : UPre s₀) : Stable (KPe s₀) s₀ :=
  fun s s' ⟨hK, hrdi, hrsi, hr10⟩ g1 g2 _ g4 hrd hwr hf =>
    ⟨Aes.X86_64.AesNi.Ecb.keys_congr hK g1 hrd hwr (by
        rw [hrdi]
        exact AesCbc.X86_64.bytesAt_frame hf (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.sch_data.sub_left (Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)))
          · exact (hp.sch_scr.sub_left (Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega))).sub_right
              buf_scr) (by rcases hp.rounds with h | h | h <;> omega)),
      by rw [g1, hrdi], by rw [g2, hrsi], by rw [g4, g1, hr10]⟩

theorem keys_entry {s₀ : State} (hp : UPre s₀) : Keys (R s₀) (wK s₀) s₀ :=
  ⟨rfl, by rcases hp.rounds with h | h | h <;> omega, fun j hj => ⟨schR s₀, by simp [hp.rd], by
    rw [ofInt_natCast]; exact contains_offset (by rcases hp.rounds with h | h | h <;> omega)
      (by rcases hp.rounds with h | h | h <;> omega)⟩⟩

theorem rsi_ofNat (s₀ : State) : s₀.gpr .rsi = BitVec.ofNat 64 (R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- The key schedule, as encryption's rounds need it, after the setup. -/
theorem kpe_pre {s₁ : State} (hp₁ : UPre s₁) {s : State} (h : SInvK s₁ s) : KPe s₁ s := by
  have hrdi : s.gpr .rdi = W s₁ := h.1.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  refine ⟨Aes.X86_64.AesNi.Ecb.keys_congr (keys_entry hp₁) hrdi h.1.rd h.1.wr ?_, hrdi,
    h.1.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [h.2, hrdi]⟩
  exact AesCbc.X86_64.bytesAt_frame h.1.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp₁.sch_scr.sub_left (Region.sub_prefix (by rcases hp₁.rounds with h | h | h <;> omega)))
    (by rcases hp₁.rounds with h | h | h <;> omega)

theorem encrypt_wp {s₀ : State} (h0 : (modeX86_64 (AesXts.xtsMode true)).pre s₀) :
    WP isa Impl.AesXts.X86_64Vaes.encrypt s₀ fun s' =>
      gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s₀ s' := by
  refine crypt_wp (KP := KPe) h0 (fun s₁ hp₁ => kpe_stable hp₁)
    (fun s₁ hp₁ => loop8_ok hp₁ (kpe_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => WP.block_nil ⟨h, ?_⟩)
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact Aes.X86_64.Vaes.aes_ok regs4 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aes_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩
  · exact kpe_pre hp₁ h

end VG.Proof.AesXts.X86_64.Vaes
