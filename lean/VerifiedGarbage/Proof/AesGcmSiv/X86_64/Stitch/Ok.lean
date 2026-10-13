module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Enc
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM-SIV's interleaved loop: the powers, and the whole loop

`setupG_ok`: the setup computes `H'`–`H'¹⁶` (`x · H'ᵏ = Hᵏ`) from `H` at
`r8`, as AES-GCM's from its hash subkey (`Proof.Gcm.X86_64.Stitch.setupG_ok`);
with the rest of the setup (`setupT_ok`), the state the loop starts from
(`Ready`). `dec_ok`: with those powers, whose products add up to `GHASH`
(`Proof.Gcm.X86_64.Stitch.finE`), the loop meets `DPost`.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (pows_ok const_ok ldrev_ok hInv_ok rev_eq)
open VG.Proof.Gcm.X86_64.Vpclmul (powersP_ok powers16P_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupG setup dec)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Stitch (finE)

theorem setupG_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setupG) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ (hk s₀) ^ (16 - 2 * k - l)) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r8 0 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide), BitVec.ofInt_natCast, BitVec.add_zero]; exact hp.h_in))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have hH : x * φ (s₄.xmm .xmm3) = φ (hk s₀) := by
    rw [t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide), BitVec.ofInt_natCast, BitVec.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (pows_ok s₄ (by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]) hH)
    fun s₇ ⟨hH2, hH3, hH4, o₇⟩ => ?_
  have o₁₇ := o₁₃.trans (o₄.trans o₇)
  rw [WP.block_append_iff]
  refine WP.mono (powersP_ok (H := hk s₀)
    (by rw [(o₂.trans (o₃.trans (o₄.trans o₇))).xmm _ (by decide), c₁, rev_eq])
    (by rw [(o₃.trans (o₄.trans o₇)).xmm _ (by decide), c₂])
    (by rw [o₇.xmm _ (by decide), hH]) hH2 hH3 hH4)
    fun s₈ ⟨l0, l1, _, pw8, _, g₈, m₈, rd₈, wr₈⟩ => ?_
  refine WP.mono (powers16P_ok l1 pw8) fun s₉ ⟨pw, F⟩ => ⟨fun l hl => ?_, fun l hl => ?_, pw,
    fun r hr => by rw [F.gpr, g₈ r hr, o₁₇.gpr r hr], by rw [F.mem, m₈, o₁₇.mem],
    by rw [F.rd, rd₈, o₁₇.rd], by rw [F.wr, wr₈, o₁₇.wr]⟩
  · rw [F.lane _ (by decide) l hl]; exact l0 l hl
  · rw [F.lane _ (by decide) l hl]; exact l1 l hl

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (setupG_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (setupT_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => ⟨_, hR, pw⟩

/-- The loop, on `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => decTail_ok hp hm (finE hpw) hR)

end VG.Proof.AesGcmSiv.X86_64.Stitch
