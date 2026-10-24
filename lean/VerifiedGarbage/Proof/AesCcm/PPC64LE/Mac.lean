module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.B0
import VerifiedGarbage.Proof.AesCcm.BytesAt
public import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Absorb

/-!
# AES-CCM on PPC64LE: the CBC-MAC (`mac y`)

Untrusted: everything here is checked by Lean. `mac y` chains `B₀`, the
blocks of the associated data (none if there is none) and those of the
payload padded into the MAC state at `W + y`, which then holds the chaining
of the formatted blocks (A.2) from a zero block (`mac_wp`), whose first
`t` bytes are the MAC (`Proof.AesCcm.mac_eq`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld)
open VG.Proof.Gather.PPC64LE (eval_zero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt bytesAt_suffix adataBlocks headLen)

/-- The blocks of the associated data, by `aadHead` and `absorbPad`. -/
theorem aad_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    (h18 : s.gpr .r18 = c.A) (h19 : s.gpr .r19 = BitVec.ofNat 64 c.al) :
    WP isa (.ite (.zero .d .r19) (.block []) (.seq (aadHead y) (absorbPad y))) s fun s' =>
      Absorbed c y s (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R)
        (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16) (adataBlocks (bytesAt s.mem c.A c.al))) s' := by
  have hl := L.al_lt
  have hA := L.bufA E.perm
  refine WP.ite (decide (c.al = 0)) (eval_zero h19 hl) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨PK.refl _, Frame.refl _ _, ?_⟩
    simp [adataBlocks, length_bytesAt, h0, Spec.Cmac.chain]
  · have h0 : c.al ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (aadHead_wp L E hy hA h18 h19 (by omega)) fun s₁ H => ?_)
    have hk : headLen c.al ≤ c.al := Nat.min_le_left _ _
    have hB := (hA.drop hk).of_eq H.abs.pk.rd H.abs.pk.wr
    refine WP.mono (absorbPad_wp L (E.of_pk H.abs.pk) hy hB H.r18 H.r19) fun s₂ A =>
      ⟨H.abs.pk.trans A.pk, H.abs.frame.trans A.frame, ?_⟩
    rw [A.out, H.abs.out, ciph_keep L hy H.abs.frame, buf_keep (hA.drop hk) hy H.abs.frame,
      bytesAt_suffix _ _ hk, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ite_false, List.singleton_append]

/-- `Yᵣ`, the chaining of the formatted blocks from a zero block, at `W + y`. -/
theorem mac_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (mac y) s (Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Ccm.zeros 16)
        (Spec.Ccm.format c.tl nonce (bytesAt s.mem c.A c.al) (bytesAt s.mem c.D c.n)))) := by
  have hn15 : nonce.length ≤ 15 := by have := L.h13; omega
  unfold mac
  refine WP.seq (wp_ld (a := c.W + BitVec.ofNat 64 216) (by decide) (by decide) (by rw [E.r14]; rfl)
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_)
  refine wp_ld (a := c.W + BitVec.ofNat 64 224) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14]; rfl) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have E₂ := E.of_pk pk₂
  have r18₂ : s₂.gpr .r18 = c.A := by rw [u₂.other _ (by decide), u₁.gpr, S.aad]
  have r19₂ : s₂.gpr .r19 = BitVec.ofNat 64 c.al := by rw [u₂.gpr, u₁.mem, S.alen]
  refine WP.seq (WP.mono (b0_wp L E₂ (by rw [m₂]; exact S) r19₂ hnl (by rw [m₂]; exact hc0) hy)
    fun s₃ ⟨A₃, k₃⟩ => ?_)
  have f₃ : Frame (macR c.W y) s.mem s₃.mem := by have := A₃.frame; rwa [m₂] at this
  have o₃ := A₃.out
  rw [m₂] at o₃
  refine WP.seq (WP.mono (aad_wp L (E.of_pk (pk₂.trans A₃.pk)) hy (by rw [k₃ .r18 (by simp), r18₂])
    (by rw [k₃ .r19 (by simp), r19₂])) fun s₄ A₄ => ?_)
  refine WP.seq (wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK s s₆ := pk₂.trans (A₃.pk.trans (A₄.pk.trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆))))
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have f₄ : Frame (macR c.W y) s.mem s₄.mem := f₃.trans A₄.frame
  have hD := L.bufD (E.of_pk pk₆).perm
  refine WP.mono (absorbPad_wp L (E.of_pk pk₆) hy hD
    (by rw [u₆.other _ (by decide), u₅.gpr, (pk₂.trans (A₃.pk.trans A₄.pk)).gpr .r22 (by decide), E.r22])
    (by rw [u₆.gpr, u₅.other _ (by decide), (pk₂.trans (A₃.pk.trans A₄.pk)).gpr .r23 (by decide), E.r23]))
    fun s₇ A₇ => ?_
  have o₇ := A₇.out
  have f₇ := A₇.frame
  rw [m₆] at o₇ f₇
  refine ⟨pk₆.trans A₇.pk, f₄.trans f₇, ?_⟩
  have hD₀ := L.bufD E.perm
  have hA₀ := L.bufA E.perm
  rw [o₇, A₄.out, o₃, ciph_keep L hy f₄, ciph_keep L hy f₃, buf_keep hD₀ hy f₄, buf_keep hA₀ hy f₃,
    Proof.AesCcm.format_eq c.tl hn15, Proof.Cmac.chain_append, Proof.Cmac.chain_append, length_bytesAt,
    length_bytesAt]

end VG.Proof.AesCcm.PPC64LE
