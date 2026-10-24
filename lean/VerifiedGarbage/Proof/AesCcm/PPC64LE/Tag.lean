module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.B0
public import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Cmac.Frame
public import Mathlib.Data.List.Induction
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Callee
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-CCM on PPC64LE: the MAC encrypted (`tag y`)

Untrusted: everything here is checked by Lean. `tag y` copies `Ctr₀` to
`W + 64` (`ctrAt` with `i = 0`) and calls `vg_aes_ctr32` on the MAC at
`W + y`: it XORs in `CIPH_K(Ctr₀)`, CCM's keystream from `Ctr₀`
(`tag_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li)
open VG.Proof.AesCtr.PPC64LE (ctr_call)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (xorFrom)

/-- What `tag y` and a call of `vg_aes_ctr32` from a counter block leave. -/
abbrev ctrR (W : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩]

theorem tag_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (tag y) s fun s' => PK s s' ∧ (∀ r ∈ [Reg.r18, .r19, .r20, .r21], s'.gpr r = s.gpr r) ∧
      Frame (ctrR c.W y) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 0 (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16) := by
  unfold tag
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine ctrAt_wp L (E.of_pk (PK.ofUpd u₁)) hnl (by rw [u₁.mem]; exact hc0) (i := 0)
    (Nat.pow_pos (by decide : 0 < 256)) u₁.gpr
    fun s₂ pk₂ k₂ f₂ hc₂ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ =>
    wp_addi (by decide) (by decide) fun s₆ u₆ => wp_addi (by decide) (by omega) fun s₇ u₇ =>
    wp_li (by decide) fun s₈ u₈ => WP.block_nil ?_
  have pk₈ : PK s s₈ := (PK.ofUpd u₁).trans (pk₂.trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))))
  have E₈ := E.of_pk pk₈
  have m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have C := cargsW L E₈ (o := 64) (d := y) (by decide) (by omega) (by omega)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, (PK.ofUpd u₁ |>.trans pk₂).gpr .r16 (by decide), E.r16])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .r17 (by decide), E.r17])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .r14 (by decide), E.r14]; rfl)
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .r14 (by decide), E.r14])
    (by rw [u₈.gpr])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .r14 (by decide), E.r14]; rfl)
  refine WP.mono (ctr_call C) fun s₉ h => ⟨pk₈.trans (PK.ofSaved h.rd h.wr h.sp h.saved), fun r hr => ?_, ?_, ?_⟩
  · have h1 : r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r8 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [h.saved _ hp, u₈.other _ h1.2.2.2.2.2.1, u₇.other _ h1.2.2.2.2.1, u₆.other _ h1.2.2.2.1,
      u₅.other _ h1.2.2.1, u₄.other _ h1.2.1, u₃.other _ h1.1,
      k₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp [h]),
      u₁.other _ h1.2.2.2.2.2.2]
  · rw [u₁.mem] at f₂
    rw [← m₈] at f₂
    refine (f₂.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · have hx := Proof.AesCcm.ctr32_ccm (nonce := nonce) (k := 1) (j := 0) (by have := L.h13; omega)
      (fun i hi => by
        rw [show i = 0 by omega, Nat.add_zero]
        show Spec.Gcm.ofBytes _ = _
        rw [m₈, hc₂]) h.out
    rw [Nat.mul_one] at hx
    rw [u₁.mem] at f₂
    have hK : Spec.Ccm.ctxCiph s₈.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
      unfold Spec.Ccm.ctxCiph
      rw [m₈, Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega)]
    have hY : bytesAt s₈.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 := by
      rw [m₈]
      exact Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    rw [hx, hK, hY]

end VG.Proof.AesCcm.PPC64LE
