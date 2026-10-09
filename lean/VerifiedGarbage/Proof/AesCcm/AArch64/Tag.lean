import VerifiedGarbage.Proof.AesCcm.AArch64.Mac

/-!
# AES-CCM on AArch64: the MAC encrypted (`tag y`)

Untrusted: everything here is checked by Lean. `tag y` copies `Ctr₀` to
`W + 64` (`tagArgs_ok`) and calls `vg_aes_ctr32` on the MAC at `W + y`: it
XORs in `CIPH_K(Ctr₀)`, CCM's keystream from `Ctr₀` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (CtrCall ctr_call Others)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesCcm (xorFrom)

/-- The arguments of the call: `Ctr₀` at `W + 64`. -/
theorem tagArgs_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (([imm .x9 0] : List Instr) ++ ctrAt ++ ctrArgs ++ ([ptr .x3 .x19 y, imm .x4 1] : List Instr))) s
      fun s₃ => Env c s₃ ∧
        CtrCall s₃ c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 y) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
        Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] s s₃ ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
        Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
        bytesAt s₃.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  have h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  have h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  have E₁ : Env c t₁ := E.others (rs := [.x9]) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]) (by decide)
    (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  have h9 : t₁.gpr .x9 = BitVec.ofNat 64 0 := by rw [← ht₁]; simp [gpr_write]
  have hm₁ : t₁.mem = s.mem := by rw [← ht₁]; rfl
  have hg₁ : Others [.x9] s t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  refine WP.block_append (WP.mono (ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := 0) (Nat.pow_pos (by decide))
    h9) fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hy' : y < 4096 := by omega_arith
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [ctrArgs, hy'], rfl⟩ fun t₃ ht₃ => ?_
  have hg₃ : Others [.x0, .x1, .x2, .x3, .x4, .x5] t₂ t₃ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; rw [← ht₃]; simp [gpr_write, hr]
  have E₃ : Env c t₃ := E₂.others hg₃ (by decide) (by rw [← ht₃]; rfl) (by rw [← ht₃]; rfl) (by rw [← ht₃]; rfl)
  have hm₃ : t₃.mem = t₂.mem := by rw [← ht₃]; rfl
  refine ⟨E₃, cargsW L E₃ (o := 64) (d := y) (by decide) (by omega_arith) (by omega_arith) ?_ ?_ ?_ ?_ ?_ ?_, ?_,
    by rw [← ht₃]; simp only [rd_write]; rw [rd₂, ← ht₁]; rfl,
    by rw [← ht₃]; simp only [wr_write]; rw [wr₂, ← ht₁]; rfl,
    by rw [hm₃, ← hm₁]; exact f₂, by rw [hm₃]; exact hc₂⟩
  · rw [← ht₃]; simp [gpr_write, E₂.x21]
  · rw [← ht₃]; simp [gpr_write, E₂.x22]
  · rw [← ht₃]; simp [gpr_write, E₂.x19]
  · rw [← ht₃]; simp [gpr_write, E₂.x19]
  · rw [← ht₃]; simp [gpr_write]
  · rw [← ht₃]; simp [gpr_write, E₂.x19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
      hg₂ r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      hg₁ r (by simp [hr.2.2.2.2.2.2.1])]

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`. -/
theorem tag_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (tag v.callee y) s fun s' => Env c s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩]
        s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 0 (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16) := by
  refine WP.seq (WP.mono (tagArgs_ok L E hnl hc0 hy) fun t₃ ⟨E₃, C₃, _, rd₃, wr₃, f₃, hc₃⟩ => ?_)
  refine WP.mono (ctr_call v C₃) fun t₄ h => ⟨E₃.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, rd₃],
    by rw [h.wr, wr₃], ?_, ?_⟩
  · refine (f₃.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 0) (by rw [hnl]; have := L.h13; omega_arith) (fun i hi => by
      rw [show i = 0 by omega_arith, Nat.add_zero]
      show Spec.Gcm.ofBytes _ = _
      rw [hc₃]) h.out
    rw [Nat.mul_one] at hx
    have hK : Spec.Ccm.ctxCiph t₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
      unfold Spec.Ccm.ctxCiph
      rw [Proof.AesGcm.AArch64.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega_arith)]
    have hY : bytesAt t₃.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
      Proof.AesGcm.AArch64.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    rw [hx, hK, hY]

end VG.Proof.AesCcm.AArch64
