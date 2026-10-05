import VerifiedGarbage.Proof.AesCcm.X86_64.Aad

/-!
# AES-CCM on x86-64: the MAC (`mac y`)

Untrusted: everything here is checked by Lean. `mac y` chains `B₀`, the
formatted associated data and the payload padded into the MAC state at
`W + y`, from a zero block: CBC-MAC of the formatted blocks (`mac_ok`), whose
first `t` bytes are CCM's MAC (`Proof.AesCcm.mac_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok (v : UpdateImpl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : Buf K W SP s A al) (hD : Buf K W SP s D n) :
    WP isa (mac v.callee y) s (@MacStep K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem A al) (bytesAt s.mem D n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega
  refine WP.seq (WP.mono (b0_ok v L E S hR hnl h7 h13 ht4 ht16 hte hA.lt hn hc0 hy)
    fun s₁ ⟨E₁, f₁, h₁, hrd₁, hwr₁⟩ => ?_)
  -- The slots, which the pieces of the MAC keep.
  have kept : ∀ {m m' : Mem}, Frame (macR W SP y) m m' → Slots W R N A D nl al n tl m → Slots W R N A D nl al n tl m' :=
    fun hf hs => by
      have k : ∀ d, 160 ≤ d → d + 8 ≤ 240 → _ := fun d h₁ h₂ =>
        hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rcases hy with rfl | rfl
            · exact L.w_w (.inr (by omega)) (by omega) (by decide)
            · exact L.w_w (.inr (by omega)) (by omega) (by decide)
          · exact L.w_w (.inr (by omega)) (by omega) (by decide)
          · exact L.w_w (.inl (by omega)) (by omega) (by decide)
          · exact (L.stk_w' (by omega)).symm) (by decide)
      exact ⟨by rw [k 232 (by decide) (by decide)]; exact hs.rounds, by rw [k 160 (by decide) (by decide)]; exact hs.nonce,
        by rw [k 168 (by decide) (by decide)]; exact hs.nlen, by rw [k 176 (by decide) (by decide)]; exact hs.aad,
        by rw [k 184 (by decide) (by decide)]; exact hs.alen, by rw [k 192 (by decide) (by decide)]; exact hs.data,
        by rw [k 200 (by decide) (by decide)]; exact hs.len, by rw [k 208 (by decide) (by decide)]; exact hs.tl⟩
  have S₁ := kept f₁ S
  refine WP.seq (WP.mono (aad_ok v L E₁ S₁ hR hy (hA.of_eq hrd₁ hwr₁)) fun s₂ M₂ => ?_)
  have S₂ := kept M₂.frame S₁
  have E₂ := M₂.env
  have h15 := E₂.r15
  have r₁ := E₂.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E₂.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have hd₂ := S₂.data
  have hl₂ := S₂.len
  obtain ⟨s₃, run₃, hm₃, h12, hbp, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] s₂ = some s₃ ∧
      s₃.mem = s₂.mem ∧ s₃.gpr .r12 = D ∧ s₃.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hd₂]
    · simp [gpr_setReg, hl₂]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env K W SP s₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hRo₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₃]; exact S₂.rounds
  have rd₃ : s₃.rd = s.rd := by rw [hrd₃, M₂.rd, hrd₁]
  have wr₃ : s₃.wr = s.wr := by rw [hwr₃, M₂.wr, hwr₁]
  refine WP.mono (absorbPad_ok v L E₃ hR hRo₃ hy (hD.of_eq rd₃ wr₃) h12 hbp) fun s₄ A₄ => ?_
  have f₃ : Frame (macR W SP y) s.mem s₃.mem := by rw [hm₃]; exact f₁.trans M₂.frame
  have hk := k_macR L hy16
  refine ⟨A₄.env, f₃.trans A₄.frame, ?_, by rw [A₄.rd, rd₃], by rw [A₄.wr, wr₃]⟩
  have hl : nonce.length ≤ 15 := by omega
  have f₂ : Frame (macR W SP y) s.mem s₂.mem := f₁.trans M₂.frame
  rw [A₄.out, hm₃, M₂.out, h₁, ctxCiph_frame f₂ hk hRb, ctxCiph_frame f₁ hk hRb, buf_kept hD hy16 f₂,
    buf_kept hA hy16 f₁, format_eq tl hl, length_bytesAt, length_bytesAt, Proof.Cmac.chain_append,
    Proof.Cmac.chain_append]

end VG.Proof.AesCcm.X86_64
