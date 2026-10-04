import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks

/-!
# AES-CCM on x86-64: the tag (`tag y`)

Untrusted: everything here is checked by Lean. `tag y` makes `Ctr₀` at
`W + 64` and calls `vg_aes_ctr32` on the MAC state at `W + y`, one block:
the state XORed with `CIPH_K(Ctr₀)`, CCM's keystream from `Ctr₀` (`tag_ok`),
whose first `t` bytes are the MAC encrypted (`Proof.AesCcm.take_xorFrom_zero`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The arguments of the call: `Ctr₀` at `W + 64`. -/
theorem tagArgs_ok {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov32 .rax (imm 0)] : List Instr) ++ ctrAt ++ ([.mov .rdi (.reg .r13)] : List Instr) ++
      ptr .rdx .r15 c1O ++ ptr .rcx .r15 y ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) s fun s₃ =>
      Env K W SP s₃ ∧ CtrCall s₃ K (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 384) R 1 ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14], s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  have h15 := E.r15
  have h13' := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₁, run₁, hm₁, hsi₁, hax₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov32 .rax (imm 0)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rax = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  obtain ⟨s₂, run₂, f₂, hc₂, hg₂, hrd₂, hwr₂⟩ :=
    ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (Nat.pow_pos (by decide)) hax₁
  have E₂ : Env K W SP s₂ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have h15₂ := E₂.r15
  obtain ⟨s₃, run₃, hm₃, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      ([.mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 y ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s₂ =
        some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .rdi = K ∧ s₃.gpr .rsi = BitVec.ofNat 64 R ∧ s₃.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      s₃.gpr .rcx = W + BitVec.ofNat 64 y ∧ s₃.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₃.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .rbp, .r12, .r14], s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [h15₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, E₂.r13]
    · simp [gpr_setReg, hg₂ .rsi (by decide) (by decide) (by decide), hsi₁]
    · simp [gpr_setReg, h15₂]
    · simp [gpr_setReg, h15₂, imm_eq hy']
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₃ : Env K W SP s₃ := E₂.keep (fun r hr => hg₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₃ hwr₃
  refine WP.of_runBlock ⟨s₃, ?_, ?_⟩
  · simp only [List.append_assoc]
    rw [runBlock_append, run₁, Option.bind_some, runBlock_append, run₂, Option.bind_some]
    simpa only [List.append_assoc] using run₃
  have hq := srcW (s := s₃) L E₃.perm (t := y) (k := 16 * 1) (by omega)
  have hqc : (⟨W + BitVec.ofNat 64 y, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16 * 1⟩ := L.k_w.sub_right (Lay.wSub (by omega))
  refine ⟨E₃, cargs L E₃ hR (c := 64) (by decide) hq hqc hqk (E₃.perm.wC (d := y) (n := 16 * 1) (by omega))
    hdi hsi hdx hcx hr8 hr9, fun r hr => ?_, by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁],
    by rw [hm₃, ← hm₁]; exact f₂, by rw [hm₃]; exact hc₂⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have h3 : r ∈ [Reg.r13, .r15, .rsp, .rbx, .rbp, .r12, .r14] := by rcases hr with rfl | rfl | rfl | rfl <;> simp
  have ha : r ≠ .rax := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hc : r ≠ .rcx := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hd : r ≠ .rdx := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hs : r ≠ .rsi := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  rw [hg₃ r h3, hg₂ r ha hc hd, hg₁ r ha hs]

/-- The MAC state at `W + y` XORed with `CIPH_K(Ctr₀)`. -/
theorem tag_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (tag v.callee y) s fun s' => Env K W SP s' ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩,
        below SP 16] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 0 (bytesAt s.mem (W + BitVec.ofNat 64 y) 16) := by
  refine WP.seq (WP.mono (tagArgs_ok L E hR hRo h7 h13 hc0 hy) fun s₃ ⟨E₃, C₃, g₃, hrd₃, hwr₃, f₃, hc₃⟩ => ?_)
  refine WP.mono (ctr_call v C₃) fun s₄ h => ?_
  have hqc : (⟨W + BitVec.ofNat 64 y, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hK₃ : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have hY₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (W + BitVec.ofNat 64 y) 16 :=
    bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hqc) (by decide)
  refine ⟨E₃.of_saved h.saved h.rd h.wr, fun r hr => ?_, by rw [h.rd, hrd₃], by rw [h.wr, hwr₃], ?_, ?_⟩
  · have hr' : r ∈ calleeSaved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [h.saved r hr', g₃ r hr]
  · have f₄ := h.frame
    rw [E₃.rsp] at f₄
    refine (f₃.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (f₄.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨below SP 16, by simp, below8_sub SP⟩
  · have hc := ctr32_ccm (m := s₃.mem) (m' := s₄.mem) (K := K) (C := W + BitVec.ofNat 64 64)
      (D := W + BitVec.ofNat 64 y) (R := R) (nonce := nonce) (by omega) (j := 0) (k := 1)
      (fun i hi => by
        rw [show i = 0 by omega, Nat.zero_add]
        show Spec.Gcm.ofBytes _ = _
        rw [hc₃]) h.out
    rw [Nat.mul_one] at hc
    rw [hc, hK₃, hY₃]

end VG.Proof.AesCcm.X86_64
