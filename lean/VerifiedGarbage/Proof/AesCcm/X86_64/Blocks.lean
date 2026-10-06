import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs

/-!
# AES-CCM on x86-64: counter blocks and chaining a block

Untrusted: everything here is checked by Lean. `ctrAt` makes `Ctrᵢ` at
`W + 64` from `Ctr₀` (`ctrAt_ok`); `updBlock y` chains the block `B` at
`W + 32` into the MAC state at `W + y` (`updBlock_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)
open VG.Proof.CmacAes.Stream.X86_64 (upd_call)

/-! ## `ctrAt` -/

/-- `Ctrᵢ` at `W + 64`, for `i` in `rax`. -/
theorem ctrAt_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (h13 : nonce.length ≤ 13) (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) (hax : s.gpr .rax = BitVec.ofNat 64 i) :
    ∃ s', runBlock isa ctrAt s = some s' ∧ Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h15 := E.r15
  have w₁ := E.perm.wW (show 64 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 56 + 8 ≤ 2560 by decide)
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 64) (s.mem.readW (W + BitVec.ofNat 64 48) 64)).writeW
        (W + BitVec.ofNat 64 72) (bswap64 (BitVec.ofNat 64 i) ||| s.mem.readW (W + BitVec.ofNat 64 56) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by crun [ctrAt, h15, w₁, w₂, r₁, r₂], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, hax]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  have e72 : W + BitVec.ofNat 64 72 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have e56 : W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  refine ⟨s', run, ?_, ?_, hg, hrd, hwr⟩
  · rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (d := 64) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains W (d := 72) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))
  · have h8 : bytesAt s.mem (W + BitVec.ofNat 64 48) 8 = (bytesAt s.mem (W + BitVec.ofNat 64 48) 16).take 8 := by
      rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hlo : le8 (s.mem.readW (W + BitVec.ofNat 64 48) 64) = (Spec.Ccm.ctrBlock nonce i).take 8 := by
      rw [Proof.Cmac.le8_readW, h8, hc0, ctrBlock_take8 h7, ctrBlock_take8 h7]
    have hhi : le8 (s.mem.readW (W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    rw [hm, e72, Proof.Cmac.bytesAt_store2, hlo, ctr_or h7 h13 hhi hi, List.take_append_drop]

/-! ## Chaining `B` -/

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok (v : UpdateImpl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock v.callee y) s fun s' => Env K W SP s' ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
          [bytesAt s.mem (W + BitVec.ofNat 64 32) 16] := by
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rdi = K ∧ s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₁.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s₁.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₁.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .rbp, .r12, .r14], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, imm_eq hy']
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hq := srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨W + BitVec.ofNat 64 32, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (upd_call v (uargs L E₁ hR (by omega) hq hqy (by decide) hdi hsi hdx hcx hr8 hr9))
    fun s₂ h => ⟨E₁.of_saved h.saved h.rd h.wr, fun r hr => ?_, by rw [h.rd, hrd₁], by rw [h.wr, hwr₁], ?_, ?_⟩
  · rw [h.saved r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      hg₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp)]
  · rw [← hm₁]; simpa [E₁.rsp] using h.frame
  · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
      (Proof.Cmac.bytesAt_length _ _ _), hm₁]
    rfl

end VG.Proof.AesCcm.X86_64
