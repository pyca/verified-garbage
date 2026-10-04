import VerifiedGarbage.Proof.AesCcm.X86_64.Run

/-!
# AES-CCM on x86-64: `Ctr₀` (`ctrs`)

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte and copies the nonce
after it: `Ctr₀` (`ctrs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)

theorem sub_low_byte {nl : Nat} (h : nl ≤ 14) :
    ((BitVec.ofNat 64 14 - BitVec.ofNat 64 nl).setWidth 8 : Byte) = BitVec.ofNat 8 (15 - nl - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `Ctr₀`, from the nonce `N` of `nl` bytes. -/
theorem ctrs_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hN : Buf K W SP s N nl) (h7 : 7 ≤ nl)
    (h13 : nl ≤ 13) :
    WP isa ctrs s fun s' => Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N nl) 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h15 := E.r15
  have w₁ := E.perm.wW (show 48 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 56 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 48 + 1 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 168 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 160 + 8 ≤ 2560 by decide)
  have hnl := S.nlen
  have hNp := S.nonce
  obtain ⟨s₁, run₁, hm₁, hsi, hdi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov .rsi (.mem (at_ .r15 nonceO)), .mov .rcx (.mem (at_ .r15 nlenO))] ++ zero16 c0O ++
        [.mov32 .rax (imm 14), .alu .sub .rax (.reg .rcx), .store8 (at_ .r15 c0O) .rax] ++ ptr .rdi .r15 (c0O + 1)) s =
        some s₁ ∧
      s₁.mem = ((s.mem.writeW (W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 56)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 48) (BitVec.ofNat 8 (15 - nl - 1)) ∧
      s₁.gpr .rsi = N ∧ s₁.gpr .rdi = W + BitVec.ofNat 64 49 ∧ s₁.gpr .rcx = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [zero16, h15, w₁, w₂, w₃, r₁, r₂, add_ofNat_assoc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]
      rw [hnl, sub_low_byte (show nl ≤ 14 by omega)]
      rfl
    · simp [gpr_setReg, hNp]
    · simp [gpr_setReg]
    · simp [gpr_setReg, hnl]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dNW : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 49, nl⟩ := hN.w.sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₁ N (W + BitVec.ofNat 64 49) nl :=
    ⟨hsi, hdi, hcx, by omega, by omega, by rw [hrd₁, hwr₁]; exact hN.rd, E₁.perm.wC (by omega), dNW⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
  have hfz : Frame [⟨W + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (d := 48) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains W (d := 56) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains W (d := 48) (n := 1) (e := 48) (k := 16) (by decide) (by decide) (by decide))
  have hNs : bytesAt s₁.mem N nl = bytesAt s.mem N nl :=
    bytesAt_frame hfz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hN.w.sub_right (Lay.wSub (by decide))) (by omega)
  refine ⟨E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂, ?_, ?_,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · refine hfz.trans ?_
    rw [hm₂]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains W (d := 49) (n := nl) (e := 48) (k := 16) (by decide) (by omega) (by decide))
  · -- The bytes of the block.
    have e56 : W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
    have hz : bytesAt s₁.mem (W + BitVec.ofNat 64 48) 16 = BitVec.ofNat 8 (15 - nl - 1) :: Spec.Ccm.zeros 15 := by
      rw [hm₁, bytesAt_writeW8_base _ _ _ (by decide) (by decide), e56, Proof.Cmac.bytesAt_store2,
        Proof.Cmac.le8_zero]
      rfl
    have hl := length_bytesAt s.mem N nl
    rw [hm₂, show W + BitVec.ofNat 64 49 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 by rw [add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hz, hNs,
      Spec.Ccm.ctrBlock, hl, be_zero, show 1 + nl = nl + 1 by omega]
    simp only [Spec.Ccm.zeros, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_replicate,
      List.cons_append, List.nil_append]

end VG.Proof.AesCcm.X86_64
