import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks

/-!
# AES-CCM on x86-64: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `b0 y` computes the flags
`64 [a > 0] + 4 (t − 2) + q − 1` (which is A.2.1's for an even `t`), writes
`B₀` to `W + 32` from `Ctr₀`, zeroes the MAC state at `W + y` and chains
`B₀` into it (`b0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B`, the
working space of the functions called and the stack below `SP`. -/
abbrev macR (W SP : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16]

theorem flags_val {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    ((BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega, ite_false, Nat.zero_add]; omega
  · simp only [h, ite_false, show al > 0 by omega, ite_true]; omega

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee v.suffix y) s fun s' => Env K W SP s' ∧ Frame (macR W SP y) s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n] := by
  have h15 := E.r15
  have rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have rn := E.perm.wR (show 168 + 8 ≤ 2560 by decide)
  have ra := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have htl := S.tl
  have hnl' := S.nlen
  have hal' := S.alen
  -- The flags, without `64 [a > 0]`, and ZF for `a = 0`.
  obtain ⟨s₁, run₁, hm₁, hax₁, hzf₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov32 .rcx (imm 14), .alu .sub .rcx (.mem (at_ .r15 nlenO)),
        .alu .add .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rax = BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl)) ∧
      s₁.zf = some (decide (al = 0)) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, rt, rn, ra], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, htl, hnl']
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, setWidth_imm]
      omega
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hal', and_self_beq hal]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- `64 [a > 0]`.
  have hite : WP isa (.ite .e (.block []) (.block [.alu .add .rax (imm 64)])) s₁ fun s₂ =>
      s₂.mem = s.mem ∧ s₂.gpr .rax = BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine WP.ite (decide (al = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : al = 0 := of_decide_eq_true ht
      exact WP.of_runBlock ⟨s₁, rfl, hm₁, by rw [hax₁, h0]; rfl, hg₁, hrd₁, hwr₁⟩
    · have h0 : al ≠ 0 := of_decide_eq_false hf
      refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
      · exact hm₁
      · simp only [gpr_setReg, ite_true, hax₁, h0, ite_false]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, imm_eq (show 64 < 2 ^ 31 by decide)]
        omega
      · intro r a b; simp [gpr_setReg, a, hg₁ r a b]
      · exact hrd₁
      · exact hwr₁
  refine WP.seq (WP.mono hite fun s₂ ⟨hm₂, hax₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have E₂ : Env K W SP s₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  -- `B₀`, and the state zeroed.
  have h15₂ := E₂.r15
  have hRo : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₂]; exact S.rounds
  have hlen : s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by rw [hm₂]; exact S.len
  have c₁ := E₂.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have c₂ := E₂.perm.wR (show 56 + 8 ≤ 2560 by decide)
  have c₃ := E₂.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have b₁ := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have b₂ := E₂.perm.wW (show 32 + 1 ≤ 2560 by decide)
  have b₃ := E₂.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have y₁ := E₂.perm.wW (show y + 8 ≤ 2560 by omega)
  have y₂ := E₂.perm.wW (show y + 8 + 8 ≤ 2560 by omega)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₃, run₃, hm₃, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      ([.mov .rcx (.mem (at_ .r15 c0O)), .mov .rdx (.mem (at_ .r15 (c0O + 8))), .mov .rsi (.mem (at_ .r15 lenO)),
        .store (at_ .r15 bO) .rcx, .store8 (at_ .r15 bO) .rax, .bswap .rsi, .alu .or .rsi (.reg .rdx),
        .store (at_ .r15 (bO + 8)) .rsi] ++ zero16 y) s₂ = some s₃ ∧
      s₃.mem = (((((s₂.mem.writeW (W + BitVec.ofNat 64 32) (s₂.mem.readW (W + BitVec.ofNat 64 48) 64)).writeW
        (W + BitVec.ofNat 64 32) ((s₂.gpr .rax).setWidth 8 : Byte)).writeW (W + BitVec.ofNat 64 40)
        (bswap64 (BitVec.ofNat 64 n) ||| s₂.mem.readW (W + BitVec.ofNat 64 56) 64)).writeW (W + BitVec.ofNat 64 y)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 (y + 8)) (0 : BitVec 64)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [zero16, h15₂, c₁, c₂, c₃, b₁, b₂, b₃, y₁, y₂, imm_eq hy', add_ofNat_assoc], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hlen,
        add_ofNat_assoc, setWidth_imm, Nat.reduceMod]
      rfl
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env K W SP s₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide) (by decide)) hrd₃ hwr₃
  -- What the block wrote.
  have e40 : W + BitVec.ofNat 64 40 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have ey8 : W + BitVec.ofNat 64 (y + 8) = W + BitVec.ofNat 64 y + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 → (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  have cY : ∀ d k, y ≤ d → d + k ≤ y + 16 → (⟨W + BitVec.ofNat 64 y, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega) (by omega)
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((s₂.mem.writeW (W + BitVec.ofNat 64 32) (s₂.mem.readW (W + BitVec.ofNat 64 48) 64)).writeW
      (W + BitVec.ofNat 64 32) ((s₂.gpr .rax).setWidth 8 : Byte)).writeW (W + BitVec.ofNat 64 40)
      (bswap64 (BitVec.ofNat 64 n) ||| s₂.mem.readW (W + BitVec.ofNat 64 56) 64) := ⟨_, rfl⟩
  rw [← hmB] at hm₃
  have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₂.mem mB := by
    rw [hmB]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))
  have fY : Frame [⟨W + BitVec.ofNat 64 y, 16⟩] mB s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cY y 8 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (cY (y + 8) 8 (by omega) (by omega))
  have dYB : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have f₃ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s₃.mem := by
    rw [← hm₂]
    exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  have kept : ∀ d k, (232 ≤ d ∧ d + k ≤ 240) → s₃.mem.readW (W + BitVec.ofNat 64 d) (8 * k) =
      s.mem.readW (W + BitVec.ofNat 64 d) (8 * k) := by
    intro d k hd
    refine f₃.readW (r := ⟨W + BitVec.ofNat 64 d, k⟩) (by simpa using Region.contains_self _ _) (fun r hr => ?_)
      (by simp; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by omega)
  have hRo₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [kept 232 8 ⟨Nat.le_refl _, by decide⟩]; exact S.rounds
  refine WP.mono (updBlock_ok v L E₃ hR hRo₃ hy) fun s₄ ⟨E₄, f₄, h₄⟩ => ⟨E₄, ?_, ?_⟩
  · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · -- The state was zeroed.
    have hz : bytesAt s₃.mem (W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 := by
      rw [hm₃, ey8, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
    -- `B₀`.
    have hB₁ : bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 = bytesAt mB (W + BitVec.ofNat 64 32) 16 :=
      bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB) (by decide)
    have hlo : le8 (s₂.mem.readW (W + BitVec.ofNat 64 48) 64) =
        BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
      have h8 : bytesAt s₂.mem (W + BitVec.ofNat 64 48) 8 = (bytesAt s₂.mem (W + BitVec.ofNat 64 48) 16).take 8 := by
        rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rw [Proof.Cmac.le8_readW, h8, hm₂, hc0, ctrBlock_take8 (by omega)]
    have hhi : le8 (s₂.mem.readW (W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      have e56 : W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
      rw [Proof.Cmac.le8_readW, ← hc0, hm₂, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hb : ((s₂.gpr .rax).setWidth 8 : Byte) = Spec.Ccm.flags tl (15 - nonce.length) al := by
      rw [hax₂, hnl, flags_val ht4 ht16 hte h7 h13]
    have hB : bytesAt mB (W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
      rw [hmB, e40, bytesAt_writeW64_at _ _ _ (by decide) (by decide), bytesAt_writeW8_base _ _ _ (by decide)
        (by decide), bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hb,
        ctr_or (by omega) (by omega) hhi (by rw [hnl]; exact hn), ctrBlock_drop8 (by omega)]
      simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons]
      have hX : (Spec.Ccm.flags tl (15 - nonce.length) al ::
          (List.take 7 nonce ++ List.drop 8 (bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16))).length ≤ 8 + 8 := by
        simp [length_bytesAt]; omega
      rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega),
        List.drop_eq_nil_of_le hX, List.append_nil, ← List.append_assoc, List.take_append_drop]
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [h₄, hz, hB₁, hB, ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Lay.wSub (by omega))) hRb]

end VG.Proof.AesCcm.X86_64
