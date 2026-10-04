import VerifiedGarbage.Proof.AesCcm.X86_64.Header

/-!
# AES-CCM on x86-64: the associated data (`aadHead y`, `aad y`)

Untrusted: everything here is checked by Lean. `aadHead y` writes the
encoding of the length `a` of the associated data to `B`, copies its first
`min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`); `aad y`
does that and chains the rest of the associated data, padded, if there is
any associated data (`aad_ok`): the blocks `Proof.AesCcm.adataBlocks`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop minLen)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks)

/-- The encoding of the length of the associated data and its first bytes in `B`. -/
theorem aadHeadPre_ok {K W SP : Addr} {s : State} (E : Env K W SP s)
    {A : Addr} {a : Nat} (hA : Buf K W SP s A a) (ha0 : 0 < a)
    (h12 : s.gpr .r12 = A) (hbp : s.gpr .rbp = BitVec.ofNat 64 a) :
    WP isa (.seq header (.seq minLen (.seq (.block [.mov .rsi (.reg .r12), .mov .rdi (.reg .r15),
        .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm bO), .alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)])
        copyLoop))) s fun s₄ =>
      Env K W SP s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem ∧
      s₄.gpr .r12 = A + BitVec.ofNat 64 (headLen a) ∧ s₄.gpr .rbp = BitVec.ofNat 64 (a - headLen a) ∧
      bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a)) := by
  have ha := hA.lt
  have hh := Proof.AesCcm.hdrLen_le a
  have hh2 : 2 ≤ hdrLen a := by unfold hdrLen; split <;> [omega; split <;> omega]
  refine WP.seq (WP.mono (header_ok E ha0 ha hbp) fun s₁ ⟨E₁, hbx₁, hg₁, hrd₁, hwr₁, f₁, hB₁⟩ => ?_)
  have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₁ _ (by simp), hbp]
  refine WP.seq (WP.mono (minLen_ok s₁ hbx₁ hbp₁ (by omega) ha) fun s₂ ⟨hcx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = headLen a := by unfold headLen; omega
  rw [hn1] at hcx₂
  have hn1' : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega
  have E₂ : Env K W SP s₂ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  have h15 := E₂.r15
  obtain ⟨s₃, run₃, hm₃, hsi, hdi, hcx₃, h12₃, hbp₃, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .rsi (.reg .r12), .mov .rdi (.reg .r15), .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm bO),
        .alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)] s₂ = some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .rsi = A ∧ s₃.gpr .rdi = W + BitVec.ofNat 64 (32 + hdrLen a) ∧
      s₃.gpr .rcx = BitVec.ofNat 64 (headLen a) ∧ s₃.gpr .r12 = A + BitVec.ofNat 64 (headLen a) ∧
      s₃.gpr .rbp = BitVec.ofNat 64 (a - headLen a) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .r14], s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have h12₂ : s₂.gpr .r12 = A := by rw [hg₂ _ (by decide), hg₁ _ (by simp), h12]
    have hbx₂ : s₂.gpr .rbx = BitVec.ofNat 64 (hdrLen a) := by rw [hg₂ _ (by decide), hbx₁]
    have hbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₂ _ (by decide), hbp₁]
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, gpr_arithFlags, h12₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, hbx₂]
      rw [BitVec.add_assoc, show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ofNat_add_ofNat,
        Nat.add_comm (hdrLen a) 32]
    · simp [gpr_setReg, gpr_arithFlags, hcx₂]
    · simp [gpr_setReg, gpr_arithFlags, h12₂, hcx₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂, hcx₂]
      exact ofNat_sub hn1'.2.1 ha
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env K W SP s₃ := E₂.keep (fun r hr => hg₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₃ hwr₃
  have hA₃ := hA.of_eq (s' := s₃) (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])
  have dAB : (⟨A, headLen a⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (32 + hdrLen a), headLen a⟩ :=
    (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₃ A (W + BitVec.ofNat 64 (32 + hdrLen a)) (headLen a) :=
    ⟨hsi, hdi, hcx₃, hn1'.1, by omega, (hA₃.take hn1'.2.1).rd, E₃.perm.wC (by omega), dAB⟩
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  have E₄ : Env K W SP s₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)) hrd₄ hwr₄
  -- What was written.
  have fC : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains W (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← hm₂] at f₁; rw [← hm₃] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem A (headLen a) = (bytesAt s.mem A a).take (headLen a) := by
    rw [hm₃, hm₂, bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right
        (Lay.wSub (by decide))) (by omega), bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem A a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega
    rw [hm₄, show W + BitVec.ofNat 64 (32 + hdrLen a) = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by
        rw [add_ofNat_assoc], bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide),
      length_bytesAt, hAk, hm₃, hm₂, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega)
  exact ⟨E₄, by rw [hrd₄, hrd₃, hrd₂, hrd₁], by rw [hwr₄, hwr₃, hwr₂, hwr₁], fB,
    by rw [hg₄ _ (by decide) (by decide), h12₃], by rw [hg₄ _ (by decide) (by decide), hbp₃], hB₄⟩

/-- The first block of the associated data. -/
theorem aadHead_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : Addr} {a : Nat} (hA : Buf K W SP s A a) (ha0 : 0 < a)
    (h12 : s.gpr .r12 = A) (hbp : s.gpr .rbp = BitVec.ofNat 64 a) :
    WP isa (aadHead v.callee v.suffix y) s (@Absorbed K W SP s y (A + BitVec.ofNat 64 (headLen a)) (a - headLen a)
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a))])) := by
  refine seq_assoc4 (WP.seq (WP.mono (aadHeadPre_ok E hA ha0 h12 hbp)
    fun s₄ ⟨E₄, hrd₄, hwr₄, fB, h12₄, hbp₄, hB₄⟩ => ?_))
  have hRo₄ : s₄.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fB.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)]
    exact hRo
  have hY₄ : bytesAt s₄.mem (W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (W + BitVec.ofNat 64 y) 16 :=
    bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  have dK : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], (⟨K, 240⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok v L E₄ hR hRo₄ hy) fun s₅ ⟨E₅, g₅, hr₅, hw₅, f₅, h₅⟩ =>
    ⟨E₅, ?_, ?_, (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_), ?_, ?_, ?_⟩
  · rw [g₅ _ (by simp), h12₄]
  · rw [g₅ _ (by simp), hbp₄]
  · simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
  · rw [h₅, hY₄, hB₄, ctxCiph_frame fB dK hRb]
  · rw [hr₅, hrd₄]
  · rw [hw₅, hwr₄]

/-- What a piece of the MAC leaves: the environment, what it writes, the
MAC state `Y` at `W + y`, and the permissions. -/
structure MacStep {K W SP : Addr} (s : State) (y : Nat) (Y : List Byte) (s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (macR W SP y) s.mem s'.mem
  out : bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The associated data, formatted and chained. -/
theorem aad_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) (hA : Buf K W SP s A al) :
    WP isa (aad v.callee v.suffix y) s (@MacStep K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem A al)))) := by
  have h15 := E.r15
  have ha := hA.lt
  have r₁ := E.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hAp := S.aad
  have hal := S.alen
  obtain ⟨s₁, run₁, hm₁, h12, hbp, hzf, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .alu .test .rbp (.reg .rbp)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.zf = some (decide (al = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, gpr_arithFlags, hAp]
    · simp [gpr_setReg, gpr_arithFlags, hal]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hal, and_self_beq ha]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep hg₁ hrd₁ hwr₁
  have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₁]; exact S.rounds
  have hA₁ := hA.of_eq hrd₁ hwr₁
  refine WP.ite (decide (al = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    simp only [hm₁, adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : al ≠ 0 := of_decide_eq_false hf
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    refine WP.seq (WP.mono (aadHead_ok v L E₁ hR hRo₁ hy hA₁ (by omega) h12 hbp) fun s₂ A₂ => ?_)
    have hn1 : headLen al ≤ al := by unfold headLen; omega
    have hRo₂ : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
      rw [rounds_kept L hy A₂.frame, hRo₁]
    have hT := (hA.drop hn1).of_eq (s' := s₂) (by rw [A₂.rd, hrd₁]) (by rw [A₂.wr, hwr₁])
    refine WP.mono (absorbPad_ok v L A₂.env hR hRo₂ hy hT A₂.r12 A₂.rbp) fun s₃ A₃ =>
      ⟨A₃.env, by rw [← hm₁]; exact A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd, hrd₁], by rw [A₃.wr, A₂.wr, hwr₁]⟩
    rw [A₃.out, A₂.out, buf_kept hT (by omega) A₂.frame, ctxCiph_frame A₂.frame (k_macR L (by omega)) hRb,
      bytesAt_suffix _ _ hn1, hm₁, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

end VG.Proof.AesCcm.X86_64
