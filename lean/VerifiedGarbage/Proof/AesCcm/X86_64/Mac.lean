module

import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
public import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesCcm.X86_64.Header
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Proof.AesCcm.X86_64.Env
public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
public import VerifiedGarbage.Spec.Ccm

/-! ### `AesCcm.X86_64.Aad`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86_64.B0`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86-64: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `b0 y` computes the flags
`64 [a > 0] + 4 (t − 2) + q − 1` (which is A.2.1's for an even `t`), writes
`B₀` to `W + 32` from `Ctr₀`, zeroes the MAC state at `W + y` and chains
`B₀` into it (`b0_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B`, the
working space of the functions called and the stack below `SP`. -/
abbrev macR (W SP : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 16]

omit fp in
theorem flags_val {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    ((BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega, ite_false, Nat.zero_add]; omega
  · simp only [h, ite_false, show al > 0 by omega, ite_true]; omega

omit fp in
/-- `B₀` in `B` and the MAC state at `W + y` zeroed. -/
theorem b0Pre_ok {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov32 .rcx (imm 14), .alu .sub .rcx (.mem (at_ .r15 nlenO)),
        .alu .add .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)])
      (.seq (.ite .e (.block []) (.block [.alu .add .rax (imm 64)]))
      (.block (([.mov .rcx (.mem (at_ .r15 c0O)), .mov .rdx (.mem (at_ .r15 (c0O + 8))),
        .mov .rsi (.mem (at_ .r15 lenO)), .store (at_ .r15 bO) .rcx, .store8 (at_ .r15 bO) .rax, .bswap .rsi,
        .alu .or .rsi (.reg .rdx), .store (at_ .r15 (bO + 8)) .rsi] : List Instr) ++ zero16 y)))) s fun s' =>
      Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
  have h15 := E.r15
  obtain rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain rn := E.perm.wR (show 168 + 8 ≤ 2560 by decide)
  obtain ra := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
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
      omega_arith
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hal', and_self_beq hal]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- `64 [a > 0]`.
  obtain hite : WP isa (.ite .e (.block []) (.block [.alu .add .rax (imm 64)])) s₁ fun s₂ =>
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
        omega_arith
      · intro r a b; simp [gpr_setReg, a, hg₁ r a b]
      · exact hrd₁
      · exact hwr₁
  refine WP.seq (WP.mono hite fun s₂ ⟨hm₂, hax₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  obtain E₂ : Env K W SP s₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  -- `B₀`, and the state zeroed.
  have h15₂ := E₂.r15
  obtain hRo : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₂]; exact S.rounds
  obtain hlen : s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by rw [hm₂]; exact S.len
  obtain c₁ := E₂.perm.wR (show 48 + 8 ≤ 2560 by decide)
  obtain c₂ := E₂.perm.wR (show 56 + 8 ≤ 2560 by decide)
  obtain c₃ := E₂.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain b₁ := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
  obtain b₂ := E₂.perm.wW (show 32 + 1 ≤ 2560 by decide)
  obtain b₃ := E₂.perm.wW (show 40 + 8 ≤ 2560 by decide)
  obtain y₁ := E₂.perm.wW (show y + 8 ≤ 2560 by omega_arith)
  obtain y₂ := E₂.perm.wW (show y + 8 + 8 ≤ 2560 by omega_arith)
  obtain hy' : y < 2 ^ 31 := by omega_arith
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
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  obtain E₃ : Env K W SP s₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide) (by decide)) hrd₃ hwr₃
  -- What the block wrote.
  obtain e40 : W + BitVec.ofNat 64 40 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  obtain ey8 : W + BitVec.ofNat 64 (y + 8) = W + BitVec.ofNat 64 y + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  obtain cB : ∀ d k, 32 ≤ d → d + k ≤ 48 → (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega_arith) (by decide)
  obtain cY : ∀ d k, y ≤ d → d + k ≤ y + 16 → (⟨W + BitVec.ofNat 64 y, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega_arith) (by omega_arith)
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((s₂.mem.writeW (W + BitVec.ofNat 64 32) (s₂.mem.readW (W + BitVec.ofNat 64 48) 64)).writeW
      (W + BitVec.ofNat 64 32) ((s₂.gpr .rax).setWidth 8 : Byte)).writeW (W + BitVec.ofNat 64 40)
      (bswap64 (BitVec.ofNat 64 n) ||| s₂.mem.readW (W + BitVec.ofNat 64 56) 64) := ⟨_, rfl⟩
  rw [← hmB] at hm₃
  obtain fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₂.mem mB := by
    rw [hmB]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))
  obtain fY : Frame [⟨W + BitVec.ofNat 64 y, 16⟩] mB s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cY y 8 (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (cY (y + 8) 8 (by omega_arith) (by omega_arith))
  obtain dYB : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain f₃ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s₃.mem := by
    rw [← hm₂]
    exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  refine ⟨E₃, by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂], f₃, ?_⟩
  constructor
  · -- The state was zeroed.
    rw [hm₃, ey8, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · -- `B₀`.
    obtain hB₁ : bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 = bytesAt mB (W + BitVec.ofNat 64 32) 16 :=
      bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB) (by decide)
    obtain hlo : le8 (s₂.mem.readW (W + BitVec.ofNat 64 48) 64) =
        BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
      obtain h8 : bytesAt s₂.mem (W + BitVec.ofNat 64 48) 8 = (bytesAt s₂.mem (W + BitVec.ofNat 64 48) 16).take 8 := by
        rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rw [Proof.Cmac.le8_readW, h8, hm₂, hc0, ctrBlock_take8 (by omega_arith)]
    obtain hhi : le8 (s₂.mem.readW (W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      obtain e56 : W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
      rw [Proof.Cmac.le8_readW, ← hc0, hm₂, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    obtain hb : ((s₂.gpr .rax).setWidth 8 : Byte) = Spec.Ccm.flags tl (15 - nonce.length) al := by
      rw [hax₂, hnl, flags_val ht4 ht16 hte h7 h13]
    obtain hB : bytesAt mB (W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
      rw [hmB, e40, bytesAt_writeW64_at _ _ _ (by decide) (by decide), bytesAt_writeW8_base _ _ _ (by decide)
        (by decide), bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hb,
        ctr_or (by omega_arith) (by omega_arith) hhi (by rw [hnl]; exact hn), ctrBlock_drop8 (by omega_arith)]
      simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons]
      obtain hX : (Spec.Ccm.flags tl (15 - nonce.length) al ::
          (List.take 7 nonce ++ List.drop 8 (bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16))).length ≤ 8 + 8 := by
        simp [length_bytesAt]; omega_arith
      rw [List.take_append_of_le_length (by simp; omega_arith), List.take_of_length_le (by simp; omega_arith),
        List.drop_eq_nil_of_le hX, List.append_nil, ← List.append_assoc, List.take_append_drop]
    rw [hB₁, hB]

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee y) s fun s' => Env K W SP s' ∧ Frame (macR W SP y) s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n] ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine seq_assoc3 (WP.seq (WP.mono (b0Pre_ok L E S hnl h7 h13 ht4 ht16 hte hal hn hc0 hy)
    fun s₃ ⟨E₃, rd₃, wr₃, f₃, hz, hB⟩ => ?_))
  obtain hRo₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by omega_using [hy])) (by decide) (by omega_using [hy])) (by decide)]
    exact S.rounds
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok v L E₃ hR hRo₃ hy) fun s₄ ⟨E₄, _, hrd₄, hwr₄, f₄, h₄⟩ =>
    ⟨E₄, ?_, ?_, by rw [hrd₄, rd₃], by rw [hwr₄, wr₃]⟩
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
  · rw [h₄, hz, hB, ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Lay.wSub (by omega_using [hy]))) hRb]

end VG.Proof.AesCcm.X86_64

end

end

/-! ### `AesCcm.X86_64.Absorb`, which only this module used -/

section

/-!
# AES-CCM on x86-64: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`
(`absorbWhole_ok`), then its last `len mod 16` bytes copied into the zeroed
block `B` (`absorbTail_ok`); together, the blocks of the padded string
(`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

theorem sub_mac {W SP : Addr} {y : Nat} {r : Region} (hr : r ∈ macR W SP y) :
    ∃ r' ∈ macR W SP y, Region.Sub r r' := ⟨r, hr, fun _ h => h⟩

/-- What `absorbPad`'s pieces keep: the environment, the registers holding
the string, and what they write. -/
structure Absorbed {K W SP : Addr} (s : State) (y : Nat) (P : Addr) (len : Nat) (Y : List Byte) (s' : State) :
    Prop where
  env : Env K W SP s'
  r12 : s'.gpr .r12 = P
  rbp : s'.gpr .rbp = BitVec.ofNat 64 len
  frame : Frame (macR W SP y) s.mem s'.mem
  out : bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The whole blocks of the string. -/
theorem absorbWhole_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (.seq (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)])
        (.ite .e (.block []) (.seq (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) (callUpdate v.callee))))
      s (@Absorbed _ K W SP s y P len
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16)))))) := by
  have hl := hP.lt
  obtain ⟨s₁, run₁, hm₁, hr8, hzf, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ s₁.zf = some (decide (len / 16 = 0)) ∧
      (∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hbp, shr4 len hl]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hbp, shr4 len hl, and_self_beq (show len / 16 < 2 ^ 64 by omega_arith)]
    · intro r a; simp [gpr_setReg, gpr_setFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (len / 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len / 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hg₁ _ (by decide), h12], by rw [hg₁ _ (by decide), hbp],
      by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    rw [hm₁, h0, Nat.mul_zero, List.take_zero]; rfl
  · have h0 : len / 16 ≠ 0 := of_decide_eq_false hf
    have h15 := E₁.r15
    have h13 := E₁.r13
    have r₁ := E₁.perm.wR (show 232 + 8 ≤ 2560 by decide)
    have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₁]; exact hRo
    have hy' : y < 2 ^ 31 := by omega_arith
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hdx, hcx, hr8₂, hr9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (updArgs y ++ [.mov .rcx (.reg .r12)]) s₁ = some s₂ ∧ s₂.mem = s₁.mem ∧
        s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 y ∧
        s₂.gpr .rcx = P ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 384 ∧
        (∀ r ∈ [Reg.r12, .rbp, .r13, .r15, .rsp], s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · simp [gpr_setReg, h13]
      · simp [gpr_setReg, hRo₁]
      · simp [gpr_setReg, h15, imm_eq hy']
      · simp [gpr_setReg, hg₁ _ (by decide : Reg.r12 ≠ .r8), h12]
      · simp [gpr_setReg, hr8]
      · simp [gpr_setReg, h15]
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
      all_goals rfl
    have E₂ : Env K W SP s₂ := E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by simp)) hrd₂ hwr₂
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
    have hq := srcBuf ((hP.take hb).of_eq (s' := s₂) (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁]))
    have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ :=
      (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega_arith))
    refine WP.mono (upd_call v (uargs L E₂ hR (by omega_arith) hq hqy (by omega_arith) hdi hsi hdx hcx hr8₂ hr9))
      fun s₃ h => ⟨E₂.of_saved h.saved h.rd h.wr, ?_, ?_, ?_, ?_, by rw [h.rd, hrd₂, hrd₁], by rw [h.wr, hwr₂, hwr₁]⟩
    · rw [h.saved _ (by decide), hg₂ _ (by simp), hg₁ _ (by decide), h12]
    · rw [h.saved _ (by decide), hg₂ _ (by simp), hg₁ _ (by decide), hbp]
    · rw [← hm₁, ← hm₂]
      exact h.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_mac (by simp)
        · exact sub_mac (by simp)
        · exact ⟨below SP 16, by simp, by rw [E₂.rsp]; exact fun _ h => h⟩
    · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, hm₂, hm₁, ← bytesAt_prefix _ _ hb]
      rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- The last bytes of the string, padded with zeros in `B`. -/
theorem absorbTail_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (.seq (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block [])
          (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
              ptr .rdi .r15 bO))
            (.seq copyLoop (updBlock v.callee y)))))
      s (@Absorbed _ K W SP s y P len
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
          (tailBlocks (bytesAt s.mem P len)))) := by
  have hl := hP.lt
  have hxl := length_bytesAt s.mem P len
  obtain ⟨s₁, run₁, hm₁, hcx, hzf, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ s₁.zf = some (decide (len % 16 = 0)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hbp, and15', toNat_ofNat_of_lt hl]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, hbp, and15', toNat_ofNat_of_lt hl,
        and_self_beq (show len % 16 < 2 ^ 64 by omega_arith)]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (len % 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hg₁ _ (by decide), h12], by rw [hg₁ _ (by decide), hbp],
      by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    simp only [hm₁, tailBlocks, hxl, h0, ↓reduceIte]; rfl
  · have h0 : len % 16 ≠ 0 := of_decide_eq_false hf
    have h15 := E₁.r15
    have w₁ := E₁.perm.wW (show 32 + 8 ≤ 2560 by decide)
    have w₂ := E₁.perm.wW (show 40 + 8 ≤ 2560 by decide)
    obtain ⟨s₂, run₂, hm₂, hsi, hdi, hcx₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
          ptr .rdi .r15 bO) s₁ = some s₂ ∧
        s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 40)
          (0 : BitVec 64) ∧
        s₂.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) ∧ s₂.gpr .rdi = W + BitVec.ofNat 64 32 ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧
        (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by crun [zero16, h15, w₁, w₂, add_ofNat_assoc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, mem_arithFlags]; rfl
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hg₁ _ (by decide : Reg.rbp ≠ .rcx),
          hg₁ _ (by decide : Reg.r12 ≠ .rcx), hbp, h12, hcx]
        rw [ofNat_sub (by omega_arith) hl, BitVec.add_comm, show len - len % 16 = 16 * (len / 16) by omega_arith]
      · simp [gpr_setReg, h15]
      · simp [gpr_setReg, hcx]
      · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : Env K W SP s₂ := E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
    have hb : 16 * (len / 16) + len % 16 = len := by omega_arith
    have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega_arith)).of_eq (s' := s₂)
      (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁])
    have dTB : (⟨P + BitVec.ofNat 64 (16 * (len / 16)), len % 16⟩ : Region).Disjoint
        ⟨W + BitVec.ofNat 64 32, len % 16⟩ := hT.w.sub_right (Lay.wSub (by omega_arith))
    have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (W + BitVec.ofNat 64 32) (len % 16) :=
      ⟨hsi, hdi, hcx₂, by omega_arith, by omega_arith, hT.rd, E₂.perm.wC (by omega_arith), dTB⟩
    refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
    have E₃ : Env K W SP s₃ := E₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
    -- What was written.
    have e40 : W + BitVec.ofNat 64 40 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
    have fZ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₁.mem s₂.mem := by
      rw [hm₂]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 32) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 40) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))
    have fC : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₂.mem s₃.mem := by
      rw [hm₃]
      exact writeBytes_frame _ _ _ (by
        rw [length_bytesAt]
        exact Offset.contains W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega_arith) (by decide))
    have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem := by rw [← hm₁]; exact fZ.trans fC
    have dK : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], (⟨K, 240⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))
    have hRo₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
      rw [fB.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)]
      exact hRo
    have hY₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (W + BitVec.ofNat 64 y) 16 :=
      bytesAt_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    have hB₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
      have hs₁ : bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
          (bytesAt s.mem P len).drop (16 * (len / 16)) := by
        rw [bytesAt_frame fZ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hT.w.sub_right (Lay.wSub (by decide))) (by omega_arith),
          hm₁, show len % 16 = len - 16 * (len / 16) by omega_arith, bytesAt_suffix _ _ (by omega_arith)]
      have hz : bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
        rw [hm₂, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
      rw [hm₃, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega_arith) (by decide), hs₁, hz,
        List.length_drop, hxl]
      congr 1
      simp only [Spec.Cmac.zeros, Spec.Ccm.zeros, List.drop_replicate]
      congr 1
      omega_arith
    have rw₄ : ∀ s₄ : State, s₄.rd = s₃.rd → s₄.wr = s₃.wr → s₄.rd = s.rd ∧ s₄.wr = s.wr := fun s₄ a b =>
      ⟨by rw [a, hrd₃, hrd₂, hrd₁], by rw [b, hwr₃, hwr₂, hwr₁]⟩
    refine WP.mono (updBlock_ok v L E₃ hR hRo₃ hy) fun s₄ ⟨E₄, g₄, hr₄, hw₄, f₄, h₄⟩ =>
      ⟨E₄, ?_, ?_, ?_, ?_, (rw₄ s₄ hr₄ hw₄).1, (rw₄ s₄ hr₄ hw₄).2⟩
    · rw [g₄ _ (by simp), hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide),
        hg₁ _ (by decide), h12]
    · rw [g₄ _ (by simp), hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide),
        hg₁ _ (by decide), hbp]
    · refine ((fB.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
      · simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
    · have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
      rw [h₄, hY₃, hB₃, ctxCiph_frame fB dK hRb]
      simp only [tailBlocks, hxl, h0, ↓reduceIte]

/-- Keeps `[232, 240)`, where the rounds are. -/
theorem rounds_kept {K W SP : Addr} (L : Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (hf : Frame (macR W SP y) m m') : m'.readW (W + BitVec.ofNat 64 232) 64 = m.readW (W + BitVec.ofNat 64 232) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by have := tailBytes_le; have := scratchBytes_le; omega)
    · exact (L.stk_w' (by decide)).symm) (by decide)

/-- A buffer missing `W` and the stack below `SP` keeps its bytes. -/
theorem buf_kept {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (macR W SP y) m m') : bytesAt m' P len = bytesAt m P len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by have := tailBytes_le; have := scratchBytes_le; omega))
    · exact hP.stk.symm) (by have := hP.lt; omega_arith)

theorem k_macR {K W SP : Addr} (L : Lay K W SP) {y : Nat} (hy : y + 16 ≤ 2560) :
    ∀ r ∈ macR W SP y, (⟨K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Lay.wSub hy)
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by have := tailBytes_le; have := scratchBytes_le; omega))
  · exact L.stk_k.symm

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (absorbPad v.callee y) s (@Absorbed _ K W SP s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  refine seq_assoc (WP.seq (WP.mono (absorbWhole_ok v L E hR hRo hy hP h12 hbp) fun s₁ A₁ => ?_))
  have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [rounds_kept L hy A₁.frame, hRo]
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (absorbTail_ok v L A₁.env hR hRo₁ hy (hP.of_eq A₁.rd A₁.wr) A₁.r12 A₁.rbp) fun s₂ A₂ =>
    ⟨A₂.env, A₂.r12, A₂.rbp, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  rw [A₂.out, A₁.out, buf_kept hP (by omega_arith) A₁.frame, ctxCiph_frame A₁.frame (k_macR L (by omega_arith)) hRb,
    ← Proof.Cmac.chain_append, Proof.AesCcm.blocks_pad16, length_bytesAt, tailBlocks, length_bytesAt]

end VG.Proof.AesCcm.X86_64

end

end


/-!
# AES-CCM on x86-64: the associated data (`aadHead y`, `aad y`)

Untrusted: everything here is checked by Lean. `aadHead y` writes the
encoding of the length `a` of the associated data to `B`, copies its first
`min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`); `aad y`
does that and chains the rest of the associated data, padded, if there is
any associated data (`aad_ok`): the blocks `Proof.AesCcm.adataBlocks`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop minLen)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks)

omit fp in
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
  have hh2 : 2 ≤ hdrLen a := by unfold hdrLen; split <;> [omega_arith; split <;> omega_arith]
  refine WP.seq (WP.mono (header_ok E ha0 ha hbp) fun s₁ ⟨E₁, hbx₁, hg₁, hrd₁, hwr₁, f₁, hB₁⟩ => ?_)
  have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₁ _ (by simp), hbp]
  refine WP.seq (WP.mono (minLen_ok s₁ hbx₁ hbp₁ (by omega_arith) ha) fun s₂ ⟨hcx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = headLen a := by unfold headLen; omega_arith
  rw [hn1] at hcx₂
  have hn1' : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega_arith
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
    (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right (Lay.wSub (by omega_arith))
  have lp : LoopPre s₃ A (W + BitVec.ofNat 64 (32 + hdrLen a)) (headLen a) :=
    ⟨hsi, hdi, hcx₃, hn1'.1, by omega_arith, (hA₃.take hn1'.2.1).rd, E₃.perm.wC (by omega_arith), dAB⟩
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  have E₄ : Env K W SP s₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)) hrd₄ hwr₄
  -- What was written.
  have fC : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains W (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega_arith) (by omega_arith)
        (by decide))
  have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← hm₂] at f₁; rw [← hm₃] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem A (headLen a) = (bytesAt s.mem A a).take (headLen a) := by
    rw [hm₃, hm₂, bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right
        (Lay.wSub (by decide))) (by omega_arith), bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem A a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega_arith
    rw [hm₄, show W + BitVec.ofNat 64 (32 + hdrLen a) = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by
        rw [add_ofNat_assoc], bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega_arith) (by decide),
      length_bytesAt, hAk, hm₃, hm₂, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega_arith) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega_arith), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega_arith]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega_arith)
  exact ⟨E₄, by rw [hrd₄, hrd₃, hrd₂, hrd₁], by rw [hwr₄, hwr₃, hwr₂, hwr₁], fB,
    by rw [hg₄ _ (by decide) (by decide), h12₃], by rw [hg₄ _ (by decide) (by decide), hbp₃], hB₄⟩

/-- The first block of the associated data. -/
theorem aadHead_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : Addr} {a : Nat} (hA : Buf K W SP s A a) (ha0 : 0 < a)
    (h12 : s.gpr .r12 = A) (hbp : s.gpr .rbp = BitVec.ofNat 64 a) :
    WP isa (aadHead v.callee y) s (@Absorbed _ K W SP s y (A + BitVec.ofNat 64 (headLen a)) (a - headLen a)
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
theorem aad_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) (hA : Buf K W SP s A al) :
    WP isa (aad v.callee y) s (@MacStep _ K W SP s y
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
    refine WP.seq (WP.mono (aadHead_ok v L E₁ hR hRo₁ hy hA₁ (by omega_arith) h12 hbp) fun s₂ A₂ => ?_)
    have hn1 : headLen al ≤ al := by unfold headLen; omega_arith
    have hRo₂ : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
      rw [rounds_kept L hy A₂.frame, hRo₁]
    have hT := (hA.drop hn1).of_eq (s' := s₂) (by rw [A₂.rd, hrd₁]) (by rw [A₂.wr, hwr₁])
    refine WP.mono (absorbPad_ok v L A₂.env hR hRo₂ hy hT A₂.r12 A₂.rbp) fun s₃ A₃ =>
      ⟨A₃.env, by rw [← hm₁]; exact A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd, hrd₁], by rw [A₃.wr, A₂.wr, hwr₁]⟩
    rw [A₃.out, A₂.out, buf_kept hT (by omega_arith) A₂.frame, ctxCiph_frame A₂.frame (k_macR L (by omega_arith)) hRb,
      bytesAt_suffix _ _ hn1, hm₁, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

end VG.Proof.AesCcm.X86_64

end

end

/-!
# AES-CCM on x86-64: the MAC (`mac y`)

Untrusted: everything here is checked by Lean. `mac y` chains `B₀`, the
formatted associated data and the payload padded into the MAC state at
`W + y`, from a zero block: CBC-MAC of the formatted blocks (`mac_ok`), whose
first `t` bytes are CCM's MAC (`Proof.AesCcm.mac_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : Buf K W SP s A al) (hD : Buf K W SP s D n) :
    WP isa (mac v.callee y) s (@MacStep _ K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem A al) (bytesAt s.mem D n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega_using [hy]
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
            · exact L.w_w (.inr (by omega_arith)) (by omega_using [h₂]) (by decide)
            · exact L.w_w (.inr (by omega_arith)) (by omega_using [h₂]) (by decide)
          · exact L.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
          · exact L.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by have := tailBytes_le; have := scratchBytes_le; omega)
          · exact (L.stk_w' (by omega_using [h₂])).symm) (by decide)
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
  have hl : nonce.length ≤ 15 := by omega_using [hnl, h13]
  have f₂ : Frame (macR W SP y) s.mem s₂.mem := f₁.trans M₂.frame
  rw [A₄.out, hm₃, M₂.out, h₁, ctxCiph_frame f₂ hk hRb, ctxCiph_frame f₁ hk hRb, buf_kept hD hy16 f₂,
    buf_kept hA hy16 f₁, format_eq tl hl, length_bytesAt, length_bytesAt, Proof.Cmac.chain_append,
    Proof.Cmac.chain_append]

end VG.Proof.AesCcm.X86_64
