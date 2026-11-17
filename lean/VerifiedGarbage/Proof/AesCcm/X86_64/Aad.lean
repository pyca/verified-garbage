module
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesCcm.X86_64.B0
import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
public import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesCcm.X86_64.Header

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
