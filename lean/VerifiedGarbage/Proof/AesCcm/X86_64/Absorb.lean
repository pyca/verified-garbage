import VerifiedGarbage.Proof.AesCcm.X86_64.B0

/-!
# AES-CCM on x86-64: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`
(`absorbWhole_ok`), then its last `len mod 16` bytes copied into the zeroed
block `B` (`absorbTail_ok`); together, the blocks of the padded string
(`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (upd_call)

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
theorem absorbWhole_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (.seq (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)])
        (.ite .e (.block []) (.seq (.block (updArgs y ++ [.mov .rcx (.reg .r12)])) (callUpdate v.callee v.suffix))))
      s (@Absorbed K W SP s y P len
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
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hbp, shr4 len hl, and_self_beq (show len / 16 < 2 ^ 64 by omega)]
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
    have hy' : y < 2 ^ 31 := by omega
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
      (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega))
    refine WP.mono (upd_call v _ (uargs L E₂ hR (by omega) hq hqy (by omega) hdi hsi hdx hcx hr8₂ hr9))
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
theorem absorbTail_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (.seq (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block [])
          (.seq (.block (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
              ptr .rdi .r15 bO))
            (.seq copyLoop (updBlock v.callee v.suffix y)))))
      s (@Absorbed K W SP s y P len
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
        and_self_beq (show len % 16 < 2 ^ 64 by omega)]
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
        rw [ofNat_sub (by omega) hl, BitVec.add_comm, show len - len % 16 = 16 * (len / 16) by omega]
      · simp [gpr_setReg, h15]
      · simp [gpr_setReg, hcx]
      · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : Env K W SP s₂ := E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
    have hb : 16 * (len / 16) + len % 16 = len := by omega
    have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega)).of_eq (s' := s₂)
      (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁])
    have dTB : (⟨P + BitVec.ofNat 64 (16 * (len / 16)), len % 16⟩ : Region).Disjoint
        ⟨W + BitVec.ofNat 64 32, len % 16⟩ := hT.w.sub_right (Lay.wSub (by omega))
    have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (W + BitVec.ofNat 64 32) (len % 16) :=
      ⟨hsi, hdi, hcx₂, by omega, by omega, hT.rd, E₂.perm.wC (by omega), dTB⟩
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
        exact Offset.contains W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide))
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
            simp only [List.mem_singleton] at hr; subst hr; exact hT.w.sub_right (Lay.wSub (by decide))) (by omega),
          hm₁, show len % 16 = len - 16 * (len / 16) by omega, bytesAt_suffix _ _ (by omega)]
      have hz : bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
        rw [hm₂, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
      rw [hm₃, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega) (by decide), hs₁, hz,
        List.length_drop, hxl]
      congr 1
      simp only [Spec.Cmac.zeros, Spec.Ccm.zeros, List.drop_replicate]
      congr 1
      omega
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
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide)

/-- A buffer missing `W` and the stack below `SP` keeps its bytes. -/
theorem buf_kept {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (macR W SP y) m m') : bytesAt m' P len = bytesAt m P len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem k_macR {K W SP : Addr} (L : Lay K W SP) {y : Nat} (hy : y + 16 ≤ 2560) :
    ∀ r ∈ macR W SP y, (⟨K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Lay.wSub hy)
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (absorbPad v.callee v.suffix y) s (@Absorbed K W SP s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  refine seq_assoc (WP.seq (WP.mono (absorbWhole_ok v L E hR hRo hy hP h12 hbp) fun s₁ A₁ => ?_))
  have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [rounds_kept L hy A₁.frame, hRo]
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (absorbTail_ok v L A₁.env hR hRo₁ hy (hP.of_eq A₁.rd A₁.wr) A₁.r12 A₁.rbp) fun s₂ A₂ =>
    ⟨A₂.env, A₂.r12, A₂.rbp, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  rw [A₂.out, A₁.out, buf_kept hP (by omega) A₁.frame, ctxCiph_frame A₁.frame (k_macR L (by omega)) hRb,
    ← Proof.Cmac.chain_append, Proof.AesCcm.blocks_pad16, length_bytesAt, tailBlocks, length_bytesAt]

end VG.Proof.AesCcm.X86_64
