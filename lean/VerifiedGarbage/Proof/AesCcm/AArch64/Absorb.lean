import VerifiedGarbage.Proof.AesCcm.AArch64.B0

/-!
# AES-CCM on AArch64: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`, on none if
there are none (`absWhole_ok`), then its last `len mod 16` bytes copied into
the zeroed block `B` (`absTail_ok`); together, the blocks of the padded
string (`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok loopRegs Others add_ofNat_assoc eval_zero ofNat_sub lsr_ofNat
  lsl4_ofNat and15 toNat_ofNat_of_lt)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeBytes_base bytesAt_prefix bytesAt_suffix)

/-- The arguments of the call for the whole blocks. -/
theorem absArgs_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr}
    {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P) (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) s fun s₁ =>
      Proof.CmacAes.Stream.AArch64.UArgs s₁ c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R
        (len / 16) ∧ Env c s₁ ∧ Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hl := hP.lt
  obtain ⟨s₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ [mov .x3 .x23, .lsr .x .x4 .x24 4]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .x0 = c.K ∧ s₁.gpr .x1 = BitVec.ofNat 64 c.R ∧ s₁.gpr .x2 = c.W + BitVec.ofNat 64 y ∧
      s₁.gpr .x3 = P ∧ s₁.gpr .x4 = BitVec.ofNat 64 (len / 16) ∧ s₁.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hy' : y < 4096 := by omega
    refine ⟨_, by carun [updArgs, hy'], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x22]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h23]
    · simp [gpr_write, h24, lsr_ofNat len 4 hl]
    · simp [gpr_write, E.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have E₁ : Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hq := ((hP.take hb).of_eq (s' := s₁) rd₁ wr₁).src
  have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ :=
    (hP.take hb).wd (by omega)
  exact WP.of_runBlock ⟨s₁, run₁, uargs L E₁ (by omega) hq hqy (by omega) x0 x1 x2 x3 x4 x5, E₁, hg₁, hm₁,
    rd₁, wr₁⟩

/-- What `absorbPad`'s pieces leave. -/
structure Absorbed (c : Cx) (y : Nat) (P : Addr) (len : Nat) (s : State) (Y : List Byte) (s' : State) :
    Prop where
  env : Env c s'
  x23 : s'.gpr .x23 = P
  x24 : s'.gpr .x24 = BitVec.ofNat 64 len
  frame : Frame (macR c.W y) s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The whole blocks of the string. -/
theorem absWhole_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.seq (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) (callUpdate v.callee)) s
      (Absorbed c y P len s
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16)))))) := by
  refine WP.seq (WP.mono (absArgs_ok L E hy hP h23 h24) fun s₁ ⟨U, E₁, hg₁, hm₁, rd₁, wr₁⟩ => ?_)
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  refine WP.mono (upd_call v v.callee.name U) fun s₂ h =>
    ⟨E₁.of_saved h.saved h.sp h.rd h.wr, ?_, ?_, ?_, ?_, by rw [h.rd, rd₁], by rw [h.wr, wr₁]⟩
  · rw [h.saved _ (by decide) (by decide), hg₁ _ (by decide), h23]
  · rw [h.saved _ (by decide) (by decide), hg₁ _ (by decide), h24]
  · rw [← hm₁]
    exact h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, hm₁, ← bytesAt_prefix _ _ hb]
    rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- The last `len mod 16` (not 0) bytes, padded with zeros in `B`. -/
theorem absTailPre_ok {c : Cx} {s : State} (E : Env c s)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) (h13 : s.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h0 : len % 16 ≠ 0) :
    WP isa (.seq (.block (zero16 bO ++ ([.lsr .x .x10 .x24 4, .lsl .x .x10 .x10 4, .add .x .x12 .x23 .x10,
        ptr .x11 .x19 bO] : List Instr))) copyLoop) s fun s₃ =>
      Env c s₃ ∧ s₃.gpr .x23 = P ∧ s₃.gpr .x24 = BitVec.ofNat 64 len ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
  have hl := hP.lt
  have hxl := length_bytesAt s.mem P len
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, x11₂, x12₂, x13₂, hg₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      (zero16 bO ++ [.lsr .x .x10 .x24 4, .lsl .x .x10 .x10 4, .add .x .x12 .x23 .x10, ptr .x11 .x19 bO]) s =
        some s₂ ∧
      s₂.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧
      s₂.gpr .x11 = c.W + BitVec.ofNat 64 32 ∧ s₂.gpr .x12 = P + BitVec.ofNat 64 (16 * (len / 16)) ∧
      s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧
      Others [.x9, .x10, .x11, .x12] s s₂ ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h23, h24, lsr_ofNat len 4 hl, lsl4_ofNat]
    · simp [gpr_write, h13]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : Env c s₂ := E.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hb : 16 * (len / 16) + len % 16 = len := by omega
  have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega)).of_eq (s' := s₂) rd₂ wr₂
  have dTB : (⟨P + BitVec.ofNat 64 (16 * (len / 16)), len % 16⟩ : Region).Disjoint
      ⟨c.W + BitVec.ofNat 64 32, len % 16⟩ := hT.wd (by omega)
  have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (c.W + BitVec.ofNat 64 32) (len % 16) :=
    ⟨by omega, hT.rd, E₂.perm.wC (by omega), dTB⟩
  refine WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ (by omega) lp) fun s₃ ⟨hm₃, _, _, hg₃, sp₃, rd₃, wr₃⟩ => ?_
  have E₃ : Env c s₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  -- What was written.
  have e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have fZ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 32) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 40) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))
  have fC : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s₂.mem s₃.mem := by
    rw [hm₃]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains c.W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide))
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem := fZ.trans fC
  have hB₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 =
      (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
    have hs₁ : bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
        (bytesAt s.mem P len).drop (16 * (len / 16)) := by
      rw [Proof.AesGcm.AArch64.bytesAt_frame fZ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hT.wd (by decide)) (by omega),
        show len % 16 = len - 16 * (len / 16) by omega, bytesAt_suffix _ _ (by omega)]
    have hz : bytesAt s₂.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      rw [hm₂, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
    rw [hm₃, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega) (by decide), hs₁, hz,
      List.length_drop, hxl]
    congr 1
    simp only [Spec.Cmac.zeros, Spec.Ccm.zeros, List.drop_replicate]
    congr 1
    omega
  refine ⟨E₃, by rw [hg₃ _ (by decide), hg₂ _ (by decide), h23], by rw [hg₃ _ (by decide), hg₂ _ (by decide), h24],
    by rw [rd₃, rd₂], by rw [wr₃, wr₂], fB, hB₃⟩

/-- The last `len mod 16` (not 0) bytes, padded with zeros in `B`, chained. -/
theorem absTail_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) (h13 : s.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h0 : len % 16 ≠ 0) :
    WP isa (absTail v.callee y) s (Absorbed c y P len s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (tailBlocks (bytesAt s.mem P len)))) := by
  have hxl := length_bytesAt s.mem P len
  refine WP.assoc (WP.seq (WP.mono (absTailPre_ok E hP h23 h24 h13 h0)
    fun s₃ ⟨E₃, x23₃, x24₃, rd₃, wr₃, fB, hB₃⟩ => ?_))
  have hY₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  refine WP.mono (updBlock_ok v L E₃ hy) fun s₄ ⟨E₄, g₄, hr₄, hw₄, f₄, h₄⟩ =>
    ⟨E₄, ?_, ?_, ?_, ?_, by rw [hr₄, rd₃], by rw [hw₄, wr₃]⟩
  · rw [g₄ _ (by simp), x23₃]
  · rw [g₄ _ (by simp), x24₃]
  · refine ((fB.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₄, hY₃, hB₃, ciph_macR L (y := y) (by omega) (fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)]
    simp only [tailBlocks, hxl, h0, ↓reduceIte]

/-- The length of the last bytes, `len mod 16`. -/
theorem absMask_ok {s : State} {len : Nat} (hl : len < 2 ^ 64)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.block [imm .x9 15, .logic .and .x .x13 .x24 .x9]) s fun s₂ =>
      s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧ Others [.x9, .x13] s s₂ ∧ s₂.mem = s.mem ∧
      s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain ⟨s₂, run₂, x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [imm .x9 15, .logic .and .x .x13 .x24 .x9]
      s = some s₂ ∧ s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧ Others [.x9, .x13] s s₂ ∧ s₂.mem = s.mem ∧
      s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h24]
      rw [and15, toNat_ofNat_of_lt hl]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  exact WP.of_runBlock ⟨s₂, run₂, x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (absorbPad v.callee y) s (Absorbed c y P len s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  have hl := hP.lt
  refine WP.assoc (WP.seq (WP.mono (absWhole_ok v L E hy hP h23 h24) fun s₁ A₁ => ?_))
  refine WP.seq (WP.mono (absMask_ok hl A₁.x24) fun s₂ ⟨x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env c s₂ := A₁.env.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hb := Proof.AesCcm.blocks_pad16 (bytesAt s.mem P len)
  rw [length_bytesAt] at hb
  have hRb := L.rb
  refine WP.ite (decide (len % 16 = 0)) (eval_zero x13₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E₂, by rw [hg₂ _ (by decide), A₁.x23], by rw [hg₂ _ (by decide), A₁.x24],
      by rw [hm₂]; exact A₁.frame, ?_, by rw [rd₂, A₁.rd], by rw [wr₂, A₁.wr]⟩
    rw [hm₂, A₁.out, hb]
    simp only [h0, ↓reduceIte, List.append_nil]
  · have h0 : len % 16 ≠ 0 := of_decide_eq_false hf
    refine WP.mono (absTail_ok v L E₂ hy (hP.of_eq (by rw [rd₂, A₁.rd]) (by rw [wr₂, A₁.wr]))
      (by rw [hg₂ _ (by decide), A₁.x23]) (by rw [hg₂ _ (by decide), A₁.x24]) x13₂ h0) fun s₃ A₃ =>
      ⟨A₃.env, A₃.x23, A₃.x24, A₁.frame.trans (by rw [← hm₂]; exact A₃.frame), ?_,
        by rw [A₃.rd, rd₂, A₁.rd], by rw [A₃.wr, wr₂, A₁.wr]⟩
    rw [A₃.out, hm₂, A₁.out, buf_macR hP (by omega) A₁.frame, ciph_macR L (by omega) A₁.frame,
      ← Proof.Cmac.chain_append, hb, tailBlocks, length_bytesAt]

end VG.Proof.AesCcm.AArch64
