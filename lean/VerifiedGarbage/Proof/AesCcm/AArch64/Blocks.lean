import VerifiedGarbage.Proof.AesCcm.AArch64.Entry

/-!
# AES-CCM on AArch64: `Ctr₀`, counter blocks and chaining a block

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte and copies the nonce
after it: `Ctr₀` (`ctrs_ok`). `ctrAt` makes `Ctrᵢ` at `W + 64` from `Ctr₀`
(`ctrAt_ok`); `updBlock y` chains the block `B` at `W + 32` into the MAC
state at `W + y` (`updBlock_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok loopRegs Others add_ofNat_assoc)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_base ctrBlock_take8 ctr_or be_zero
  sub_low_byte)

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

/-! ## `Ctr₀` -/

/-- `Ctr₀`, from the nonce `N` of `nl` bytes. -/
theorem ctrs_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {N : Addr} (hN : Buf c s N c.nl)
    (h2 : s.gpr .x2 = N) (h3 : s.gpr .x3 = BitVec.ofNat 64 c.nl) :
    WP isa ctrs s fun s' => Env c s' ∧ Frame [⟨c.W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h7 := L.h7
  have h13 := L.h13
  have w₁ := E.perm.wW (show 48 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 56 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 48 + 1 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, x11₁, x12₁, x13₁, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa ctrsSeg s = some s₁ ∧
      s₁.mem = ((s.mem.writeW (c.W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 56)
        (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 48) (BitVec.ofNat 8 (15 - c.nl - 1)) ∧
      s₁.gpr .x11 = c.W + BitVec.ofNat 64 49 ∧ s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 c.nl ∧
      Others [.x9, .x11, .x12, .x13] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [ctrsSeg, E.x19, w₁, w₂, w₃], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · have z : (BitVec.setWidth 64 0#16 <<< 0 : BitVec 64) = 0 := by decide
      have f : (BitVec.setWidth 64 14#16 <<< 0 : BitVec 64) = BitVec.ofNat 64 14 := by decide
      simp only [mem_write, z, f, h3, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide),
        sub_low_byte (show c.nl ≤ 14 by omega)]
      rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h2]
    · simp [gpr_write, h3]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  have dNW : (⟨N, c.nl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 49, c.nl⟩ := hN.wd (by omega)
  have lp : LoopPre s₁ N (c.W + BitVec.ofNat 64 49) c.nl :=
    ⟨by omega, by rw [rd₁, wr₁]; exact hN.rd, E₁.perm.wC (by omega), dNW⟩
  refine WP.mono (copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega) lp) fun s₂ ⟨hm₂, _, _, hg₂, sp₂, rd₂, wr₂⟩ => ?_
  have hfz : Frame [⟨c.W + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 48) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 56) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 48) (n := 1) (e := 48) (k := 16) (by decide) (by decide) (by decide))
  have hNs : bytesAt s₁.mem N c.nl = bytesAt s.mem N c.nl :=
    Proof.AesGcm.AArch64.bytesAt_frame hfz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hN.wd (by decide)) (by omega)
  refine ⟨E₁.others hg₂ (by decide) sp₂ rd₂ wr₂, ?_, ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · refine hfz.trans ?_
    rw [hm₂]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains c.W (d := 49) (n := c.nl) (e := 48) (k := 16) (by decide) (by omega) (by decide))
  · -- The bytes of the block.
    have e56 : c.W + BitVec.ofNat 64 56 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
    have hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 48) 16 = BitVec.ofNat 8 (15 - c.nl - 1) :: Spec.Ccm.zeros 15 := by
      rw [hm₁, bytesAt_writeW8_base _ _ _ (by decide) (by decide), e56, Proof.Cmac.bytesAt_store2,
        Proof.Cmac.le8_zero]
      rfl
    have hl := length_bytesAt s.mem N c.nl
    rw [hm₂, show c.W + BitVec.ofNat 64 49 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 by rw [add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hz, hNs,
      Spec.Ccm.ctrBlock, hl, be_zero, show 1 + c.nl = c.nl + 1 by omega]
    simp only [Spec.Ccm.zeros, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_replicate,
      List.cons_append, List.nil_append]

/-! ## `ctrAt` -/

/-- `Ctrᵢ` at `W + 64`, for `i` in `x9`. -/
theorem ctrAt_ok {c : Cx} {s : State} (E : Env c s) {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (h13 : nonce.length ≤ 13) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) (h9 : s.gpr .x9 = BitVec.ofNat 64 i) :
    WP isa (.block ctrAt) s fun s' => Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      Others [.x9, .x10, .x11] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₁ := E.perm.wW (show 64 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 56 + 8 ≤ 2560 by decide)
  obtain ⟨s', run, hm, hg, sp', rd', wr'⟩ : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 64) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
        (c.W + BitVec.ofNat 64 72) (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 i)) ∧
      Others [.x9, .x10, .x11] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by carun [ctrAt, E.x19, w₁, w₂, r₁, r₂], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h9]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have e72 : c.W + BitVec.ofNat 64 72 = c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have e56 : c.W + BitVec.ofNat 64 56 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  refine WP.of_runBlock ⟨s', run, ?_, ?_, hg, sp', rd', wr'⟩
  · rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 64) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 72) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))
  · have h8 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 8 = (bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16).take 8 := by
      rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hlo : le8 (s.mem.readW (c.W + BitVec.ofNat 64 48) 64) = (Spec.Ccm.ctrBlock nonce i).take 8 := by
      rw [Proof.Cmac.le8_readW, h8, hc0, ctrBlock_take8 h7, ctrBlock_take8 h7]
    have hhi : le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    rw [hm, e72, Proof.Cmac.bytesAt_store2, hlo, ctr_or h7 h13 hhi hi, List.take_append_drop]

/-! ## Chaining `B` -/

/-- What a call of `vg_cmac_aes_update` keeps of the pieces' registers. -/
abbrev pieceRegs : List Reg := [.x23, .x24, .x25, .x26]

/-- The arguments of the call chaining `B` into the MAC state at `W + y`. -/
theorem updArgs_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (updArgs y ++ ([ptr .x3 .x19 bO, imm .x4 1] : List Instr))) s fun s₁ => Env c s₁ ∧
      Proof.CmacAes.Stream.AArch64.UArgs s₁ c.K (c.W + BitVec.ofNat 64 y) (c.W + BitVec.ofNat 64 32)
        (c.W + BitVec.ofNat 64 384) c.R 1 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ [ptr .x3 .x19 bO, imm .x4 1]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .x0 = c.K ∧ s₁.gpr .x1 = BitVec.ofNat 64 c.R ∧ s₁.gpr .x2 = c.W + BitVec.ofNat 64 y ∧
      s₁.gpr .x3 = c.W + BitVec.ofNat 64 32 ∧ s₁.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₁.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hy' : y < 4096 := by omega
    refine ⟨_, by carun [updArgs, hy'], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x22]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, E.x19]
    · simp [gpr_write]
    · simp [gpr_write, E.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have E₁ : Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  refine WP.of_runBlock ⟨s₁, run₁, E₁, ?_, hg₁, hm₁, rd₁, wr₁⟩
  have hq := L.srcW (s := s₁) E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨c.W + BitVec.ofNat 64 32, 16 * 1⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  exact uargs L E₁ (by omega) hq hqy (by decide) x0 x1 x2 x3 x4 x5

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock v.callee y) s fun s' => Env c s' ∧ (∀ r ∈ pieceRegs, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 y, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
          [bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16] := by
  refine WP.seq (WP.mono (updArgs_ok L E hy) fun s₁ ⟨E₁, A₁, hg₁, hm₁, rd₁, wr₁⟩ => ?_)
  refine WP.mono (upd_call v v.callee.name A₁)
    fun s₂ h => ⟨E₁.of_saved h.saved h.sp h.rd h.wr, fun r hr => ?_, by rw [h.rd, rd₁], by rw [h.wr, wr₁],
      by rw [← hm₁]; exact h.frame, ?_⟩
  · have hr' : r = .x23 ∨ r = .x24 ∨ r = .x25 ∨ r = .x26 := by simpa using hr
    rcases hr' with rfl | rfl | rfl | rfl <;> rw [h.saved _ (by decide) (by decide), hg₁ _ (by decide)]
  · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
      (Proof.Cmac.bytesAt_length _ _ _), hm₁]
    rfl

end VG.Proof.AesCcm.AArch64
