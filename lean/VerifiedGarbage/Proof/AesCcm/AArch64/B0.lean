import VerifiedGarbage.Proof.AesCcm.AArch64.Blocks

/-!
# AES-CCM on AArch64: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `flagsSeg` computes the flags
`4 (t − 2) + q − 1 + 64 [a > 0]` (which is A.2.1's for an even `t`,
`flags_ok`); `b0Seg y` writes `B₀` to `W + 32` from `Ctr₀` and zeroes the MAC
state at `W + y` (`b0Seg_ok`); `b0 y` then chains `B₀` into it (`b0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (Others add_ofNat_assoc eval_zero ofNat_sub)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeW64_at bytesAt_writeW8_base bytesAt_writeW64_base
  ctrBlock_take8 ctrBlock_drop8 ctr_or flags_val)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B` and the
working space of the functions called. -/
abbrev macR (W : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩]

theorem macR_mut {c : Cx} {y : Nat} (hy : y = 0 ∨ y = 96) : ∀ r ∈ macR c.W y, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by omega)
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

/-- The flags, from the tag length, the nonce length in its slot and the
length of the associated data in `x24`. -/
theorem flags_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) :
    WP isa flagsSeg s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64) ∧
      Others [.x9, .x10, .x11] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have rn := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have ht4 := L.t4
  have ht16 := L.t16
  have h13 := L.h13
  obtain ⟨s₁, run₁, x9₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.subImm .x .x9 .x20 2, .lsl .x .x9 .x9 2, .ldr .x .x10 .x19 nlenO, imm .x11 14,
        .sub .x .x11 .x11 .x10, .add .x .x9 .x9 .x11] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl)) ∧ Others [.x9, .x10, .x11] s s₁ ∧
      s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, rn], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
    · have hn : s.mem.read (c.W + 232#64) 8 = BitVec.ofNat 64 c.nl := S.nlen
      simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E.x20, hn]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft,
        BitVec.toNat_ofNat, Nat.shiftLeft_eq, Size.bits]
      have := L.h7
      omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 c.al := by rw [hg₁ _ (by decide), h24]
  refine WP.ite (decide (c.al = 0)) (eval_zero h24₁ L.al_lt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    exact WP.block_nil ⟨by rw [x9₁, h0]; rfl, hg₁, hm₁, sp₁, rd₁, wr₁⟩
  · have h0 : c.al ≠ 0 := of_decide_eq_false hf
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₂ hs₂ => ?_
    subst hs₂
    refine ⟨?_, fun r hr => ?_, hm₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, x9₁, h0, ite_false]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Size.bits]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hg₁ r (by simp [hr.1, hr.2.1, hr.2.2])]

/-- `B₀` in `B`, and the MAC state at `W + y` zeroed. -/
theorem b0Seg_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64))
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (b0Seg y)) s fun s' => Env c s' ∧ (∀ r ∈ pieceRegs, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
  have h7 := L.h7
  have h13 := L.h13
  have c₁ := E.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have c₂ := E.perm.wR (show 56 + 8 ≤ 2560 by decide)
  have b₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have b₂ := E.perm.wW (show 32 + 1 ≤ 2560 by decide)
  have b₃ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have y₁ := E.perm.wW (show y + 8 ≤ 2560 by omega)
  have y₂ := E.perm.wW (show y + 8 + 8 ≤ 2560 by omega)
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((s.mem.writeW (c.W + BitVec.ofNat 64 32) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
      (c.W + BitVec.ofNat 64 32) ((s.gpr .x9).setWidth 8 : Byte)).writeW (c.W + BitVec.ofNat 64 40)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 c.n)) := ⟨_, rfl⟩
  obtain ⟨s₃, run₃, hm₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa (b0Seg y) s = some s₃ ∧
      s₃.mem = (mB.writeW (c.W + BitVec.ofNat 64 y) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 (y + 8))
        (0 : BitVec 64) ∧
      Others [.x9, .x10, .x11, .x12] s s₃ ∧ s₃.sp = s.sp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
    have ya : y % 8 = 0 ∧ y < 32768 := by omega
    have yb : (y + 8) % 8 = 0 ∧ y + 8 < 32768 := by omega
    refine ⟨_, by carun [b0Seg, E.x19, c₁, c₂, b₁, b₂, b₃, y₁, y₂, ya, yb], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
    · rw [hmB]
      simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, E.x28]
      rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨s₃, run₃, E.others hg₃ (by decide) sp₃ rd₃ wr₃, fun r hr => hg₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> decide),
    rd₃, wr₃, ?_⟩
  -- What the block wrote.
  have e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have ey8 : c.W + BitVec.ofNat 64 (y + 8) = c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by decide)
  have cY : ∀ d k, y ≤ d → d + k ≤ y + 16 →
      (⟨c.W + BitVec.ofNat 64 y, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by omega)
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem mB := by
    rw [hmB]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))
  have fY : Frame [⟨c.W + BitVec.ofNat 64 y, 16⟩] mB s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cY y 8 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (cY (y + 8) 8 (by omega) (by omega))
  have dYB : (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨(fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
    (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩), ?_, ?_⟩
  · -- The state was zeroed.
    rw [hm₃, ey8, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · -- `B₀`.
    have hB₁ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 = bytesAt mB (c.W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.AArch64.bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB)
        (by decide)
    have hlo : le8 (s.mem.readW (c.W + BitVec.ofNat 64 48) 64) =
        BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
      have h8 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 8 =
          (bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16).take 8 := by
        rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rw [Proof.Cmac.le8_readW, h8, hc0, ctrBlock_take8 (by omega)]
    have hhi : le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      have e56 : c.W + BitVec.ofNat 64 56 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
      rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hb : ((s.gpr .x9).setWidth 8 : Byte) = Spec.Ccm.flags c.tl (15 - nonce.length) c.al := by
      rw [h9, hnl, flags_val L.t4 L.t16 L.te h7 h13]
    have hB : bytesAt mB (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
      rw [hmB, e40, bytesAt_writeW64_at _ _ _ (by decide) (by decide), bytesAt_writeW8_base _ _ _ (by decide)
        (by decide), bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hb,
        ctr_or (by omega) (by omega) hhi (by rw [hnl]; exact L.hn), ctrBlock_drop8 (by omega)]
      simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons]
      have hX : (Spec.Ccm.flags c.tl (15 - nonce.length) c.al ::
          (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16))).length ≤ 8 + 8 := by
        simp [length_bytesAt]; omega
      rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega),
        List.drop_eq_nil_of_le hX, List.append_nil, ← List.append_assoc, List.take_append_drop]
    rw [hB₁, hB]

/-- What a piece of the MAC leaves: the environment, what it writes, the MAC
state `Y` at `W + y`, and the permissions. -/
structure MacStep (c : Cx) (y : Nat) (s : State) (Y : List Byte) (s' : State) : Prop where
  env : Env c s'
  frame : Frame (macR c.W y) s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem k_macR {c : Cx} (L : Lay c) {y : Nat} (hy : y + 16 ≤ 2560) :
    ∀ r ∈ macR c.W y, (⟨c.K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w' hy
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)

theorem ciph_macR {c : Cx} (L : Lay c) {y : Nat} (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (macR c.W y) m m') :
    Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (k_macR L hy r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

/-- A buffer missing `W` keeps its bytes. -/
theorem buf_macR {c : Cx} {s : State} {P : Addr} {len : Nat} (hP : Buf c s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (macR c.W y) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.wd hy
    · exact hP.wd (by decide)
    · exact hP.wd (by decide)) (by have := hP.lt; omega)

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    (S : Slots c s.mem) (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee y) s fun s' => MacStep c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 c.tl nonce c.al c.n]) s' ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 := by
  refine WP.seq (WP.mono (flags_ok L E S h24) fun s₁ ⟨x9₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (b0Seg_ok L E₁ hnl (by rw [hm₁]; exact hc0) x9₁ hy)
    fun s₃ ⟨E₃, g₃, rd₃, wr₃, f₃, hz, hB⟩ => ?_)
  refine WP.mono (updBlock_ok v L E₃ hy) fun s₄ ⟨E₄, g₄, rd₄, wr₄, f₄, h₄⟩ =>
    ⟨⟨E₄, ?_, ?_, by rw [rd₄, rd₃, rd₁], by rw [wr₄, wr₃, wr₁]⟩, ?_, ?_⟩
  · rw [← hm₁]
    refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₄, hz, hB, ← hm₁, ciph_macR L (y := y) (by omega) (f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩)]
  · rw [g₄ _ (by simp), g₃ _ (by simp), hg₁ _ (by decide)]
  · rw [g₄ _ (by simp), g₃ _ (by simp), hg₁ _ (by decide)]

end VG.Proof.AesCcm.AArch64
