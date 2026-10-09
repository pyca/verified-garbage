import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Stitch
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full

/-!
# AES-GCM on whole blocks out of place, x86-64: loops that take all the blocks

Untrusted: everything here is checked by Lean. With a `piece` that also
takes the blocks after the last 16 (`full`), at least 16 blocks are all
given to it, after `takeAllTo` makes the arguments kept those of no rest
(`takeAllTo_ok`): its result is `Mid` with `q = k = n` (`mid_of_postTo`),
which `rest` keeps (`restFullTo_ok`). With fewer, `q = 0`, as without `full`
(`stitchFullTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo EPostTo StitchToOkM)

/-- The blocks a `piece` that takes them all is given: all of them if at
least 16, else none. -/
def qf (s : State) : Nat := if n s < 16 then 0 else n s

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- `takeAllTo`: the arguments kept become those of no rest. -/
theorem takeAllTo_ok {s₂ : State} (h11 : s₂.gpr .r11 = S s) (h9 : s₂.gpr .r9 = s.gpr .r9)
    (h8 : s₂.gpr .r8 = Src s) (h10 : s₂.gpr .r10 = Dst s) (hk : Kept s 0 s₂.mem)
    (hf : Frame [kR' s] s.mem s₂.mem) (hwr : s₂.wr = s.wr) :
    WP isa (.block takeAllTo) s₂ fun s₃ => Kept s (n s) s₃.mem ∧ Frame [kR' s] s.mem s₃.mem ∧
      (∀ r, r ≠ .rax → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
  have w₅ : InRegions s₂.wr (S s + BitVec.ofNat 64 32) 8 := by rw [hwr]; exact s_in hp (by decide)
  have w₆ : InRegions s₂.wr (S s + BitVec.ofNat 64 40) 8 := by rw [hwr]; exact s_in hp (by decide)
  have w₇ : InRegions s₂.wr (S s + BitVec.ofNat 64 48) 8 := by rw [hwr]; exact s_in hp (by decide)
  have e9 : s₂.gpr .r9 = BitVec.ofNat 64 (n s) := by rw [h9]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ u v w : BitVec 64,
      (((s₂.mem.writeW (S s + BitVec.ofNat 64 32) u).writeW (S s + BitVec.ofNat 64 48) v).writeW
        (S s + BitVec.ofNat 64 40) w).readW (S s + BitVec.ofNat 64 d) 64 =
        s₂.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ u v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 48 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega)) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [takeAllTo, argSrc, argDst, argN]; xrun [h11, e9, h8, h10, w₅, w₆, w₇, times16_val], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r hr => by simp [gpr_setReg, gpr_arithFlags, hr], rfl, rfl⟩
  · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact hk.ctx
  · rw [kp 8 (by decide)]; exact hk.rounds
  · rw [kp 16 (by decide)]; exact hk.ctr
  · rw [kp 24 (by decide)]; exact hk.y
  · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 32 48 (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, BitVec.add_comm]
  · rw [Mem.readW_writeW_self64, Nat.sub_self]; rfl
  · rw [Mem.readW_writeW_sep (sep 48 40 (.inr (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, BitVec.add_comm]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega)
    exact ((hf.writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

/-- `rest` with no blocks left: nothing changes. -/
theorem restZeroTo_ok {q : Nat} (hq : q = n s) {st : State} (h : Mid s q q st) :
    WP isa (.block rest) st (Mid s q q) := by
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₇ : InRegions st.wr (S s + BitVec.ofNat 64 48) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kr := h.kept.src
  have kn := h.kept.n
  have kd := h.kept.dst
  rw [hq, Nat.sub_self] at kn
  have e15 : 0#64 &&& 15#64 = 0#64 := by decide
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have s₅₇ := sep 32 48 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have s₆₇ := sep 40 48 (by decide) (by decide) (by decide)
  have s₇₅ := sep 48 32 (by decide) (by decide) (by decide)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ u v w : BitVec 64,
      (((st.mem.writeW (S s + BitVec.ofNat 64 32) u).writeW (S s + BitVec.ofNat 64 48) v).writeW
        (S s + BitVec.ofNat 64 40) w).readW (S s + BitVec.ofNat 64 d) 64 =
        st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ u v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 48 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega)) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [rest, argSrc, argN, argDst]
    xrun [a₂, hS, r₅, r₆, r₇, w₅, w₆, w₇, kn, e15, kr, kd, s₅₇, s₅₆, s₆₇, s₇₅, BitVec.sub_self,
      BitVec.add_zero, BitVec.zero_add, Mem.readW_writeW_sep, Mem.readW_writeW_self64], ?_⟩
  refine h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => ?_) ?_ ?_ rfl rfl
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
    · rw [kp 8 (by decide)]; exact h.kept.rounds
    · rw [kp 16 (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 32 48 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64, hq, Nat.sub_self]
    · rw [Mem.readW_writeW_sep (sep 48 40 (.inr (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

/-- `rest` after all the blocks, or none if fewer than 16. -/
theorem restFullTo_ok {st : State} (h : Mid s (qf s) (qf s) st) :
    WP isa (.block rest) st (Mid s (qf s) (qf s)) := by
  by_cases h16 : n s < 16
  · have hq : qf s = 0 := by simp [qf, h16]
    rw [hq] at h ⊢
    exact rest_ok hp (by omega) h
  · exact restZeroTo_ok hp (by simp [qf, h16]) h

/-- With `full`, all the blocks by `piece` (if at least 16). -/
theorem stitchFullTo_ok {piece : Prog isa} (hpiece : StitchToOkM M piece 1)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (h10 : s₁.gpr .r10 = Dst s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece aligned true) s₁ (Mid s (qf s) (qf s)) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h16 : n s < 16 := by simpa using h
    have hq : qf s = 0 := by simp [qf, h16]
    rw [hq]
    exact WP.block_nil (mid_entry hp (by rw [g₂]; exact hg _ (by decide) (by decide))
      (fun r hr => by rw [g₂]; exact hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ n s := by simp at h; omega
    have hq : qf s = n s := by simp [qf, show ¬ n s < 16 by omega]
    rw [hq]
    refine WP.seq ?_
    rw [show ((if true = true then takeAllTo else [.mov .rax (.reg .r9), .alu .and .rax (imm 15),
      .alu .sub .r9 (.reg .rax)]) ++ Blocks.scratchSetup aligned : List Instr) =
      takeAllTo ++ Blocks.scratchSetup aligned from rfl, WP.block_append_iff]
    refine WP.mono (takeAllTo_ok hp (by rw [g₂, h11]) (by rw [g₂, hg _ (by decide) (by decide)])
      (by rw [g₂, hg _ (by decide) (by decide)]) (by rw [g₂, h10]) (by rw [m₂]; exact hk) (by rw [m₂]; exact hf)
      (by rw [wr₂, hwr])) fun s₃ ⟨k₃, f₃, g₃, rd₃, wr₃⟩ => ?_
    refine WP.mono (Blocks.scratch_ok (aligned := aligned) s₃) fun s₄ ⟨h11₄, g₄, m₄, rd₄, wr₄⟩ => ?_
    have keepR : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s₄.gpr r = s.gpr r := fun r a b c => by
      rw [g₄ r c, g₃ r a, g₂, hg r c b]
    have ga : ∀ r ∈ argRegs, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide)
    have gc : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide)
    have h10₄ : s₄.gpr .r10 = Dst s := by rw [g₄ _ (by decide), g₃ _ (by decide), g₂, h10]
    have g11 : s₄.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
      rw [h11₄, g₃ _ (by decide), g₂, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
    have h9 : s₄.gpr .r9 = BitVec.ofNat 64 (n s) := by
      rw [keepR _ (by decide) (by decide) (by decide)]
      exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
    have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, hrd]
    have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, hwr]
    have hk₄ : Kept s (n s) s₄.mem := by rw [m₄]; exact k₃
    have hf₄ : Frame [kR' s] s.mem s₄.mem := by rw [m₄]; exact f₃
    exact WP.mono (hpiece s₄ (spreTo_of hp h16 (Nat.le_refl _) h9 ga h10₄ g11 rd₄' wr₄' hf₄) (Nat.mod_one _))
      fun s₅ hP => mid_of_postTo hp (Nat.le_refl _) h9 ga gc h10₄ g11 rd₄' wr₄' hk₄ hf₄ hP

end

end VG.Proof.AesGcm.X86_64.BlocksTo
