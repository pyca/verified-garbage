import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch

/-!
# AES-GCM on whole blocks, x86-64: loops that take all the blocks

Untrusted: everything here is checked by Lean. With a `piece` that also
takes the blocks after the last 16 (`full`), at least 16 blocks are all
given to it, after `takeAll` makes the arguments kept those of no rest
(`takeAll_ok`): its result is `Mid` with `q = k = n` (`mid_of_post`), which
`rest` keeps (`restZero_ok`). With fewer, `q = 0`, as without `full`
(`stitchFull_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BP M s)
include hp

/-- `takeAll`: the arguments kept become those of no rest. -/
theorem takeAll_ok {s₂ : State} (h11 : s₂.gpr .r11 = S s) (h9 : s₂.gpr .r9 = s.gpr .r9)
    (h8 : s₂.gpr .r8 = D s) (hk : Kept s 0 s₂.mem) (hf : Frame [kR' s] s.mem s₂.mem) (hwr : s₂.wr = s.wr) :
    WP isa (.block takeAll) s₂ fun s₃ => Kept s (n s) s₃.mem ∧ Frame [kR' s] s.mem s₃.mem ∧
      (∀ r, r ≠ .rax → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
  have w₅ : InRegions s₂.wr (S s + BitVec.ofNat 64 32) 8 := by rw [hwr]; exact s_in hp (by decide)
  have w₆ : InRegions s₂.wr (S s + BitVec.ofNat 64 40) 8 := by rw [hwr]; exact s_in hp (by decide)
  have e9 : s₂.gpr .r9 = BitVec.ofNat 64 (n s) := by rw [h9]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ v w : BitVec 64,
      ((s₂.mem.writeW (S s + BitVec.ofNat 64 32) v).writeW (S s + BitVec.ofNat 64 40) w).readW
        (S s + BitVec.ofNat 64 d) 64 = s₂.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega)) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [takeAll, argData, argN]; xrun [h11, e9, h8, w₅, w₆, times16_val], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r hr => by simp [gpr_setReg, gpr_arithFlags, hr], rfl, rfl⟩
  · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact hk.ctx
  · rw [kp 8 (by decide)]; exact hk.rounds
  · rw [kp 16 (by decide)]; exact hk.ctr
  · rw [kp 24 (by decide)]; exact hk.y
  · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, BitVec.add_comm]
  · rw [Mem.readW_writeW_self64, Nat.sub_self]; rfl
  · have c : ∀ d, d + 8 ≤ 48 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega)
    exact (hf.writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))

/-- `rest` with no blocks left: nothing changes. -/
theorem restZero_ok {q : Nat} (hq : q = n s) {ys : List Block} {st : State} (h : Mid s q q ys st) :
    WP isa (.block rest) st (Mid s q q ys) := by
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by
    rw [h.rsp, keep_a hp h.frame]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kd := h.kept.data
  have kn := h.kept.n
  rw [hq, Nat.sub_self] at kn
  have e15 : 0#64 &&& 15#64 = 0#64 := by decide
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ v w : BitVec 64,
      ((st.mem.writeW (S s + BitVec.ofNat 64 32) v).writeW (S s + BitVec.ofNat 64 40) w).readW
        (S s + BitVec.ofNat 64 d) 64 = st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega)) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [rest, argData, argN]; xrun [a₀, hS, r₅, r₆, w₅, w₆, kn, e15, kd, BitVec.sub_self,
    BitVec.add_zero, BitVec.zero_add], ?_⟩
  refine h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2, h3]) ?_ ?_ rfl rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
    · rw [kp 8 (by decide)]; exact h.kept.rounds
    · rw [kp 16 (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64, hq, Nat.sub_self]
  · have c : ∀ d, d + 8 ≤ 48 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))

omit hp in
/-- `r11` at the working space. -/
theorem scratch_ok (s₁ : State) :
    WP isa (.block (Blocks.scratchSetup aligned)) s₁ fun s₃ =>
      s₃.gpr .r11 = AlignedScratch.ptr aligned (s₁.gpr .r11) ∧ (∀ r, r ≠ .r11 → s₃.gpr r = s₁.gpr r) ∧
      s₃.mem = s₁.mem ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
  cases aligned <;> apply WP.of_runBlock
  all_goals refine ⟨_, by xrun [Blocks.scratchSetup], ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro r a; simp [gpr_setReg, gpr_arithFlags, a])
    | simp [AlignedScratch.ptr, gpr_setReg, gpr_arithFlags, mem_arithFlags, mem_setReg,
        rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The blocks taken by a `piece` that takes them all: all of them if at
least 16, else none. -/
def qf (s : State) : Nat := if n s < 16 then 0 else n s

/-- With `full`, all the blocks by `piece` (if at least 16). -/
theorem stitchFull_ok {piece : Prog isa} {Post : State → State → Prop} {ys : Nat → List Block}
    (hys : ys 0 = [])
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ → WP isa piece s₃ (Post s₃))
    (hpost : ∀ s₃ s₄, s₃.gpr .r9 = BitVec.ofNat 64 (n s) → (∀ r ∈ argRegs, s₃.gpr r = s.gpr r) →
      (∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r) →
      s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) → s₃.rd = s.rd →
      s₃.wr = s.wr → Kept s (n s) s₃.mem → Frame [kR' s] s.mem s₃.mem → Post s₃ s₄ →
      Mid s (n s) (n s) (ys (n s)) s₄)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) (hk : Kept s 0 s₁.mem)
    (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece aligned true) s₁ (Mid s (qf s) (qf s) (ys (qf s))) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h16 : n s < 16 := by simp at h; omega
    have hq : qf s = 0 := by simp [qf, h16]
    refine WP.block_nil ?_
    rw [hq, hys]
    exact mid_entry hp (fun r hr => by rw [g₂]; exact hg r hr) (by rw [m₂]; exact hk)
      (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr)
  · have h16 : 16 ≤ n s := by simp at h; omega
    refine WP.seq ?_
    rw [show ((if true = true then takeAll else [.mov .rax (.reg .r9), .alu .and .rax (imm 15),
      .alu .sub .r9 (.reg .rax)]) ++ Blocks.scratchSetup aligned : List Instr) =
      takeAll ++ Blocks.scratchSetup aligned from rfl, WP.block_append_iff]
    refine WP.mono (takeAll_ok hp (by rw [g₂, h11]) (by rw [g₂, hg _ (by decide)]) (by rw [g₂, hg _ (by decide)])
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (by rw [wr₂, hwr])) fun s₃ ⟨k₃, f₃, g₃, rd₃, wr₃⟩ => ?_
    refine WP.mono (scratch_ok (aligned := aligned) s₃) fun s₄ ⟨h11₄, g₄, m₄, rd₄, wr₄⟩ => ?_
    have keepR : ∀ r, r ≠ .rax → r ≠ .r11 → s₄.gpr r = s.gpr r := fun r a c => by
      rw [g₄ r c, g₃ r a, g₂, hg r c]
    have ga : ∀ r ∈ argRegs, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide)
    have gc : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide)
    have g11 : s₄.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
      rw [h11₄, g₃ _ (by decide), g₂, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
    have h9 : s₄.gpr .r9 = BitVec.ofNat 64 (n s) := by
      rw [keepR _ (by decide) (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm
    have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, hrd]
    have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, hwr]
    have hk₄ : Kept s (n s) s₄.mem := by rw [m₄]; exact k₃
    have hf₄ : Frame [kR' s] s.mem s₄.mem := by rw [m₄]; exact f₃
    have hq : qf s = n s := by simp [qf, show ¬ n s < 16 by omega]
    rw [hq]
    exact WP.mono (hpiece s₄ (spreM_of hp h16 (Nat.le_refl _) h9 ga g11 rd₄' wr₄' hf₄)) fun s₅ hP =>
      hpost s₄ s₅ h9 ga gc g11 rd₄' wr₄' hk₄ hf₄ hP

/-- `rest` after all the blocks, or none if fewer than 16. -/
theorem restFull_ok {ys : List Block} {st : State} (h : Mid s (qf s) (qf s) ys st) :
    WP isa (.block rest) st (Mid s (qf s) (qf s) ys) := by
  by_cases h16 : n s < 16
  · have hq : qf s = 0 := by simp [qf, h16]
    rw [hq] at h ⊢
    exact rest_ok hp (by omega) h
  · exact restZero_ok hp (by simp [qf, h16]) h


/-- Encryption by a loop that takes all the blocks: the blocks hashed are
those written. -/
theorem stitchEFull_ok {enc dec : Prog isa} (hS : Gcm.X86_64.Stitch.StitchOkM M enc dec 1) {s₁ : State}
    (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart enc aligned true) s₁
      (Mid s (qf s) (qf s) (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (qf s)))) :=
  stitchFull_ok hp (ys := fun q => ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) rfl
    (fun _ h => hS.1 _ h (Nat.mod_one _))
    (fun s₃ s₄ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP => by
      refine mid_of_post hp (by omega) h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
        fun eH eY _ eD => ?_
      have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
      have hy := hP.y
      simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
        Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
        ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
        toNat_ofNat_of_lt hn] at hy
      rw [hy, eH, eY, eD])
    h11 hg hk hf hrd hwr

end

end VG.Proof.AesGcm.X86_64.Blocks
