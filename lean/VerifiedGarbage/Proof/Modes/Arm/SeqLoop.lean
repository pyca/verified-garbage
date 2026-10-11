import VerifiedGarbage.Proof.Modes.Arm.SeqBody

/-!
# The modes one block at a time on ARMv7: the loop and the whole function

`seq_wp`: `Core.seq c M` meets `seqArm c S M`, for any core and any mode
whose operations are on two different blocks (`ModeOk`): the prologue gives
the invariant for no blocks, each run of the body (`body_ok`) one more, and
the epilogue returns the chaining block if the mode does (`finish`) and
restores our caller's registers from the scratch buffer, whose slots
nothing after the prologue writes.
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf over)
open VG.Proof.MdStream.Arm (wp_ldr eval_eq eval_ne)

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

theorem loop_ok (hM : ModeOk c M) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv c S M s₀ k s) :
    WP isa (.loop (c.body M) .ne) s (LInv c S M s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := c.body M) (c := .ne) (Q := LInv c S M s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv c S M s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hM hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

theorem mid_wp (hM : ModeOk c M) {s₁ : State} (h : LInv c S M s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop (c.body M) .ne)) s₁ (LInv c S M s₀ (N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp hM (by omega) h

/-! ## The epilogue -/

/-- The slots of the saved registers. -/
abbrev slotsR (s₀ : State) : Region := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 0, 36⟩

theorem UPre.slots_disj : ∀ r ∈ [dataR c s₀ M, blkR c s₀, belowR S s₀, ivR c s₀], (slotsR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.data_scr.symm.sub_left UPre.slots_sub
  · exact hp.slots_disj_blk
  · exact hp.b_scr.symm.sub_left UPre.slots_sub
  · exact hp.iv_scr.symm.sub_left UPre.slots_sub

/-- What the epilogue starts from: the invariant after all the blocks, with
the chaining block perhaps copied to the IV. -/
structure EInv (s₀ : State) (s : State) : Prop where
  r8 : s.gpr .r8 = Sc s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀, ivR c s₀] (savedMem s₀) s.mem
  data : blocksOf (c.ds M) s.mem (State.addr (Dp s₀)) (N s₀) = (rK S s₀ M (N s₀)).1
  iv : M.finish = true → bytesAt s.mem (State.addr (Ivp s₀)) c.bs = (rK S s₀ M (N s₀)).2.o

omit hp in
theorem take_N : (xs c s₀ M).take (N s₀) = xs c s₀ M := List.take_of_length_le (by rw [length_blocksOf])

theorem finish_wp {s : State} (h : LInv c S M s₀ (N s₀) s) :
    WP isa (.block (c.finish M)) s (EInv (c := c) (S := S) (M := M) s₀) := by
  have hnil : (xs c s₀ M).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_blocksOf])
  have hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes at this; omega
  have fr4 : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀, ivR c s₀] (savedMem s₀) s.mem :=
    h.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]
  unfold Core.finish
  split
  · rename_i hf
    have hS := hp.fS
    have hI := hp.fIv
    have hsc : c.scratchBytes = oOff + 2 * c.bs := rfl
    have hbs : c.bs = 4 * c.bw := rfl
    have hb := S.bw_le
    have ho : oOff = 40 := rfl
    have np : NPre c.bw s .r5 .r8 0 oOff (State.addr (Ivp s₀) + BitVec.ofNat 64 0) (oA s₀) := by
      refine ⟨by rw [h.r5], by rw [h.r8], by rw [h.r5]; omega, by rw [h.r8]; omega, by omega, by omega,
        by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
      · rw [h.wr]; exact cov_off (R := ivR c s₀) (hp.fin hf) (by show 0 + 4 * c.bw ≤ c.bs; omega)
      · rw [h.rd, h.wr]
        exact cov_off (R := scrR c s₀) (List.mem_append_right _ hp.scr_in)
          (by show oOff + 4 * c.bw ≤ c.scratchBytes; omega)
      · exact (hp.iv_scr.sub_left (VG.Offset.sub_base _ (by omega))).sub_right
          (VG.Offset.sub_base _ (by omega))
    refine WP.mono (copyN_wp np) fun s' hi => ⟨by rw [hi.regs _ (by decide) (by decide), h.r8],
      by rw [hi.sp, h.sp], by rw [hi.rd, h.rd], by rw [hi.wr, h.wr], ?_, ?_, fun _ => ?_⟩
    · rw [hi.mem]
      exact fr4.trans ((VG.Proof.Modes.over_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨ivR c s₀, .tail _ (.tail _ (.tail _ (.head _))), by rw [add0]; exact Region.sub_prefix (by omega)⟩)
    · rw [hi.mem]
      refine Eq.trans (b := blocksOf (c.ds M) s.mem (State.addr (Dp s₀)) (N s₀))
        (List.map_congr_left fun j hj => ?_) (by rw [h.data, hnil, List.append_nil])
      have hj := List.mem_range.mp hj
      have hsub : Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (c.ds M * j), c.ds M⟩ (dataR c s₀ M) :=
        VG.Offset.sub_base _ (by have := idx_lt' (L := c.ds M) hj; omega)
      exact bytesAt_over_other _ _ (by rw [add0]; exact (hp.iv_data.sub_left (Region.sub_prefix (by omega))).sub_right hsub)
        (by have := S.ds_le M; omega)
    · rw [hi.mem, ← h.o, add0]
      have e := bytesAt_over_self s.mem (State.addr (Ivp s₀) + BitVec.ofNat 64 0)
        (fun i => s.mem (oA s₀ + BitVec.ofNat 64 i)) (n := 4 * c.bw) (by omega)
      rw [add0] at e
      rw [hbs, e]; rfl
  · refine WP.block_nil ⟨h.r8, h.sp, h.rd, h.wr, fr4, by rw [h.data, hnil, List.append_nil], fun hf => ?_⟩
    rename_i hnf; exact absurd hf hnf

theorem epilogue_wp {s : State} (h : EInv (c := c) (S := S) (M := M) s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (seqArm c S M).post s₀ s' := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs := rfl
  have ho : oOff = 40 := rfl
  have hsv : Spill.Saved s.mem (State.addr (Sc s₀)) s₀.gpr saved :=
    (Spill.saveMem_saved (State.addr (Sc s₀)) s₀.gpr s₀.mem saved saved_slots).frame saved_slots h.frame
      (fun r hr => hp.slots_disj r hr)
  have hin : ∀ d, d + 4 ≤ 36 → InRegions (s.rd ++ s.wr) (State.addr (Sc s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [h.rd, h.wr]
      exact ⟨scrR c s₀, List.mem_append_right _ hp.scr_in, VG.Offset.contains_base _ (by omega) (by omega)⟩
  rw [show (restore : List Instr) = savedA.map (fun p => Instr.ldr p.1 .r8 p.2) ++ [.ldr .r8 .r8 16] from rfl]
  refine Spill.restore_slots_ok savedA_slots savedA_restorable (g := s₀.gpr) (by rw [h.r8]; omega)
    (fun d _ hd => by rw [h.r8]; exact hin d hd)
    (by rw [h.r8]; exact fun p hp' => hsv p (by rw [saved_eq]; exact List.mem_append_left _ hp'))
    fun s₁ ld ho' m₁ rd₁ wr₁ sp₁ => ?_
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 16) (by decide)
    (by rw [ho' _ (by decide), h.r8]; exact addr_add (by omega))
    (by rw [rd₁, wr₁]; exact hin 16 (by decide)) fun s₂ u₂ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · by_cases h8 : r = .r8
    · subst h8; rw [u₂.gpr, m₁]; exact hsv (.r8, 16) (by decide)
    · rw [u₂.other _ h8]
      have : r ∈ savedA.map Prod.fst := by
        revert hr h8; revert r; decide
      exact Spill.restored_reg ld this
  · rw [u₂.sp, sp₁, h.sp]
  · show blocksOf (c.ds M) s₂.mem (State.addr (Dp s₀)) (N s₀) = _
    rw [u₂.mem, m₁, h.data]; simp only [rK, take_N]
  · intro hf
    show bytesAt s₂.mem (State.addr (Ivp s₀)) c.bs = _
    rw [u₂.mem, m₁, h.iv hf]; simp only [rK, take_N]

end

/-- The whole function meets its contract, for any core and mode. -/
theorem seq_wp {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk c M) {s₀ : State}
    (h0 : (seqArm c S M).pre s₀) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧ (seqArm c S M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hp hM h₁ hz) fun _ h₂ => by
      rw [WP.block_append_iff]
      exact WP.mono (finish_wp hp h₂) fun _ h₃ => epilogue_wp hp h₃))

end VG.Proof.Modes.Arm
