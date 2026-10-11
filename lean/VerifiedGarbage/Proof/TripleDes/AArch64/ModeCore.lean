import VerifiedGarbage.Proof.TripleDes.AArch64.Pre
import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
import VerifiedGarbage.Proof.TripleDes.CbcBlocks

/-!
# Triple DES's core for the modes on AArch64

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.AArch64.dirCore d`) meets what the modes need of a core of
one-word blocks (`Proof.Modes.AArch64.BlockSpec`), with the key a schedule,
its cipher `Spec.TripleDes.cipher` for encryption and
`Spec.TripleDes.invCipher` for decryption, and the key ready when its copy
in the core's slots is the schedule. `crypt` is the block function
(`block_ok`) on the buffer.
-/

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp addImm_ok runBlock_app
  addr_add)
open VG.Spec.TripleDes (Direction)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `x0`, outside the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.TripleDes.scheduleAt s.mem p ∧ (⟨p, 384⟩ : Region) ∈ s.rd ∧
    p.toNat + 384 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 384⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 1 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, blockResult, ofFn_bytesAt]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 904⟩ := rfl
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 512, 8⟩ := rfl
theorem total_eq (d : Direction) : (dirCore d).total = 125 := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 384⟩ ⟨B, 904⟩ := Offset.sub_base B (by decide)

theorem readyAt_frame {d : Direction} {m m' : Mem} {B : Addr} {k : Spec.TripleDes.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_eq_of_frame _ hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'
    exact (Offset.disjoint B (.inr (by decide)) (by decide) (by decide)).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_eq_of_frame p hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 384⟩ ⟨B, 904⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 48) (u := .x7) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega) (by simp only [schedSlot]; omega)⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega⟩) fun s' h => ?_
  refine ⟨scheduleAt_copy fun i hi => by rw [h.mem, over_at hi (by omega)],
    by rw [h.regs _ (by decide) (by decide), hB], h.regs _ (by decide) (by decide), h.regs _ (by decide) (by decide),
    ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hss : schedSlot = 65 := rfl
  have hw := hs.wr
  rw [total_eq] at hw
  -- `x0`, `x1` and `x2` to the schedule's copy, the buffer and the block function's slots.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := addImm_ok s .x0 sb (v := 8 * schedSlot) (by decide)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x1 sb (v := 8 * cbcBuf) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x2 sb (v := 0) (by decide)
  have g₃ : ∀ x, x ≠ .x0 → x ≠ .x1 → x ≠ .x2 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₃ x h3, o₂ x h2, o₁ x h1]
  have x0₃ : s₃.gpr .x0 = schedAddr B := by rw [o₃ _ (by decide), o₂ _ (by decide), r₁, hB]
  have x1₃ : s₃.gpr .x1 = B + BitVec.ofNat 64 512 := by
    rw [o₃ _ (by decide), r₂, o₁ _ (by decide), hB]; rfl
  have x2₃ : s₃.gpr .x2 = B := by
    rw [r₃, o₂ _ (by decide), o₁ _ (by decide), hB]; exact BitVec.add_zero _
  have mem₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  rw [show (dirCore d).crypt = .seq (.block ([.addImm .x .x0 sb (8 * schedSlot)] ++
      ([.addImm .x .x1 sb (8 * cbcBuf)] ++ ([.addImm .x .x2 sb 0] : List Instr))))
      (.seq (block d) (.block [.addImm .x sb .x2 0])) by cases d <;> rfl]
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃], ?_⟩)
  -- The block.
  have inS : ∀ {t}, t + 8 ≤ 1000 → InRegions s₃.wr (B + BitVec.ofNat 64 t) 8 := fun ht =>
    ⟨_, by rw [wr₃']; exact hw, Offset.contains_base B (by omega) (by omega)⟩
  have hp := headPre_of s₃ (fun i hi => by rw [x2₃]; exact inS (by omega))
    (fun i hi => by
      rw [x0₃, addr_add]
      obtain ⟨r, h1, h2⟩ := inS (t := 8 * schedSlot + 8 * i) (by simp only [schedSlot]; omega)
      exact ⟨r, List.mem_append_right _ h1, h2⟩)
    (by rw [x1₃]; exact inS (by decide))
    (by rw [x0₃, x2₃]; exact Offset.disjoint_base B (by decide) (by omega))
    (by rw [x1₃, x2₃]; exact Offset.disjoint_base B (by decide) (by omega))
  rw [x0₃, mem₃, hr] at hp
  refine WP.seq (WP.mono (block_ok k (schedAddr B) d s₃ hp (by rw [x1₃]; exact inS (by decide)))
    fun s₄ h₄ => ?_)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ sb .x2 (v := 0) (by decide)
  refine WP.of_runBlock ⟨s₅, e₅, ?_⟩
  have x2₄ : s₄.gpr .x2 = B := by rw [h₄.regs .x2 (by decide), x2₃]
  have fB : Frame [⟨B, 904⟩] s₃.mem s₄.mem := h₄.frame.sub fun r hr => by
    simp only [blockRegions, x1₃, x2₃, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  refine ⟨by rw [r₅, x2₄]; exact BitVec.add_zero _,
    by rw [o₅ _ (by decide), h₄.regs _ (by decide), g₃ _ (by decide) (by decide) (by decide)],
    by rw [o₅ _ (by decide), h₄.regs _ (by decide), g₃ _ (by decide) (by decide) (by decide)], ?_,
    by rw [m₅, core_eq, ← mem₃]; exact fB, fun j hj => ?_, by rw [rd₅, h₄.rd, rd₃'], by rw [wr₅, h₄.wr, wr₃']⟩
  · rw [ReadyAt, m₅, scheduleAt_eq_of_frame _ h₄.frame fun r hr => ?_, mem₃, hr]
    simp only [blockRegions, x1₃, x2₃, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint_base B (by decide) (by omega)
  · have hG : (dirCore d).G = 1 := by cases d <;> rfl
    have hj0 : j = 0 := by omega
    subst hj0
    have ea : blkAddr (dirCore d) B 0 = s₃.gpr .x1 := by rw [x1₃]; rfl
    rw [dirCore_bw, ea, dirCipher_bytes, bytesAt_eq, m₅, h₄.result, mem₃]

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]
  layout := ⟨by cases d <;> decide, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩
  keyRegs_ok := by cases d <;> decide
  regs_ok := by cases d <;> decide
  keyArgs_congr := keyArgs_congr
  ready_frame h hf hd _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.TripleDes.AArch64
