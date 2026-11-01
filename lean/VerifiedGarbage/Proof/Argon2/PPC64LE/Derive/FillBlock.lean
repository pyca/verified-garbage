module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillDep
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillWrite
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillPtr
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Initial
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
import VerifiedGarbage.Proof.Argon2.PPC64LE.Copy
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCall
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on PPC64LE: one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch + 4096`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd wp_addi)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Impl.Argon2.PPC64LE.Derive (passOff counterOff tmpOff curOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : Outside s₀ ⟨scrP s₀, 4096⟩ := by
  have := outside_scr hp (o := 0) (n := 4096) (.inl (by decide))
  simpa using this

/-- `fillCompress`: G of the previous and reference blocks, to `scratch + 4096`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 64 (R * 1024)) :
    WP isa Impl.Argon2.PPC64LE.Derive.fillCompress s fun t => FS s₀ pass slice lane index ctr st t ∧
      (∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s d) ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 4096) =
        compress (blockAt s.mem (matrixCell (memP s₀) (lane * (prm s₀).laneLen +
          (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memP s₀) R)) := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega_arith))
  unfold Impl.Argon2.PPC64LE.Derive.fillCompress Impl.Argon2.PPC64LE.HPrime.mov
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_only k₁
  refine WP.seq (wp_ldloc h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => wp_addi (by decide) fun s₃ u₃ =>
    wp_addi (by decide) fun s₄ u₄ => WP.block_nil ?_)
  have k₄ := ((Only.of_upd u₂).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  have h₄ := h₁.of_only k₄
  have m₄ : s₄.mem = s.mem := by rw [k₄.mem, k₁.mem]
  have ax : s₄.gpr .r3 = memP s₀ + BitVec.ofNat 64 (P * 1024) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₄.gpr .r4 = memP s₀ + BitVec.ofNat 64 (R * 1024) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  have cx : s₄.gpr .r5 = scrP s₀ + BitVec.ofNat 64 4096 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h₁.inv.r31]
  have dx : s₄.gpr .r6 = scrP s₀ := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h₁.inv.r31]; simp
  refine ccall_ok hp h₄.inv dx (o := 4096) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨scrP s₀ + BitVec.ofNat 64 4096, 1024⟩, ⟨scrP s₀, 4096⟩], Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outside_scr hp (.inl (by decide))
    · exact outside_work hp
  refine ⟨h₄.frame hp it f ho, fun d h₁ h₂ => ?_, ?_⟩
  · rw [lw_keep hp f (fun r hr => ⟨scrR s₀, by simp, ?_⟩) h₁ h₂, lw_mem m₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_sub (by decide)
    · exact Region.sub_prefix (by decide)
  · rw [post, ax, sx, m₄]; rfl

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 64 (C * 1024)) :
    WP isa Impl.Argon2.PPC64LE.Derive.fillWrite s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memP s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memP s₀) C) = if pass = 0 then blockAt s.mem (scrP s₀ + BitVec.ofNat 64 4096)
        else xorBlock (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 4096)) (blockAt s.mem (matrixCell (memP s₀) C)) := by
  unfold Impl.Argon2.PPC64LE.Derive.fillWrite
  refine WP.seq (wp_addi (by decide) fun s₁ u₁ => ?_)
  have h₁ := h.of_only (Only.of_upd u₁)
  refine wp_ldloc h₁.inv (d := curOff) (by decide) fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂)
  refine wp_ldloc h₂.inv (d := passOff) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have h₃ := h₂.of_only (Only.of_upd u₃)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have si : s₃.gpr .r4 = scrP s₀ + BitVec.ofNat 64 4096 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.inv.r31]
  have di : s₃.gpr .r6 = memP s₀ + BitVec.ofNat 64 (C * 1024) := by
    rw [u₃.other _ (by decide), u₂.gpr, lw_mem u₁.mem, hcur]
  have Pw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, scrP s₀ + BitVec.ofNat 64 4096 = R.base + BitVec.ofNat 64 off ∧
      off + 1024 ≤ R.len := ⟨scrR s₀, by simp, 4096, rfl, show 4096 + 1024 ≤ 16384 by decide⟩
  have PC : Region.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 4096, 1024⟩ ⟨matrixCell (memP s₀) C, 1024⟩ :=
    (hp.mem_scr.symm.sub_left (scr_sub (by decide))).sub_right (Proof.Argon2.matrixCell_sub _ _ _ hC)
  have done : ∀ (xo : Bool) (t : State), (∀ i < 128, md s₀ t.mem (C * 1024 + 8 * i) = if i < 128 then
        (if xo then s₃.mem.readW (scrP s₀ + BitVec.ofNat 64 4096 + BitVec.ofNat 64 (8 * i)) 64 ^^^
            md s₀ s₃.mem (C * 1024 + 8 * i)
          else s₃.mem.readW (scrP s₀ + BitVec.ofNat 64 4096 + BitVec.ofNat 64 (8 * i)) 64)
        else md s₀ s₃.mem (C * 1024 + 8 * i)) →
      blockAt t.mem (matrixCell (memP s₀) C) = if xo then
        xorBlock (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 4096)) (blockAt s.mem (matrixCell (memP s₀) C))
        else blockAt s.mem (scrP s₀ + BitVec.ofNat 64 4096) :=
    fun xo t wt => by
      apply Vector.ext
      intro j hj
      rw [cell_get _ _ hj, wt j hj, ite_eq_left hj, m₃]
      cases xo
      · simp only [Bool.false_eq_true, ite_false]; rw [blockAt_get _ _ hj]
      · simp only [ite_true]
        rw [xorBlock, Vector.getElem_zipWith, blockAt_get _ _ hj, cell_get _ _ hj]
  refine WP.ite (decide (pass = 0)) (zero_eval (by omega_arith) (by rw [u₃.gpr, h₂.pos.pass]))
    (fun hb => ?_) fun hb => ?_
  · refine ((writeWords_ok hp h₃.inv hC false si Pw PC di 128 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₃]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((writeWords_ok hp h₃.inv hC true si Pw PC di 128 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₃]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.PPC64LE.Derive.fillBlock s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.PPC64LE.Derive.fillBlock
  refine WP.seq ((randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((reference_ok hp ⟨h₁, w₁.1, w₁.2⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide) (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have cur' : lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) < blocksN s₀ := by
    rw [hb]; exact curLt
  have kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memP s₀) j) = blockAt t₃.mem (matrixCell (memP s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) cur' ne
  have lt : ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ t₃ d := fun d h₁ h₂ =>
    lw_keep hp ft (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨memR s₀, by simp, Proof.Argon2.matrixCell_sub _ _ _ cur'⟩) h₁ h₂
  refine ⟨it, Prm.of_lw h₃.pr fun d h₁ h₂ => lt d (by omega_arith) (by omega_arith),
    h₃.pos.of_lw fun d h₁ h₂ => lt d (by omega_arith) (by omega_arith), ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide) (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide) (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [blockAt_keep ft (fun r hr => ?_), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact ((cell_disj hp cur' (scrR s₀) (by simp)).symm.sub_left (scr_sub (by decide)))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end

end VG.Proof.Argon2.PPC64LE.Derive
