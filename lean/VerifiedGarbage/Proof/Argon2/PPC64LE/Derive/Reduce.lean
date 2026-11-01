module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillLoops
public import VerifiedGarbage.Proof.Argon2.FinalReduction
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillWrite
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Parameters
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.HCall
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillDep
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Initial
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on PPC64LE: the final block and the tag

`reduce_ok`: the memory's first block becomes the XOR of every lane's last
block (`Proof.Argon2.reduction`), the other blocks kept; `finalOutput_ok`:
H′ of it to `out`, the tag (`Proof.Argon2.finish_reduction`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_std)
open VG.Spec.Argon2 (Block zeroBlock FillState xorBlock)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Argon2.PPC64LE.Derive (laneOff laneLenOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` stores of `r3 = 0` to `[r6 + 8k]`, `r6` the memory matrix. -/
theorem memZeros_ok {s : State} (h : Inv s₀ s) (hx : s.gpr .r6 = memP s₀) (ha : s.gpr .r3 = 0) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).map fun k => Instr.store .d .r3 .r6 (8 * k))) s fun t =>
      Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨matrixCell (memP s₀) 0, 1024⟩] s.mem t.mem ∧
      ∀ i < n, md s₀ t.mem (8 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have b1 := blocks_pos hp
    have hm := hp.mem_fits
    have b1k : 1024 ≤ blocksN s₀ * 1024 := Nat.le_mul_of_pos_left _ b1
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((memZeros_ok h hx ha n (by omega_arith)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have hc : (memR s₀).Contains (memP s₀ + BitVec.ofNat 64 (8 * n)) 8 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    have hc' : (⟨matrixCell (memP s₀) 0, 1024⟩ : Region).Contains (memP s₀ + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [show matrixCell (memP s₀) 0 = memP s₀ by simp [matrixCell]]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine wp_std (a := memP s₀ + BitVec.ofNat 64 (8 * n)) ⟨by omega_arith, by omega_arith⟩ (by rw [gt, hx])
      ⟨_, by rw [it.wr]; exact mem_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.mupd u₁ ((Frame.refl _ _).writeW (r := memR s₀) (by simp) _ hc), by rw [u₁.gpr, gt], ?_,
        fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, md_store hp _ (by omega_arith) (by omega_arith) (by omega_arith), ha]
      by_cases e : 8 * n = 8 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega_arith)

end

theorem reduction_snoc (p : Spec.Argon2.Params) (M : Array Block) (l : Nat) (acc : Block) :
    Proof.Argon2.reduction p M 0 (l + 1) acc =
      xorBlock (Proof.Argon2.reduction p M 0 l acc) (M[Proof.Argon2.lastIndex p l]?.getD zeroBlock) := by
  unfold Proof.Argon2.reduction
  rw [foldl_range'_snoc, Nat.zero_add]

/-- The state of the reduction after `l` lanes. -/
structure RI (s₀ : State) (M : Array Block) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  lane : lw s₀ s laneOff = BitVec.ofNat 64 l
  first : blockAt s.mem (matrixCell (memP s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 l zeroBlock
  rest : ∀ k < (prm s₀).blocks, k ≠ 0 → blockAt s.mem (matrixCell (memP s₀) k) = M[k]?.getD zeroBlock

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One lane of the reduction. -/
theorem reduceLane_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.reduceLane ++
      Impl.Argon2.PPC64LE.Derive.advanceBy laneOff
        (Impl.Argon2.PPC64LE.Derive.ldw .r4 Impl.Argon2.PPC64LE.Derive.lanesArg)))
      s fun t => RI s₀ M (l + 1) t ∧ VG.PPC64LE.eval (.nonzero .d .r4) t = some (!decide (l + 1 = lanesN s₀)) := by
  have L8 := laneLen_ge hp
  have hlt := hp.lanes_lt
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  have b1 := blocks_pos hp
  obtain ⟨cl, hc'⟩ := cell_fits hp hl (col := (prm s₀).laneLen - 1) (by omega_arith)
  have last : Proof.Argon2.lastIndex (prm s₀) l = l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) := by
    unfold Proof.Argon2.lastIndex; rw [Nat.succ_mul]; omega_arith
  have ne0 : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) ≠ 0 := by omega_arith
  unfold Impl.Argon2.PPC64LE.Derive.reduceLane Impl.Argon2.PPC64LE.Derive.writeBlock
    Impl.Argon2.PPC64LE.HPrime.mov
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁
  refine wp_ldloc i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_subi (by decide) fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂).upd u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega_arith)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, MdStream.PPC64LE.sub_ofNat (by omega_arith)])
    fun s₄ a₄ k₄ => ?_
  have i₄ := i₃.only k₄
  refine wp_addi (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅
  refine wp_lda hp i₅ (i := 13) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, k₄.mem, m₃]
  generalize hc : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) = c at cl hc' a₄ ne0 last
  have sx : s₆.gpr .r4 = matrixCell (memP s₀) c := by
    rw [u₆.other _ (by decide), u₅.gpr, a₄]; simp [matrixCell]
  have dx : s₆.gpr .r6 = memP s₀ + BitVec.ofNat 64 (0 * 1024) := by
    rw [u₆.gpr]; simp
  refine WP.block_append ((writeWords_ok hp i₆ (cur := 0) b1 true sx
    ⟨memR s₀, by simp, c * 1024, rfl, hc'⟩ (cell_other hp cl b1 ne0) dx 128 (Nat.le_refl _)).mono
    fun t₇ ⟨i₇, _, f₇, w₇⟩ => ?_)
  have lt₇ : ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t₇ d = lw s₀ s d := fun d h₁ h₂ => by
    rw [← lw_mem m₆ d]
    exact lw_keep hp f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨memR s₀, by simp, Proof.Argon2.matrixCell_sub _ _ _ b1⟩) h₁ h₂
  unfold Impl.Argon2.PPC64LE.Derive.advanceBy
  refine (advanceTail_ok i₇ (d := laneOff) (n := l) (by decide) (by decide)
    (by rw [lt₇ _ (by decide) (by decide)]; exact h.lane) (by omega_arith) (B := lanesN s₀) (by omega_arith)
    fun v iv _ av => argTail_ok hp iv (i := 7) (by decide) av).mono fun t ⟨it, mt, ot, ct⟩ => ⟨?_, ct⟩
  have kt := loc_keep hp (m := t₇.mem) (d := laneOff) (by decide) (by decide) (BitVec.ofNat 64 (l + 1))
  rw [← mt] at kt
  have new : blockAt t₇.mem (matrixCell (memP s₀) 0) =
      xorBlock (blockAt s.mem (matrixCell (memP s₀) c)) (blockAt s.mem (matrixCell (memP s₀) 0)) := by
    apply Vector.ext
    intro j hj
    rw [cell_get _ _ hj, w₇ j hj, ite_eq_left hj, xorBlock, Vector.getElem_zipWith, blockAt_get _ _ hj,
      cell_get _ _ hj, m₆]
    rfl
  refine ⟨it, Prm.of_lw h.pr fun d h₁ h₂ => ?_, by rw [lw, mt, Mem.readW_writeW_self64], ?_,
    fun k hk k0 => ?_⟩
  · rw [ot d (by omega_arith) (.inl (by simp only [laneOff]; omega_arith)), lt₇ d (by omega_arith) (by omega_arith)]
  · rw [kt.2 _ (by rw [← hb]; exact b1), new, h.first, h.rest _ (by rw [← hb]; exact cl) ne0, reduction_snoc,
      Proof.Argon2.xorBlock_comm, last]
  · rw [kt.2 _ hk, blockAt_keep f₇ (fun r hr => ?_), m₆, h.rest k hk k0]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

/-- The first block of `reduce`: the memory's first block cleared, and the lane `0`. -/
theorem reduceStart_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memP s₀) (prm s₀).blocks M) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.reduceClear ++ Impl.Argon2.PPC64LE.Derive.setLocal laneOff 0)) s
      (RI s₀ M 0) := by
  have b1 := blocks_pos hp
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.PPC64LE.Derive.reduceClear Impl.Argon2.PPC64LE.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_lda hp h (i := 13) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁).upd u₂
  refine WP.block_append ((memZeros_ok hp i₂ (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr 128
    (Nat.le_refl _)).mono fun s₃ ⟨i₃, _, f₃, z₃⟩ => ?_)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have lt₃ : ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ s₃ d = lw s₀ s d := fun d h₁ h₂ => by
    rw [← lw_mem m₂ d]
    exact lw_keep hp f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨memR s₀, by simp, Proof.Argon2.matrixCell_sub _ _ _ b1⟩) h₁ h₂
  refine wp_li (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄
  refine wp_stloc i₄ (d := laneOff) (by decide) fun s₅ i₅ v₅ o₅ _ m₅ => WP.block_nil ?_
  have k₅ := loc_keep hp (m := s₄.mem) (d := laneOff) (by decide) (by decide) (s₄.gpr .r3)
  rw [← m₅] at k₅
  refine ⟨i₅, Prm.of_lw pr fun d h₁ h₂ => ?_, by rw [v₅, u₄.gpr], ?_, fun k hk k0 => ?_⟩
  · rw [o₅ d (by omega_arith) (.inl (by simp only [laneOff]; omega_arith)), lw_mem u₄.mem, lt₃ d (by omega_arith) (by omega_arith)]
  · rw [k₅.2 _ (by rw [← hb]; exact b1), u₄.mem, Proof.Argon2.reduction_zero]
    apply Vector.ext
    intro j hj
    rw [cell_get _ _ hj, Nat.zero_mul, Nat.zero_add, z₃ j hj]
    simp [zeroBlock]
  · rw [k₅.2 _ hk, u₄.mem, blockAt_keep f₃ (fun r hr => ?_), m₂, hm.block k hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0


/-- `reduce`: the XOR of every lane's last block, to the memory's first block. -/
theorem reduce_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memP s₀) (prm s₀).blocks M) :
    WP isa Impl.Argon2.PPC64LE.Derive.reduce s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      blockAt t.mem (matrixCell (memP s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 (lanesN s₀) zeroBlock := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.PPC64LE.Derive.reduce
  refine WP.seq ((reduceStart_ok hp h pr hm).mono fun s₅ start => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ RI s₀ M l t) ?_ (lanesN s₀) s₅
    ⟨0, by omega_arith, hl1, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (reduceLane_ok hp ht hl).mono fun u ⟨hu, cu⟩ => ?_
  by_cases e : l + 1 = lanesN s₀
  · refine .inl ⟨cu.trans (by rw [e]; simp), hu.inv, hu.pr, ?_⟩
    rw [hu.first, e]
  · exact .inr ⟨cu.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, l + 1, rfl, by omega_arith, hu⟩

/-- `finalOutput`: H′ of the memory's first block, to `out`. -/
theorem finalOutput_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.PPC64LE.Derive.finalOutput s fun t => Inv s₀ t ∧
      bytesAt t.mem (outP s₀) (outL s₀) =
        Spec.Argon2.hPrime (outL s₀) (Spec.Argon2.serialize (blockAt s.mem (matrixCell (memP s₀) 0))) := by
  have b1 := blocks_pos hp
  have tg := hp.tag_ge
  have tl := hp.tag_lt
  have b1k : 1024 ≤ blocksN s₀ * 1024 := Nat.le_mul_of_pos_left _ b1
  unfold Impl.Argon2.PPC64LE.Derive.finalOutput Impl.Argon2.PPC64LE.HPrime.mov
  refine WP.seq (wp_lda hp h (i := 13) (by decide) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁
  refine wp_li (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂
  refine wp_lda hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  refine wp_lda hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄
  refine wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := i₄.upd u₅
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .r3 = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : (s₅.gpr .r4).toNat = 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have di : s₅.gpr .r5 = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : (s₅.gpr .r6).toNat = outL s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
  have r7 : s₅.gpr .r7 = scrP s₀ := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r31]; simp
  refine hcall_ok hp i₅ r7
    ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega_arith⟩
    ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega_arith⟩
    (by rw [ax]; decide) (by rw [cx]; exact ⟨by omega_arith, tl⟩) fun t it _ _ post => ⟨it, ?_⟩
  rw [← di, ← cx, post, cx, ax, si, m₅, show matrixCell (memP s₀) 0 = memP s₀ by simp [matrixCell],
    Proof.Argon2.serialize_blockAt]
end

end VG.Proof.Argon2.PPC64LE.Derive
