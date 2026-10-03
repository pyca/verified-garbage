import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Group
import VerifiedGarbage.Proof.Rc2.CbcList

/-!
# The loop over groups

`loopV_ok`: `j` groups of eight blocks at `x1`, decrypted in CBC mode from the
chaining value in `x11`, which is left the last ciphertext block.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec VG.Proof.Rc2

/-- A group, as CBC on its eight blocks. -/
theorem GroupPost.cbc {m : Mem} {p : Addr} {t t' : State} (h : GroupPost m p t t') :
    Spec.Rc2.blocksAt t'.mem (t.gpr .x1) 8 = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p) .decrypt
      (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) 8)).1 ∧
    wordBlock (t'.gpr .x11) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p) .decrypt
      (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) 8)).2 := by
  rw [cbc_decrypt]
  constructor
  · apply List.ext_getElem (by simp [blocksAt_length])
    intro i h₁ h₂
    have hi : i < 8 := by simpa [blocksAt_length] using h₁
    rw [List.getElem_zipWith, blocksAt_getElem, blocksAt_getElem, h.data i hi, prevBlock]
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.getElem_cons_succ, blocksAt_getElem, Nat.add_sub_cancel, Nat.add_one_ne_zero,
        ite_false]
  · rw [h.chain, ← blockAt_read64, List.getLast_eq_getElem]
    simp only [List.length_cons, blocksAt_length, Nat.add_sub_cancel, List.getElem_cons_succ,
      blocksAt_getElem]

structure LoopVPost (m : Mem) (p : Addr) (t : State) (j : Nat) (t' : State) : Prop where
  ptr : t'.gpr .x1 = t.gpr .x1 + BitVec.ofNat 64 (64 * j)
  count : t'.gpr .x10 = 0
  reg : ∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
    t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  frame : Frame [⟨t.gpr .x1, 64 * j⟩] t.mem t'.mem
  data : Spec.Rc2.blocksAt t'.mem (t.gpr .x1) (8 * j) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p)
    .decrypt (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) (8 * j))).1
  chain : wordBlock (t'.gpr .x11) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p)
    .decrypt (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) (8 * j))).2

theorem ofNat_ne_zero {a : Nat} (h : 0 < a) (h' : a < 2 ^ 64) : BitVec.ofNat 64 a ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h', show (0 : BitVec 64).toNat = 0 from rfl] at this
  omega

theorem loopV_ok (m : Mem) (p : Addr) (j : Nat) :
    ∀ t : State, 1 ≤ j → 64 * j < 2 ^ 64 → SchedV t m p → t.v m16 = mask16 →
      t.gpr .x10 = BitVec.ofNat 64 j →
      InRegions (t.rd ++ t.wr) (t.gpr .x1) (64 * j) → InRegions t.wr (t.gpr .x1) (64 * j) →
      WP isa (.loop (.block group) (.nonzero .x .x10)) t (LoopVPost m p t j) := by
  induction j with
  | zero => intro t h; omega
  | succ j ih =>
    intro t _ bound hs hm count hrd hwr
    have z : t.gpr .x1 + BitVec.ofNat 64 0 = t.gpr .x1 := BitVec.add_zero _
    obtain ⟨t₀, s₁, exec₁, h₁⟩ := group_ok (m := m) (p := p) t hs hm
      (by have := CallLay.inRegions_sub hrd (by omega : 0 + 64 ≤ 64 * (j + 1)) (by omega)
          rwa [z] at this)
      (by have := CallLay.inRegions_sub hwr (by omega : 0 + 64 ≤ 64 * (j + 1)) (by omega)
          rwa [z] at this)
    have c₁ : s₁.gpr .x10 = BitVec.ofNat 64 j := by
      rw [h₁.count, count, Offset.ofNat_sub_ofNat (by omega)]; rfl
    have g8 := h₁.cbc
    by_cases hz : j = 0
    · subst hz
      refine ⟨_, s₁, Exec.loopExit exec₁ (by simp [eval, State.read, c₁]), ?_⟩
      refine ⟨by rw [h₁.ptr], c₁, fun g a b c d e f i => h₁.reg g a b c d e f i, h₁.rd, h₁.wr,
        h₁.sp, h₁.frame, g8.1, g8.2⟩
    · obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) h₁.sched h₁.mask c₁
        (by rw [h₁.rd, h₁.wr, h₁.ptr]; exact CallLay.inRegions_sub hrd (by omega) (by omega))
        (by rw [h₁.wr, h₁.ptr]; exact CallLay.inRegions_sub hwr (by omega) (by omega))
      refine ⟨_, s₂, Exec.loopNext exec₁ (by
        simp [eval, State.read, c₁]; exact ofNat_ne_zero (by omega) (by omega)) exec₂, ?_⟩
      let q := t.gpr .x1
      have q₁ : s₁.gpr .x1 = q + BitVec.ofNat 64 64 := h₁.ptr
      -- The first group's blocks, left by the rest; the rest's, by the first.
      have keepFirst : Spec.Rc2.blocksAt s₂.mem q 8 = Spec.Rc2.blocksAt s₁.mem q 8 :=
        blocksAt_frame h₂.frame q 8 (by
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          rw [q₁]
          exact Offset.base_disjoint q (by omega) (by omega))
      have keepRest : Spec.Rc2.blocksAt s₁.mem (q + BitVec.ofNat 64 64) (8 * j) =
          Spec.Rc2.blocksAt t.mem (q + BitVec.ofNat 64 64) (8 * j) :=
        blocksAt_frame h₁.frame _ _ (by
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact Offset.disjoint_base q (by omega) (by omega))
      have split : ∀ mm : Mem, Spec.Rc2.blocksAt mm q (8 * (j + 1)) =
          Spec.Rc2.blocksAt mm q 8 ++ Spec.Rc2.blocksAt mm (q + BitVec.ofNat 64 64) (8 * j) :=
        fun mm => by rw [show 8 * (j + 1) = 8 + 8 * j by omega, blocksAt_add]
      have data₂ := h₂.data
      have chain₂ := h₂.chain
      rw [q₁, keepRest, g8.2] at data₂ chain₂
      refine ⟨?_, h₂.count, fun g a b c d e f i => (h₂.reg g a b c d e f i).trans
        (h₁.reg g a b c d e f i), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, ?_, ?_, ?_⟩
      · rw [h₂.ptr, q₁, Offset.add_add, show 64 + 64 * j = 64 * (j + 1) by omega]
      · refine (h₁.frame.sub ?_).trans (h₂.frame.sub ?_)
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          rw [q₁]
          exact ⟨_, List.mem_singleton_self _, Offset.sub_base q (by omega)⟩
      · rw [split, split, keepFirst, g8.1, cbc_append, data₂]
      · rw [chain₂, split, cbc_append]

end VG.Proof.Rc2.AArch64.Vec
