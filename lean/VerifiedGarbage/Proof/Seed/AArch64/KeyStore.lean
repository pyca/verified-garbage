import VerifiedGarbage.Proof.Seed.AArch64.KeyLoad

/-!
# Copying `G`'s outputs on AArch64

`keyStore_ok`: `keyStore k` copies the sixteen lanes of `G`'s words to the
schedule's words from `k`; `keyMove_ok`: `keyMove` copies the second sixteen
inputs of `G` to its words.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Proof.Seed

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) (hk : k ≤ 16) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        [ldW .x14 (tSlot 0) w, .str .w .x14 .x1 (4 * (k + w))]) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .x14 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hf⟩ := keyStore_ok k hk h hw hsep n (by omega)
    have x5 : t.gpr .x5 = s.gpr .x5 := hg _ (by decide)
    have x1 : t.gpr .x1 = s.gpr .x1 := hg _ (by decide)
    have room : Room t := room_congr h x5 hwr
    have hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, x5]
      refine hf.readW (r := ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr .x5, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega)
    let t1 := t.write .w .x14 (lv t (tSlot 0) n)
    have e1 : exec (ldW .x14 (tSlot 0) n) t = some t1 := exec_ldW_lane room mem_tA (by omega) .x14
    have hw1 : InRegions t1.wr (t1.gpr .x1 + BitVec.ofNat 64 (4 * (k + n))) 4 := by
      simp only [t1, wr_write, gpr_write_of_ne _ _ _ (show ¬ Reg.x1 = .x14 by decide), hwr, x1]
      exact hw n (by omega)
    let t2 := setMem t1 (t.mem.writeW (s.gpr .x1 + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n))
    have e2 : exec (.str .w .x14 .x1 (4 * (k + n))) t1 = some t2 := by
      rw [exec_str_w ⟨by omega, by omega⟩ hw1]
      simp only [t1, t2, gpr_write_self, gpr_write_of_ne _ _ _ (show ¬ Reg.x1 = .x14 by decide), x1,
        mem_write, Size.bits, setWidth_setWidth_32, hlane]
      rfl
    refine ⟨t2, ?_, fun w hw' => ?_, fun r hr => ?_, hrd, hwr, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans ht (by rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some,
        runBlock_nil])
    · simp only [t2, mem_setMem]
      by_cases hwn : w = n
      · subst hwn; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hv w (by omega)
    · simp only [t2, gpr_setMem, t1, gpr_write_of_ne _ _ _ hr]; exact hg r hr
    · simp only [t2, mem_setMem]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [ldW .x14 uSlot w, stW (tSlot 0) w .x14])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_ldW_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_stW_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, gpr_write_self, Size.bits,
        setWidth_setWidth_32, mem_setMem, mem_write,
        laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide)]
    · simp only [gpr_write_of_ne _ _ _ h1, gpr_setMem]

end VG.Proof.Seed.AArch64
