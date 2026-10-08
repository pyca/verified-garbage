import VerifiedGarbage.Proof.Seed.X86_64.KeyLoad

/-!
# Copying `G`'s outputs on x86-64

`keyStore_ok`: `keyStore k` copies the sixteen lanes of `G`'s words to the
schedule's words from `k`; `keyMove_ok`: `keyMove` copies the second sixteen
inputs of `G` to its words.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

-- The steps share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .rsi + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) (hk : 4 * k + 64 < 2 ^ 64) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        [.mov32 .rax (.mem (lane .r9 (tSlot 0) w)),
         .store32 { base := .rsi, disp := ((4 * (k + w) : Nat) : Int) } .rax]) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hf⟩ := keyStore_ok k h hw hsep hk n (by omega)
    have r9 : t.gpr .r9 = s.gpr .r9 := hg _ (by decide)
    have rsi : t.gpr .rsi = s.gpr .rsi := hg _ (by decide)
    have room : Room t := room_congr h r9 hwr
    have hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, r9]
      refine hf.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr .r9, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega)
    let t1 := t.setReg32 .rax (lv t (tSlot 0) n)
    have e1 : exec (.mov32 .rax (.mem (lane .r9 (tSlot 0) n))) t = some t1 :=
      exec_mov32_lane room (by decide) (by omega) .rax
    have hea : t1.ea { base := .rsi, disp := ((4 * (k + n) : Nat) : Int) } =
        s.gpr .rsi + BitVec.ofNat 64 (4 * (k + n)) := by
      rw [ea_off]; simp only [t1, State.setReg32, gpr_setReg]; simp [rsi]
    have hw1 : InRegions t1.wr (t1.ea { base := .rsi, disp := ((4 * (k + n) : Nat) : Int) }) 4 := by
      rw [hea]; simp only [t1, State.setReg32, wr_setReg, hwr]; exact hw n (by omega)
    let t2 := setMem t1 (t.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n))
    have e2 : exec (.store32 { base := .rsi, disp := ((4 * (k + n) : Nat) : Int) } .rax) t1 = some t2 := by
      rw [exec_store32 hw1, hea]
      simp only [t1, t2, State.setReg32, gpr_setReg, ite_true, setWidth_setWidth_32, hlane]
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
    · simp only [t2, gpr_setMem, t1, State.setReg32, gpr_setReg, hr, ite_false]; exact hg r hr
    · simp only [t2, mem_setMem]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [.mov32 .rax (.mem (lane .r9 uSlot w)), .store32 (lane .r9 (tSlot 0) w) .rax])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_mov32_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_store32_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, State.setReg32, gpr_setReg,
        reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, mem_setMem, mem_setReg, laneA_setMem,
        laneA_setReg _ _ (show ¬ Reg.r9 = .rax by decide)]
    · simp only [State.setReg32, gpr_setReg, gpr_setMem, h1, ↓reduceIte]

end VG.Proof.Seed.X86_64
