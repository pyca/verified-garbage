import VerifiedGarbage.Impl.Weierstrass.AArch64.Mont
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# Montgomery products as functions on AArch64: registers saved in vector lanes

The functions save the callee-saved registers they write in the 64-bit lanes
of `v16`–`v20` (`slot i`: the `i`-th register in lane `i % 2` of the
`i / 2`-th): `saves_ok` puts each register in its lane and leaves the other
lanes and every general-purpose register, and `restores_ok` writes each
register back from its lane.
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The lane of the `i`-th saved register. -/
def lane (v : VReg → BitVec 128) (i : Nat) : BitVec 64 :=
  (v (slot i).1).extractLsb' (64 * (slot i).2) 64

theorem extract_setLane (x : BitVec 128) (v : BitVec 64) {i j : Nat} (hi : i < 2) (hj : j < 2) :
    (setLane x 64 i v).extractLsb' (64 * j) 64 = if i = j then v else x.extractLsb' (64 * j) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
    simp only [setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hk, decide_true, Bool.true_and, ite_true, ite_false, Nat.mul_zero, Nat.mul_one,
      Nat.sub_zero, reduceCtorEq] <;>
    (have h1 : k < 128 := by omega
     have h2 : 64 + k < 128 := by omega
     have h3 : ¬ 64 + k < 64 := by omega
     simp [h1, h2, h3, hk])

theorem slot_lt (i : Nat) : (slot i).2 < 2 := Nat.mod_lt _ (by decide)

theorem slot_eq_lt : ∀ i < 10, ∀ j < 10, (slot i).1 = (slot j).1 → (slot i).2 = (slot j).2 → i = j := by
  decide

/-- A block that writes no vector register keeps them. -/
theorem WP.block_novec {is : List Instr} {s : State} {Q : State → Prop}
    (hc : ∀ i ∈ is, vdstOf i = none) (h : WP isa (.block is) s Q) :
    WP isa (.block is) s fun s' => Q s' ∧ s'.v = s.v := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ?_⟩
  cases he with
  | block hb => exact funext fun r => execBlock_vec (fun i hi => by rw [hc i hi]; simp) hb

/-- A lane after the `i`-th register is saved. -/
theorem lane_set (s : State) (x : BitVec 64) {i j : Nat} (hi : i < 10) (hj : j < 10) :
    lane (s.setV (slot i).1 (setLane (s.v (slot i).1) 64 (slot i).2 x)).v j =
      if i = j then x else lane s.v j := by
  unfold lane
  rw [RegUpd.v_setV]
  by_cases h1 : (slot j).1 = (slot i).1
  · simp only [h1, ite_true]
    rw [extract_setLane _ _ (slot_lt i) (slot_lt j)]
    by_cases h2 : (slot i).2 = (slot j).2
    · have := slot_eq_lt i hi j hj h1.symm h2
      subst this; simp
    · have hij : i ≠ j := fun e => h2 (by rw [e])
      simp only [h2, ite_false, hij]
  · have hij : i ≠ j := fun e => h1 (by rw [e])
    simp only [h1, ite_false, hij]

theorem exec_ins {s : State} {d : VReg} {i : Nat} (hi : i < 2) (r : Reg) :
    exec (.vop (.ins .d2 d i r)) s = some (s.setV d (setLane (s.v d) 64 i (s.gpr r))) := by
  simp only [exec, VOp.eval, hi, ite_true, Option.map_some]

theorem exec_umov {s : State} {d : Reg} {n : VReg} {i : Nat} (hi : i < 2) :
    exec (.umov .x d n i) s = some (s.write .x d ((s.v n).extractLsb' (64 * i) 64)) := by
  simp only [exec, Size.bits, show i * 64 < 128 by omega, ite_true, Nat.mul_comm 64 i]

/-- The registers `rs`, the `k`-th on, saved in their lanes. -/
def insCode (rs : List Reg) (k : Nat) : List Instr :=
  (rs.zipIdx k).map fun (r, i) => .vop (.ins .d2 (slot i).1 (slot i).2 r)

/-- The registers `rs`, the `k`-th on, restored from their lanes. -/
def umovCode (rs : List Reg) (k : Nat) : List Instr :=
  (rs.zipIdx k).map fun (r, i) => .umov .x r (slot i).1 (slot i).2

theorem saveCode_eq (n : Nat) : saveCode n = insCode (saved n) 0 := rfl
theorem restoreCode_eq (n : Nat) : restoreCode n = umovCode (saved n) 0 := rfl

/-- What the saves keep: the general-purpose registers, the memory, the
regions, the stack pointer and the flags. -/
structure VKeeps (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  c : s'.c = s.c

/-- Saving `rs` from the `k`-th lane on puts each in its lane and leaves the
lanes before `k` and the vector registers other than the lanes'. -/
theorem saves_ok : ∀ (rs : List Reg) (k : Nat) {s : State}, k + rs.length ≤ 10 →
    WP isa (.block (insCode rs k)) s fun s' => VKeeps s s' ∧
      (∀ i (h : i < rs.length), lane s'.v (k + i) = s.gpr rs[i]) ∧
      (∀ j < k, lane s'.v j = lane s.v j) ∧
      (∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d)
  | [], _, s, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (by simp),
      fun _ _ => rfl, fun _ _ => rfl⟩
  | r :: rs, k, s, hk => by
    simp only [List.length_cons] at hk
    rw [insCode, List.zipIdx_cons, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_ins (slot_lt k), runStep_some, runBlock_nil, Option.some.injEq,
      exists_eq_left']
    refine WP.mono (saves_ok rs (k + 1) (s := s.setV (slot k).1 (setLane (s.v (slot k).1) 64 (slot k).2
      (s.gpr r))) (by omega)) fun s' ⟨K, E, L, V⟩ => ⟨⟨K.gpr, K.mem, K.rd, K.wr, K.sp, K.c⟩, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [L k (by omega), lane_set s (s.gpr r) (by omega) (by omega)]
        simp
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [show k + (i + 1) = k + 1 + i by omega, E i (by simpa using hi)]; rfl
    · intro j hj
      rw [L j (by omega), lane_set s (s.gpr r) (by omega) (by omega)]
      simp only [show k ≠ j by omega, ite_false]
    · intro d hd
      rw [V d hd, RegUpd.v_setV_of_ne _ _ (hd k (by omega))]

/-- Restoring `rs` from the `k`-th lane on writes each from its lane and
keeps the rest. -/
theorem restores_ok : ∀ (rs : List Reg) (k : Nat) {s : State}, k + rs.length ≤ 10 → rs.Nodup →
    WP isa (.block (umovCode rs k)) s fun s' => Keeps rs s s' ∧ s'.v = s.v ∧
      ∀ i (h : i < rs.length), s'.gpr rs[i] = lane s.v (k + i)
  | [], _, s, _, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, rfl,
      fun _ h => absurd h (by simp)⟩
  | r :: rs, k, s, hk, hnd => by
    simp only [List.length_cons] at hk
    have hr := (List.nodup_cons.mp hnd).1
    rw [umovCode, List.zipIdx_cons, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_umov (slot_lt k), runStep_some, runBlock_nil, Option.some.injEq,
      exists_eq_left']
    refine WP.mono (restores_ok rs (k + 1) (by omega) (List.nodup_cons.mp hnd).2)
      fun s' ⟨K, V, E⟩ => ⟨⟨fun q hq => ?_, K.mem, K.rd, K.wr, K.sp⟩, V, ?_⟩
    · simp only [List.mem_cons, not_or] at hq
      rw [K.gpr q hq.2, RegUpd.gpr_write_of_ne _ _ _ hq.1]
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [K.gpr r hr, RegUpd.gpr_write_self, BitVec.setWidth_eq]; rfl
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [E i (by simpa using hi), show k + (i + 1) = k + 1 + i by omega]; rfl

end VG.Proof.Weierstrass.AArch64.Mont
