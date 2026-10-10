import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Registers kept in vector lanes, on AArch64

Code that keeps registers in 64-bit lanes of vector registers (`ins vd.d[l], r`,
`insOf`) and reads them back (`umov r, vd.d[l]`, `umovOf`): `insOf_ok` sets the
lanes and changes nothing else, `umovOf_ok` sets the registers from them, so
that a function can keep the callee-saved registers it writes without a stack
frame.
-/

namespace VG.AArch64

/-- The instructions keeping registers in lanes. -/
def insOf (ks : List (Reg × VReg × Nat)) : List Instr := ks.map fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)

/-- The instructions restoring them. -/
def umovOf (ks : List (Reg × VReg × Nat)) : List Instr := ks.map fun k => .umov .x k.1 k.2.1 k.2.2

theorem exec_ins {s : State} {r : Reg} {v : VReg} {l : Nat} (hl : l < 2) :
    exec (.vop (.ins .d2 v l r)) s = some (s.setV v (setLane (s.v v) 64 l (s.gpr r))) := by
  simp only [exec, VOp.eval, hl, ite_true, Option.map_some]

theorem exec_umov {s : State} {r : Reg} {v : VReg} {l : Nat} (hl : l < 2) :
    exec (.umov .x r v l) s = some (s.write .x r (laneOf s v l)) := by
  have : 64 * l < 128 := by omega
  simp only [exec, Size.bits, laneOf, Nat.mul_comm l 64, this, ite_true]

theorem laneOf_setV {s : State} {v w : VReg} {x : BitVec 128} {l : Nat} :
    laneOf (s.setV v x) w l = if w = v then x.extractLsb' (64 * l) 64 else laneOf s w l := by
  simp only [laneOf, RegUpd.v_setV]
  split <;> rfl

/-- Keeping the registers of `ks` in their lanes, distinct and below 2. -/
theorem insOf_ok : ∀ (ks : List (Reg × VReg × Nat)) (s : State), (∀ k ∈ ks, k.2.2 < 2) →
    (ks.map fun k => (k.2.1, k.2.2)).Nodup →
    WP isa (.block (insOf ks)) s fun t => t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ (∀ k ∈ ks, laneOf t k.2.1 k.2.2 = s.gpr k.1) ∧
      ∀ v l, l < 2 → (v, l) ∉ ks.map (fun k => (k.2.1, k.2.2)) → laneOf t v l = laneOf s v l
  | [], s, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, by simp, fun _ _ _ _ => rfl⟩
  | k :: ks, s, hl, hn => by
    have hk := hl k List.mem_cons_self
    refine WP.block_cons_iff.mpr ⟨_, exec_ins hk, ?_⟩
    obtain ⟨hn₁, hn₂⟩ := List.nodup_cons.mp hn
    refine WP.mono (insOf_ok ks _ (fun k' h => hl k' (List.mem_cons_of_mem _ h)) hn₂)
      fun t ⟨hg, hm, hr, hw, hsp, hls, hoth⟩ => ?_
    have lane : ∀ v l, l < 2 →
        laneOf (s.setV k.2.1 (setLane (s.v k.2.1) 64 k.2.2 (s.gpr k.1))) v l =
          if v = k.2.1 ∧ l = k.2.2 then s.gpr k.1 else laneOf s v l := fun v l hl' => by
      rw [laneOf_setV]
      by_cases hv : v = k.2.1
      · subst hv
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), extract_setLane64 _ _ hk hl']
        by_cases hll : k.2.2 = l
        · subst hll; simp
        · simp only [hll, ite_false, laneOf, true_and, Ne.symm hll]
      · simp [hv]
    refine ⟨hg, hm, hr, hw, hsp, fun k' hk' => ?_, fun v l hl' hvl => ?_⟩
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · rw [hoth _ _ hk hn₁, lane _ _ hk, ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩)]
      · rw [hls k' hk', RegUpd.gpr_setV]
    · simp only [List.map_cons, List.mem_cons, not_or] at hvl
      rw [hoth v l hl' hvl.2, lane v l hl', ite_eq_right_of_eq_false _ _ (eq_false fun h => hvl.1 (by rw [h.1, h.2]))]

/-- Restoring the registers of `ks`, distinct, from their lanes. -/
theorem umovOf_ok : ∀ (ks : List (Reg × VReg × Nat)) (s : State), (∀ k ∈ ks, k.2.2 < 2) →
    (ks.map Prod.fst).Nodup →
    WP isa (.block (umovOf ks)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ k ∈ ks, t.gpr k.1 = laneOf s k.2.1 k.2.2) ∧ ∀ r, r ∉ ks.map Prod.fst → t.gpr r = s.gpr r
  | [], s, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, by simp, fun _ _ => rfl⟩
  | k :: ks, s, hl, hn => by
    have hk := hl k List.mem_cons_self
    refine WP.block_cons_iff.mpr ⟨_, exec_umov hk, ?_⟩
    obtain ⟨hn₁, hn₂⟩ := List.nodup_cons.mp hn
    refine WP.mono (umovOf_ok ks _ (fun k' h => hl k' (List.mem_cons_of_mem _ h)) hn₂)
      fun t ⟨hm, hr, hw, hsp, hls, hoth⟩ => ?_
    have hlane : ∀ v l, laneOf (s.write .x k.1 (laneOf s k.2.1 k.2.2)) v l = laneOf s v l := fun _ _ => rfl
    refine ⟨hm, hr, hw, hsp, fun k' hk' => ?_, fun r hr' => ?_⟩
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · rw [hoth _ hn₁, RegUpd.gpr_write_self]; rfl
      · rw [hls k' hk', hlane]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr'
      rw [hoth r hr'.2, RegUpd.gpr_write_of_ne _ _ _ hr'.1]

end VG.AArch64
