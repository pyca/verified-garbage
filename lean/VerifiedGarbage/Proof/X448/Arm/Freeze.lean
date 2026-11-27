module

import VerifiedGarbage.Proof.X448.Arm.FreezePrep
public import VerifiedGarbage.Proof.X448.Arm.Env
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.Arm.Swap
import VerifiedGarbage.Proof.Framework.Range

/-! ### `X448.Arm.Select`, which only this module used -/

section

/-!
# X448 on ARMv7: selecting the canonical representative

An XOR mask selects each limb from the original value or the carried temporary
value.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def selectStep (i : Nat) : List Instr :=
  [ld .r3 (X2 + 4 * i), ld .r2 (TMP + 4 * i), .dp .eor .r2 .r2 (.reg .r3),
    .dp .and .r2 .r2 (.reg .r4), .dp .eor .r3 .r3 (.reg .r2), st .r3 (X2 + 4 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 28)
    {sw : Bool} (hc : s.gpr .r4 = mask sw) :
    WP isa (.block (selectStep i)) s fun t =>
      t.mem = s.mem.writeW (off base (X2 + 4 * i))
        (if sw then word s.mem base (TMP + 4 * i) else word s.mem base (X2 + 4 * i)) ∧
      Keeps [.r3, .r2] s t := by
  unfold selectStep
  refine load_ok hs (by simp only [X2, slot]; omega_using [hi]) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine load_ok ts (by simp only [TMP]; omega_using [hi]) fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun v hv => ?_
  have vs := us.of_upd hv (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun w hw => ?_
  have ws := vs.of_upd hw (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun x hx => ?_
  have xs := ws.of_upd hx (by decide) (by decide)
  refine store_ok xs (by simp only [X2, slot]; omega_using [hi]) fun y hy => WP.block_nil ⟨?_, ?_⟩
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, ht.mem, hx.gpr]
    change _ = s.mem.writeW _ _
    rw [hw.other .r3 (by decide), hv.other .r3 (by decide), hu.other .r3 (by decide), ht.gpr,
      hw.gpr, hv.gpr, hu.gpr, ht.mem, hu.other .r3 (by decide), ht.gpr,
      hv.other .r4 (by decide), hu.other .r4 (by decide), ht.other .r4 (by decide), hc]
    change s.mem.writeW _ (_ ^^^ ((_ ^^^ _) &&& mask sw)) = _
    rw [BitVec.xor_comm (word s.mem base (TMP + 4 * i)), (xor_sel sw _ _).1]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans ((hw.rest (by decide)).trans ((hx.rest (by decide)).trans (hy.rest _))))))

theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .r4 = mask sw) :
    WP isa (.block ((List.range 28).flatMap selectStep)) s fun t =>
      (∀ i < 28, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
      Outside base X2 112 s.mem t.mem ∧ Keeps [.r3, .r2] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
    Outside base X2 (4 * n) s.mem t.mem ∧ Keeps [.r3, .r2] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (selectStep n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (selectStep_ok (hs.of_keeps tk (by decide)) hn ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (X2 + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [X2, slot]; omega_using [hn])
    refine ⟨?_, (tm.mono (by omega_using []) (by omega_using [])).trans (out.mono (by omega_using []) (by omega_using [])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (X2 + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [X2, slot]; omega_using [hn]) (by simp only [X2, slot]; omega_using [hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h,
        tm.word (Or.inr (by simp only [X2, slot, TMP]; omega_using [])) (by simp only [TMP]; omega_using [hn]),
        tm.word (Or.inr (by omega_using [])) (by simp only [X2, slot]; omega_using [hn])]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

end

/-!
# X448 on ARMv7: canonical reduction

The final carry selects the unique representative below the prime, using only
a mask on secret data.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem freezeMask_ok {s : State} {c : Nat} (hc : (s.gpr .r5).toNat = c) (hb : c < 2) :
    WP isa (.block [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)]) s fun t =>
      t.gpr .r4 = mask (decide (c = 1)) ∧ t.mem = s.mem ∧ Keeps [.r4] s t := by
  have he : s.gpr .r5 = BitVec.ofNat 32 c := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = mask (decide (a = 1)) := by decide
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u hu => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hu.gpr]; change t.gpr .r4 - t.gpr .r5 = _
    rw [ht.gpr, ht.other .r5 (by decide), he]; exact hm c hb
  · exact hu.mem.trans ht.mem
  · exact rest_keeps ((ht.rest (by decide)).trans (hu.rest (by decide)))

theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block freeze) s fun t =>
      Bounded t.mem base X2 ∧ fe t.mem base X2 = fe s.mem base X2 % Spec.X448.P ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  change WP isa (.block ((copy TMP X2 ++ [0, 14].flatMap (fun i =>
    [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.imm 1),
      st .r3 (TMP + 4 * i)])) ++ (pass TMP TMP ++
    (([.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)] : List Instr) ++
      (List.range 28).flatMap selectStep)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (freezePrep_ok hs hb) fun t ⟨tf, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok (hs.of_keeps tk (by decide)) (by decide) (by decide) (Or.inl rfl)
    tf (fun i hi => Nat.le_of_lt (freezeCoeff_bound hb i hi))) fun u ⟨uf, uc, um, uk⟩ => ?_
  have cb : carry (freezeCoeff (limbs s.mem base X2)) 28 < 2 := by
    rw [freeze_carry hb]; split <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok uc cb) fun v ⟨vc, vm, vk⟩ => ?_
  have vs := ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (select_ok vs vc) fun w ⟨wf, wm, wk⟩ => ?_
  have outside : Outside base TMP 112 s.mem v.mem := by rw [vm]; exact tm.trans um
  have lf : ∀ i < 28, limbs w.mem base X2 i =
      if carry (freezeCoeff (limbs s.mem base X2)) 28 = 1 then
        digit (freezeCoeff (limbs s.mem base X2)) i else limbs s.mem base X2 i := by
    intro i hi
    rw [wf i hi, outside.limbs (d := X2) (by decide) (by decide) hi, vm, uf i hi]
    simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, (FieldMem.work outside (by decide) (by decide)).trans (FieldMem.output wm),
    (tk.mono ?_).trans ((uk.mono ?_).trans ((vk.mono ?_).trans (wk.mono ?_)))⟩
  · intro i hi; rw [lf i hi]; split
    · exact digit_lt _ _
    · exact hb i hi
  · change valN (limbs w.mem base X2) 28 = _
    rw [valN_congr lf]
    by_cases h : carry (freezeCoeff (limbs s.mem base X2)) 28 = 1
    · simp only [h, ite_true]
      exact (ite_eq_left h).symm.trans (freeze_value hb)
    · simp only [h, ite_false]
      exact (ite_eq_right h).symm.trans (freeze_value hb)
  · intro r hr; exact List.mem_cons_of_mem _ hr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.Arm
