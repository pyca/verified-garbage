module

import VerifiedGarbage.Proof.X448.AArch64.FreezePrep
public import VerifiedGarbage.Proof.X448.AArch64.Env
import VerifiedGarbage.Proof.X448.AArch64.Carry
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.AArch64.Swap
import VerifiedGarbage.Proof.Framework.Range

/-! ### `X448.AArch64.Select`, which this module and modules that import it used -/

section

/-!
# X448 on AArch64: selecting the canonical representative

An XOR mask selects each limb from the original value or the carried temporary
value.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def selectStep (i : Nat) : List Instr :=
  [ld .x4 (X2 + 8 * i), ld .x5 (TMP + 8 * i), .logic .eor .x .x5 .x5 .x4,
    .logic .and .x .x5 .x5 .x7, .logic .eor .x .x4 .x4 .x5, st .x4 (X2 + 8 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 16)
    {sw : Bool} (hc : s.gpr .x7 = mask sw) :
    WP isa (.block (selectStep i)) s fun t =>
      t.mem = s.mem.writeW (off base (X2 + 8 * i))
        (if sw then word s.mem base (TMP + 8 * i) else word s.mem base (X2 + 8 * i)) ∧
      Keeps [.x4, .x5] s t := by
  have lx := hs.read (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega_using [hi])
  have ly := hs.read (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega_using [hi])
  have wx := hs.write (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega_using [hi])
  have xe : (X2 + 8 * i) % 8 = 0 ∧ X2 + 8 * i < 32768 := by simp only [X2, slot]; omega_using [hi]
  have ye : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega_using [hi]
  apply WP.of_runBlock
  simp only [selectStep, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, xe, ye, and_self,
    hs.x3, hc, lx, ly, wx, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  rw [BitVec.xor_comm (word s.mem base (TMP + 8 * i)), (xor_sel sw _ _).1]
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .x7 = mask sw) :
    WP isa (.block ((List.range 16).flatMap selectStep)) s fun t =>
      (∀ i < 16, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
      Outside base X2 128 s.mem t.mem ∧ Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
    Outside base X2 (8 * n) s.mem t.mem ∧ Keeps [.x4, .x5] s t
  have st : ∀ n t, n < 16 → inv n t → WP isa (.block (selectStep n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (selectStep_ok (hs.of_keeps tk (by decide)) hn ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (X2 + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [X2, slot]; omega_using [hn])
    refine ⟨?_, (tm.mono (by omega_using []) (by omega_using [])).trans (out.mono (by omega_using []) (by omega_using [])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (X2 + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [X2, slot]; omega_using [hn]) (by simp only [X2, slot]; omega_using [hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h,
        tm.word (Or.inr (by simp only [X2, slot, TMP]; omega_using [])) (by simp only [TMP]; omega_using [hn]),
        tm.word (Or.inr (by omega_using [])) (by simp only [X2, slot]; omega_using [hn])]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 16) inv st 16 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

end

/-!
# X448 on AArch64: canonical reduction

The final carry selects the unique representative below the prime, using only
a mask on secret data.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem freezeMask_ok {s : State} {c : Nat} (hc : (s.gpr .x6).toNat = c) (hb : c < 2) :
    WP isa (.block [.movz .x .x7 0 0, .sub .x .x7 .x7 .x6]) s fun t =>
      t.gpr .x7 = mask (decide (c = 1)) ∧ t.mem = s.mem ∧ Keeps [.x7] s t := by
  have he : s.gpr .x6 = BitVec.ofNat 64 c := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 16) - BitVec.ofNat 64 a =
      mask (decide (a = 1)) := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, BitVec.setWidth_eq,
    RegUpd.gpr_write, he, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨hm c hb, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block freeze) s fun t =>
      Bounded t.mem base X2 ∧ fe t.mem base X2 = fe s.mem base X2 % Spec.X448.P ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  change WP isa (.block ((copy TMP X2 ++ [0, 8].flatMap (fun i =>
    [ld .x4 (TMP + 8 * i), .addImm .x .x4 .x4 1,
      st .x4 (TMP + 8 * i)])) ++ (pass TMP TMP ++
    (([.movz .x .x7 0 0, .sub .x .x7 .x7 .x6] : List Instr) ++
      (List.range 16).flatMap selectStep)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (freezePrep_ok hs hb) fun t ⟨tf, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok (hs.of_keeps tk (by decide)) (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
    tf (freezeCoeff_bound hb)) fun u ⟨uf, uc, um, uk⟩ => ?_
  have cb : carry (freezeCoeff (limbs s.mem base X2)) 16 < 2 := by
    rw [freeze_carry hb]; split <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok uc cb) fun v ⟨vc, vm, vk⟩ => ?_
  have vs := ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (select_ok vs vc) fun w ⟨wf, wm, wk⟩ => ?_
  have outside : Outside base TMP 128 s.mem v.mem := by rw [vm]; exact tm.trans um
  have lf : ∀ i < 16, limbs w.mem base X2 i =
      if carry (freezeCoeff (limbs s.mem base X2)) 16 = 1 then
        digit (freezeCoeff (limbs s.mem base X2)) i else limbs s.mem base X2 i := by
    intro i hi
    rw [wf i hi, outside.limbs (d := X2) (by decide) (by decide) hi, vm, uf i hi]
    simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, (FieldMem.work outside (by decide) (by decide)).trans (FieldMem.output wm),
    (tk.mono ?_).trans ((uk.mono ?_).trans ((vk.mono ?_).trans (wk.mono ?_)))⟩
  · intro i hi; rw [lf i hi]; split
    · exact digit_lt _ _
    · exact hb i hi
  · change valN (limbs w.mem base X2) 16 = _
    rw [valN_congr lf]
    by_cases h : carry (freezeCoeff (limbs s.mem base X2)) 16 = 1
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

end VG.Proof.X448.AArch64
