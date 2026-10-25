module

public import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
import VerifiedGarbage.Proof.Curve448.AArch64.Legacy
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.X448.AArch64.Freeze
import VerifiedGarbage.Proof.Curve448.AArch64.Copy
import VerifiedGarbage.Proof.X448.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Ed448 verification on AArch64: comparing slots of the register-resident arithmetic

Untrusted: everything here is checked by Lean. `canon` and `eqSlots`
(`VerifyChecks.lean`) for slots whose limbs are below `2^118` (products of
the register-resident arithmetic).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-- `reduceX2`: `X2`'s eight limbs, those of slot `a` of `m` (below `2^118`), fully reduced into
`X2`, as sixteen 28-bit limbs. -/
theorem reduceX2_ok {s : State} {base : Addr} (hs : Scr s base) {m : Mem} (a : Fin 22)
    (hv : ∀ j < 8, limbs s.mem base X2 j = limbs m base (slot a.val) j)
    (hca : ∀ j < 8, limbs m base (slot a.val) j < 2 ^ 118) :
    WP isa (.block reduceX2) s fun t =>
      VG.Proof.X448.AArch64.Bounded t.mem base X2 ∧ VG.Proof.X448.AArch64.fe t.mem base X2 = (E m base a).val ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  rw [reduceX2, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok' hs (o := X2) (by decide) (by decide)
    (fun i hi => by rw [hv i hi]; exact hca i hi)) fun v ⟨vk, vb, vf⟩ => ?_
  have hsv := hs.of_keeps vk.1 (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.freeze_ok hsv vb) fun t ⟨tb, tv, tm, tk⟩ => ?_
  refine ⟨tb, ?_, vk.2.trans tm, (vk.1.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans tk⟩
  have hF : VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe v.mem base X2) = E m base a := by
    have : VG.Proof.X448.AArch64.F v.mem base X2 = VG.Proof.Curve448.AArch64.F s.mem base X2 := vf
    rw [show VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe v.mem base X2) = VG.Proof.X448.AArch64.F v.mem base X2
      from rfl, this]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr hv)
  rw [tv, ← hF, VG.Proof.X448.toFe_val]

/-- `canon a`: slot `a` (limbs below `2^118`) fully reduced into `X2`, as sixteen 28-bit limbs. -/
theorem canonF_ok {s : State} {base : Addr} (hs : Scr s base) (a : Fin 22) (ha : a ≠ 1)
    (hca : ∀ j < 8, limbs s.mem base (slot a.val) j < 2 ^ 118) :
    WP isa (.block (canon a.val)) s fun t =>
      VG.Proof.X448.AArch64.Bounded t.mem base X2 ∧ VG.Proof.X448.AArch64.fe t.mem base X2 = (E s.mem base a).val ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  have hal := a.isLt
  have hne : a.val ≠ 1 := fun e => ha (Fin.ext e)
  rw [canon, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (o := X2) (a := slot a.val) (by decide)
    (by simp only [slot]; omega_arith) (by decide) (by simp only [slot]; omega_arith)
    (Or.inr (by simp only [X2, slot]; omega_arith))) fun u ⟨ul, uo, uk⟩ => ?_
  refine WP.mono (reduceX2_ok (hs.of_keeps uk (by decide)) a ul hca) fun t ⟨tb, tv, tm, tk⟩ =>
    ⟨tb, tv, (FieldMem.output uo).trans tm, (uk.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans tk⟩

/-! ## The passes of `eqSlots` -/

theorem copy_x8 (o a : Nat) : ∀ i ∈ VG.Impl.Curve448.AArch64.copy o a, clobbers i .x8 = false := by
  intro i hi
  simp only [VG.Impl.Curve448.AArch64.copy, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  obtain ⟨_, _, rfl | rfl⟩ := hi <;> rfl

theorem copy16_x8 (o a : Nat) : ∀ i ∈ VG.Impl.X448.AArch64.copy o a, clobbers i .x8 = false := by
  intro i hi
  simp only [VG.Impl.X448.AArch64.copy, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  obtain ⟨_, _, rfl | rfl⟩ := hi <;> rfl

theorem reduceX2_x8 : ∀ i ∈ reduceX2, clobbers i .x8 = false := by
  have h := instrs_keeps (c := (.block reduceX2 : Prog isa)) (rs := [.x8]) (by decide +kernel)
  intro i hi
  have := List.all_eq_true.mp h i hi
  simpa using this

/-- What follows the count of a pass of `eqSlots` writes no `x8`. -/
theorem passRest_x8 (a b : Nat) :
    ∀ i ∈ instrs (.seq (.ite (.nonzero .x .x8) (.block (VG.Impl.Curve448.AArch64.copy X2 (slot a)))
      (.block (VG.Impl.X448.AArch64.copy CAN X2 ++ VG.Impl.Curve448.AArch64.copy X2 (slot b))))
      (.block reduceX2) : Prog isa), clobbers i .x8 = false := by
  intro i hi
  simp only [instrs, List.mem_append] at hi
  rcases hi with (h | h | h) | h
  · exact copy_x8 _ _ i h
  · exact copy16_x8 _ _ i h
  · exact copy_x8 _ _ i h
  · exact reduceX2_x8 i h

theorem set8_ok (s : State) :
    WP isa (.block [.movz .x .x8 2 0]) s fun t => t.gpr .x8 = BitVec.ofNat 64 2 ∧ Keeps [.x8] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl⟩, rfl⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem dec8_ok (s : State) {n : Nat} (hn : n < 2) (hc : s.gpr .x8 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x8 .x8 1]) s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 n ∧ Keeps [.x8] s t ∧ t.mem = s.mem := by
  have e : BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n := by
    rcases (by omega_arith : n = 0 ∨ n = 1) with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc,
    e, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

/-- Memory that only `X2` and the coefficients change keeps `CAN`. -/
theorem fieldMem_can {base : Addr} {m m' : Mem} (h : FieldMem base X2 m m') {j : Nat} (hj : j < 16) :
    limbs m' base CAN j = limbs m base CAN j :=
  congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ (by
        simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by simp only [CAN]; omega_arith)]
        simp only [X2, slot, CAN]; omega_arith)
      (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by simp only [CAN]; omega_arith)]
          simp only [CAN, ACC]; omega_arith))

/-- The two passes of `eqSlots`, from `x8 = 2`: slot `b` fully reduced into `X2`, and slot `a`
into `CAN`. -/
theorem eqLoop_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Fin 22)
    (hca : ∀ j < 8, limbs s.mem base (slot a.val) j < 2 ^ 118) (hcb : ∀ j < 8, limbs s.mem base (slot b.val) j < 2 ^ 118)
    (ha : a ≠ 1) (hb1 : b ≠ 1) (h8 : s.gpr .x8 = BitVec.ofNat 64 2) :
    WP isa (.loop (eqPass a.val b.val) (.nonzero .x .x8)) s fun t =>
      Keeps workRegs s t ∧ CFrame base s.mem t.mem ∧
      VG.Proof.X448.AArch64.Bounded t.mem base X2 ∧ VG.Proof.X448.AArch64.fe t.mem base X2 = (E s.mem base b).val ∧
      VG.Proof.X448.AArch64.Bounded t.mem base CAN ∧
      VG.Proof.X448.AArch64.fe t.mem base CAN = (E s.mem base a).val := by
  have hal := a.isLt
  have hne : a.val ≠ 1 := fun e => ha (Fin.ext e)
  have hbl := b.isLt
  have hbe : b.val ≠ 1 := fun e => hb1 (Fin.ext e)
  refine WP.loop (M := isa) (fun n (t : State) => (n = 1 ∨ n = 2) ∧ t.gpr .x8 = BitVec.ofNat 64 n ∧
      Keeps workRegs s t ∧ CFrame base s.mem t.mem ∧
      (n = 1 → VG.Proof.X448.AArch64.Bounded t.mem base X2 ∧
        VG.Proof.X448.AArch64.fe t.mem base X2 = (E s.mem base a).val)) ?_ 2 s
    ⟨.inr rfl, h8, Keeps.refl _ _, CFrame.refl _ _, fun h => absurd h (by decide)⟩
  intro n t ⟨hn, ct, kt, ft, e1⟩
  have ht : Scr t base := hs.of_keeps kt (by decide)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_arith⟩
  refine WP.seq (WP.mono (dec8_ok t (n := k) (by omega_arith) ct) fun u ⟨cu, ku, mu⟩ => ?_)
  have hu : Scr u base := ht.of_keeps ku (by decide)
  have kU : Keeps workRegs s u := kt.trans (ku.mono (by decide))
  have fU : CFrame base s.mem u.mem := by rw [mu]; exact ft
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · -- The second pass: slot `a`'s result into `CAN`, slot `b` reduced, and done.
    obtain ⟨bt, et⟩ := e1 rfl
    refine WP.mono (WP.gpr (r := .x8) (Q := fun w => Keeps workRegs s w ∧ CFrame base s.mem w.mem ∧
        VG.Proof.X448.AArch64.Bounded w.mem base X2 ∧ VG.Proof.X448.AArch64.fe w.mem base X2 = (E s.mem base b).val ∧
        VG.Proof.X448.AArch64.Bounded w.mem base CAN ∧
        VG.Proof.X448.AArch64.fe w.mem base CAN = (E s.mem base a).val) ?_ (passRest_x8 a.val b.val))
      fun w ⟨q, w8⟩ => .inl ⟨by simp only [eval, State.read, BitVec.setWidth_eq, w8, cu]; decide, q⟩
    refine WP.seq (WP.ite false (by simp only [eval, State.read, BitVec.setWidth_eq, cu]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.AArch64.copy_ok hu (o := CAN) (a := X2) (by decide) (by decide) (by decide)
      (by decide) (Or.inr (Or.inr (by decide)))) fun v ⟨lv, ov, kv⟩ => ?_
    have hv : Scr v base := hu.of_keeps kv (by decide)
    refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hv (o := X2) (a := slot b.val) (by decide)
      (by simp only [slot]; omega_arith) (by decide) (by simp only [slot]; omega_arith)
      (Or.inr (by simp only [X2, slot]; omega_arith))) fun v' ⟨lv', ov', kv'⟩ => ?_
    have fV : CFrame base s.mem v.mem := fU.trans (CFrame.of_can ov)
    have hl : ∀ j < 8, limbs v'.mem base X2 j = limbs s.mem base (slot b.val) j := fun j hj => by
      rw [lv' j hj, fV.limbs hb1 (by omega_arith)]
    refine WP.mono (reduceX2_ok (hv.of_keeps kv' (by decide)) b hl hcb) fun w ⟨wb, wf, wm, wk⟩ => ?_
    have cw : ∀ j < 16, limbs w.mem base CAN j = limbs u.mem base X2 j := fun j hj => by
      rw [fieldMem_can wm hj, ov'.limbs (by decide) (by decide) hj, lv j hj]
    refine ⟨((kU.trans (kv.mono (fun r hr => List.mem_cons_of_mem _ hr))).trans
        (kv'.mono (fun r hr => List.mem_cons_of_mem _ hr))).trans wk,
      (fV.trans (CFrame.of_field (FieldMem.output ov'))).trans (CFrame.of_field wm), wb, wf,
      fun j hj => by rw [cw j hj, mu]; exact bt j hj, ?_⟩
    rw [← et, ← mu]
    exact VG.Proof.X448.valN_congr fun j hj => cw j hj
  · -- The first pass: slot `a` reduced, and on to the second.
    refine WP.mono (WP.gpr (r := .x8) (Q := fun w => Keeps workRegs s w ∧ CFrame base s.mem w.mem ∧
        VG.Proof.X448.AArch64.Bounded w.mem base X2 ∧ VG.Proof.X448.AArch64.fe w.mem base X2 = (E s.mem base a).val)
        ?_ (passRest_x8 a.val b.val))
      fun w ⟨⟨kw, fw, bw, ew⟩, w8⟩ => .inr ⟨by simp only [eval, State.read, BitVec.setWidth_eq, w8, cu]; decide,
        1, by omega_arith, .inl rfl, by rw [w8, cu], kw, fw, fun _ => ⟨bw, ew⟩⟩
    refine WP.seq (WP.ite true (by simp only [eval, State.read, BitVec.setWidth_eq, cu]; decide)
      (fun _ => ?_) fun h => absurd h (by decide))
    refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hu (o := X2) (a := slot a.val) (by decide)
      (by simp only [slot]; omega_arith) (by decide) (by simp only [slot]; omega_arith)
      (Or.inr (by simp only [X2, slot]; omega_arith))) fun v ⟨lv, ov, kv⟩ => ?_
    have hl : ∀ j < 8, limbs v.mem base X2 j = limbs s.mem base (slot a.val) j := fun j hj => by
      rw [lv j hj, fU.limbs ha (by omega_arith)]
    refine WP.mono (reduceX2_ok (hu.of_keeps kv (by decide)) a hl hca) fun w ⟨wb, wf, wm, wk⟩ =>
      ⟨(kU.trans (kv.mono (fun r hr => List.mem_cons_of_mem _ hr))).trans wk,
        (fU.trans (CFrame.of_field (FieldMem.output ov))).trans (CFrame.of_field wm), wb, wf⟩

/-- `eqSlots a b`: `x20 |= c`, with `c = 0` exactly when slots `a` and `b` hold the same element. -/
theorem eqSlotsF_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Fin 22)
    (hca : ∀ j < 8, limbs s.mem base (slot a.val) j < 2 ^ 118) (hcb : ∀ j < 8, limbs s.mem base (slot b.val) j < 2 ^ 118)
    (ha : a ≠ 1) (hb1 : b ≠ 1) :
    WP isa (eqSlots a.val b.val) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ E s.mem base a = E s.mem base b) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      CKeep base s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base X2 := by
  unfold eqSlots
  refine WP.seq (WP.mono (set8_ok s) fun s1 ⟨c1, k1, m1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps k1 (by decide)
  refine WP.seq (WP.mono (eqLoop_ok hs1 a b (by rw [m1]; exact hca) (by rw [m1]; exact hcb) ha hb1 c1)
    fun w ⟨kw, fw, bw, ew, bc, ec⟩ => ?_)
  have hsw : Scr w base := hs1.of_keeps kw (by decide)
  rw [m1] at fw ew ec
  rw [WP.block_append_iff]
  refine WP.mono (diffCan_ok hsw) fun x ⟨x5, xm, xk⟩ => ?_
  refine WP.mono (orBad_ok x) fun t ⟨t20, tm, tk⟩ => ?_
  refine ⟨⟨x.gpr .x5, ?_, ?_⟩, ?_, by rw [tm, xm]; exact bw⟩
  · rw [x5]
    constructor
    · intro h
      apply Fin.ext
      rw [← ec, ← ew]
      exact VG.Proof.X448.valN_congr fun j hj => (congrArg BitVec.toNat (h j hj)).symm
    · intro h j hj
      have hv : VG.Proof.X448.AArch64.fe w.mem base X2 = VG.Proof.X448.AArch64.fe w.mem base CAN := by
        rw [ew, ec, h]
      exact BitVec.eq_of_toNat_eq (valN_inj 16 bw bc hv j hj)
  · rw [t20, xk.1 _ (by decide), kw.1 _ (by decide), k1.1 _ (by decide)]
  · refine ⟨((k1.mono (by decide)).trans (kw.mono (fun r hr => List.mem_cons_of_mem _ hr))).trans
      ((xk.mono (by decide)).trans (tk.mono (by decide))), ?_⟩
    rw [tm, xm]; exact fw

end VG.Proof.Ed448.AArch64
