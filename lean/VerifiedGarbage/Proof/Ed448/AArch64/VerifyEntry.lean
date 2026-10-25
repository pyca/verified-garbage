module

public import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
public import VerifiedGarbage.Proof.X448.AArch64.Setup
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# Ed448 verification's equation on AArch64: the entry and the constants

`ventry`: `x12 = 2^28 - 1`, `x19` and `x20` saved in the working space's
first 16 bytes and the return address at `LRS` (`LrSaved`), `x20 = 0` (no check has failed), every slot zeroed, then `B`
in slots 8–10 and `d` in slot 11, each from immediates (`constSlot`). A
constant slot keeps every slot's limbs bounded (`constE_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Saved store_ok
  word_write_aligned writeW_outside)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv E_outside slot_sep)
open VG.Proof.X448.AArch64.Base (constSlot_ok F_of_words limb_lt)
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Impl.X448.AArch64.Base (constSlot limb)

/-- The return address, saved at `LRS`. -/
def LrSaved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := word m base LRS = g .x30

theorem LrSaved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : LrSaved base g m)
    {o n : Nat} (ho : Outside base o n m m') (hl : LRS + 8 ≤ o ∨ o + n ≤ LRS) : LrSaved base g m' :=
  (ho.word hl (by decide)).trans h

theorem limb_zero (w : Nat) : limb 0 w = 0 := by
  rw [limb, Fin.val_zero, Nat.zero_shiftRight, Nat.zero_mod]; rfl

/-- `x12 := 2²⁸ - 1`. -/
theorem mask12_ok (s : State) :
    WP isa (.block ([.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x12 = 0x0fffffff ∧ Keeps [.x12] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem zero20_ok (s : State) :
    WP isa (.block [.movz .x .x20 0 0]) s fun t =>
      t.gpr .x20 = 0 ∧ t.mem = s.mem ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `x4 := x3 + slot 0`. -/
theorem ptr4_ok (s : State) {base : Addr} (hb : s.gpr .x3 = base) :
    WP isa (.block [.addImm .x .x4 .x3 (slot 0)]) s fun t =>
      t.gpr .x4 = off base (slot 0) ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, slot,
    Nat.reduceMul, Nat.reduceAdd, show (64 : Nat) < 4096 from by decide, ite_true,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, hb, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- The mask, the saves of `x19`, `x20` and the return address, `x20 = 0` and `x4` at slot 0. -/
theorem vhead_ok {s : State} {base : Addr} (hb : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block vhead) s fun t =>
      Scr t base ∧ t.gpr .x20 = 0 ∧ t.gpr .x4 = off base (slot 0) ∧ Saved base s.gpr t.mem ∧ LrSaved base s.gpr t.mem ∧
      Outside base 0 8192 s.mem t.mem ∧ Keeps [.x12, .x20, .x4] s t := by
  rw [show vhead =
      [.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ ([st .x30 LRS] ++ ([.movz .x .x20 0 0] ++
          [.addImm .x .x4 .x3 (slot 0)])))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (mask12_ok s) fun a ⟨a12, ka, ma⟩ => ?_
  have ha : Scr a base := ⟨(ka.1 _ (by decide)).trans hb, a12, by rw [ka.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ha (d := 0) (by decide) (by decide) .x19) fun b ⟨mb, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsb (d := 8) (by decide) (by decide) .x20) fun c ⟨mc, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsc (d := LRS) (by decide) (by decide) .x30) fun c' ⟨mc', kc'⟩ => ?_
  have hsc' := hsc.of_keeps kc' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero20_ok c') fun d ⟨d20, md, kd⟩ => ?_
  have hsd := hsc'.of_keeps kd (by decide)
  refine WP.mono (ptr4_ok d hsd.x3) fun t ⟨t4, mt, kt⟩ => ?_
  have k : Keeps [.x12, .x20, .x4] s t :=
    (((((ka.mono (by simp)).trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans
      (kc'.mono (by simp))).trans (kd.mono (by simp))).trans (kt.mono (by simp))
  have ob : Outside base 0 8192 s.mem b.mem := by
    rw [mb, ← ma]; exact (writeW_outside _ _ _ (by decide)).mono (by omega_arith) (by omega_arith)
  have oc : Outside base 0 8192 b.mem c.mem := by
    rw [mc]; exact (writeW_outside _ _ _ (by decide)).mono (by omega_arith) (by omega_arith)
  have oc' : Outside base 0 8192 c.mem c'.mem := by
    rw [mc']; exact (writeW_outside _ _ _ (by decide)).mono (by simp only [LRS]; omega_arith) (by simp only [LRS]; omega_arith)
  refine ⟨hsd.of_keeps kt (by decide), by rw [kt.1 _ (by decide)]; exact d20, t4, ⟨?_, ?_⟩, ?_,
    by rw [mt, md]; exact (ob.trans oc).trans oc', k⟩
  · rw [mt, md, mc', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), mb, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, ka.1 _ (by decide)]
  · rw [mt, md, mc', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, kb.1 _ (by decide), ka.1 _ (by decide)]
  · show word t.mem base LRS = _
    rw [mt, md, mc', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, kc.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)]

/-- A constant slot, among bounded ones: its value, every slot still bounded,
and the other slots unchanged. -/
theorem constE_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (o : Fin 22) (v : Spec.X448.Fe) :
    WP isa (.block (constSlot (slot o.val) v)) s fun t =>
      BoundedEnv t.mem base ∧ E t.mem base o = v ∧ (∀ i : Fin 22, i ≠ o → E t.mem base i = E s.mem base i) ∧
      Outside base (slot o.val) 64 s.mem t.mem ∧ Keeps [.x4] s t := by
  have ho := o.isLt
  refine WP.mono (constSlot_ok hs (o := slot o.val) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) v)
    fun t ⟨tv, tm, tk⟩ => ⟨fun i j hj => ?_, F_of_words tv, fun i hi => ?_, tm, tk⟩
  · by_cases h : i = o
    · subst h
      show (word t.mem base (slot i.val + 8 * j)).toNat < _
      rw [tv j hj]
      exact Nat.lt_of_lt_of_le (limb_lt v j) (by decide)
    · have hsep := slot_sep h
      rw [show limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j from
        tm.limbs (by omega_arith) (by have := i.isLt; simp only [slot]; omega_arith) (by omega_arith)]
      exact hb i j hj
  · have hsep := slot_sep hi
    exact E_outside tm i (by omega_arith)

/-- The constants, from zeroed slots: every slot bounded, slot 0 zero, `B`
and `d`. -/
theorem vconsts_ok {s : State} {base : Addr} (hs : Scr s base)
    (hz : ∀ i : Fin 22, ∀ w < 8, word s.mem base (slot i.val + 8 * w) = 0) :
    WP isa (.block (constSlot (slot 8) Spec.Ed448.basePoint.X ++ (constSlot (slot 9) Spec.Ed448.basePoint.Y ++
      (constSlot (slot 10) 1 ++ constSlot (slot 11) Spec.Ed448.d)))) s fun t =>
      BoundedEnv t.mem base ∧ E t.mem base 0 = 0 ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Outside base 64 2816 s.mem t.mem ∧ Keeps [.x4] s t := by
  have b0 : BoundedEnv s.mem base := fun i w hw => by
    show (word s.mem base (slot i.val + 8 * w)).toNat < _
    rw [hz i w hw]; decide
  have e0 : E s.mem base 0 = 0 := F_of_words fun w hw => by rw [limb_zero]; exact hz 0 w hw
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok hs b0 8 _) fun t1 ⟨b1, v1, o1, m1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok h1 b1 9 _) fun t2 ⟨b2, v2, o2, m2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok h2 b2 10 1) fun t3 ⟨b3, v3, o3, m3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  refine WP.mono (constE_ok h3 b3 11 _) fun t ⟨b4, v4, o4, m4, k4⟩ => ?_
  refine ⟨b4, ?_, ?_, v4, ?_, ((k1.trans k2).trans k3).trans k4⟩
  · rw [o4 0 (by decide), o3 0 (by decide), o2 0 (by decide), o1 0 (by decide), e0]
  · simp only [pt]
    rw [o4 8 (by decide), o3 8 (by decide), o2 8 (by decide), v1, o4 9 (by decide), o3 9 (by decide), v2,
      o4 10 (by decide), v3]
    rfl
  · simp only [slot] at m1 m2 m3 m4
    exact (((m1.mono (by omega_arith) (by omega_arith)).trans (m2.mono (by omega_arith) (by omega_arith))).trans
      (m3.mono (by omega_arith) (by omega_arith))).trans (m4.mono (by omega_arith) (by omega_arith))

/-! ## Zeroing the slots -/

/-- A store of `x20` at `x4 + 8 i`, with `x4` at offset `d` of the working space. -/
theorem zstore_ok {s : State} {base : Addr} (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {d i : Nat}
    (h4 : s.gpr .x4 = off base d) (hi : i < 8) (hd : d + 64 ≤ 8192) :
    WP isa (.block [.str .x .x20 .x4 (8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (d + 8 * i)) (s.gpr .x20) ∧ Keeps [] s t := by
  have enc : (8 * i) % 8 = 0 ∧ 8 * i < 4096 * 8 := ⟨by omega_arith, by omega_arith⟩
  have hwr : InRegions s.wr (off base (d + 8 * i)) 8 :=
    ⟨_, hw, VG.Proof.X448.AArch64.contains_sc (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Nat.reduceMul,
    enc, and_self, h4, Offset.add_add, State.store, State.read, BitVec.setWidth_eq,
    hwr, ite_true, Option.bind_some, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl⟩

/-- The end of a pass: `x4` moved on by 64 bytes, and `x12` its distance from the end of the slots. -/
theorem zeroTail_ok {s : State} {base : Addr} (h3 : s.gpr .x3 = base) {d : Nat} (h4 : s.gpr .x4 = off base d) :
    WP isa (.block [.addImm .x .x4 .x4 64, .sub .x .x12 .x4 .x3, .subImm .x .x12 .x12 (slot 22)]) s fun t =>
      t.gpr .x4 = off base (d + 64) ∧ t.gpr .x12 = BitVec.ofNat 64 (d + 64) - BitVec.ofNat 64 2880 ∧
      t.mem = s.mem ∧ Keeps [.x4, .x12] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, slot,
    Nat.reduceMul, Nat.reduceAdd, show (64 : Nat) < 4096 from by decide, show (2880 : Nat) < 4096 from by decide,
    ite_true, RegUpd.gpr_write_self, RegUpd.gpr_write, BitVec.setWidth_eq, h4, h3, reduceCtorEq, ite_false,
    Offset.add_add, Offset.add_sub_cancel_left, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- A pass of the loop: the eight words at offset `d` zeroed. -/
theorem zeroPass_ok {s : State} {base : Addr} (h3 : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (h20 : s.gpr .x20 = 0) {d : Nat} (hd : d + 64 ≤ 8192) (h4 : s.gpr .x4 = off base d) :
    WP isa (.block zeroPass) s fun t =>
      t.gpr .x4 = off base (d + 64) ∧ t.gpr .x12 = BitVec.ofNat 64 (d + 64) - BitVec.ofNat 64 2880 ∧
      (∀ i < 8, word t.mem base (d + 8 * i) = 0) ∧ Outside base d 64 s.mem t.mem ∧ Keeps [.x4, .x12] s t := by
  rw [zeroPass, WP.block_append_iff, List.map_eq_flatMap]
  let inv := fun k (u : State) =>
    (∀ i < k, word u.mem base (d + 8 * i) = 0) ∧ Outside base d 64 s.mem u.mem ∧ Keeps [] s u
  have step : ∀ k u, k < 8 → inv k u →
      WP isa (.block [.str .x .x20 .x4 (8 * k)]) u (inv (k + 1)) := by
    intro k u hk ⟨uf, um, uk⟩
    refine WP.mono (zstore_ok (base := base) (by rw [uk.2.2]; exact hw) (by rw [uk.1 _ (by decide)]; exact h4) hk hd)
      fun v ⟨vm, vk⟩ => ?_
    rw [uk.1 _ (by decide), h20] at vm
    have out : Outside base (d + 8 * k) 8 u.mem v.mem := by
      rw [vm]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega_arith)
    refine ⟨fun i hi => ?_, um.trans (out.mono (by omega_arith) (by omega_arith)), uk.trans vk⟩
    rw [vm, VG.Proof.X448.AArch64.word_write u.mem base (by omega_arith) (by omega_arith)]
    by_cases h : i = k
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact uf i (by omega_arith)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (zeroTail_ok (by rw [uk.1 _ (by decide)]; exact h3) (by rw [uk.1 _ (by decide)]; exact h4))
    fun t ⟨t4, t12, tm, tk⟩ => ⟨t4, t12, fun i hi => by rw [tm]; exact uf i hi, by rw [tm]; exact um,
      (uk.mono (by simp)).trans tk⟩

theorem zeroExit (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 44) :
    (BitVec.ofNat 64 (64 + 64 * (44 - n) + 64) - BitVec.ofNat 64 2880 != 0) = decide (n ≠ 1) := by
  have : ∀ n < 45, 1 ≤ n →
      (BitVec.ofNat 64 (64 + 64 * (44 - n) + 64) - BitVec.ofNat 64 2880 != 0) = decide (n ≠ 1) := by decide
  exact this n (by omega_arith) h1

/-- The loop: the 352 words of the slots zeroed, 44 passes of `zeroPass`. -/
theorem zeroLoop_ok {s : State} {base : Addr} (h3 : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (h20 : s.gpr .x20 = 0) (h4 : s.gpr .x4 = off base (slot 0)) :
    WP isa (.loop (.block zeroPass) (.nonzero .x .x12)) s fun t =>
      (∀ i < 352, word t.mem base (slot 0 + 8 * i) = 0) ∧ Outside base (slot 0) 2816 s.mem t.mem ∧
      Keeps [.x4, .x12] s t := by
  refine WP.loop (M := isa) (fun n (t : State) => 1 ≤ n ∧ n ≤ 44 ∧
      t.gpr .x4 = off base (64 + 64 * (44 - n)) ∧ (∀ i < 8 * (44 - n), word t.mem base (64 + 8 * i) = 0) ∧
      Outside base 64 2816 s.mem t.mem ∧ Keeps [.x4, .x12] s t) ?_ 44 s
    ⟨by decide, by decide, h4, fun _ hi => absurd hi (by omega_arith), Outside.refl _ _ _ _, Keeps.refl _ _⟩
  intro n t ⟨hn1, hn2, t4, tz, tm, tk⟩
  refine WP.mono (zeroPass_ok (by rw [tk.1 _ (by decide)]; exact h3) (by rw [tk.2.2]; exact hw)
    (by rw [tk.1 _ (by decide)]; exact h20) (by omega_arith) t4) fun u ⟨u4, u12, uz, um, uk⟩ => ?_
  have uz' : ∀ i < 8 * (44 - n) + 8, word u.mem base (64 + 8 * i) = 0 := fun i hi => by
    by_cases h : i < 8 * (44 - n)
    · rw [um.word (Or.inl (by omega_arith)) (by omega_arith)]; exact tz i h
    · have := uz (i - 8 * (44 - n)) (by omega_arith)
      rwa [show 64 + 64 * (44 - n) + 8 * (i - 8 * (44 - n)) = 64 + 8 * i by omega_arith] at this
  have uM : Outside base 64 2816 s.mem u.mem := tm.trans (um.mono (by omega_arith) (by omega_arith))
  have uK : Keeps [.x4, .x12] s u := tk.trans uk
  simp only [eval, State.read, BitVec.setWidth_eq, u12, zeroExit n hn1 hn2]
  by_cases h : n = 1
  · subst h
    refine .inl ⟨rfl, fun i hi => uz' i (by omega_arith), uM, uK⟩
  · refine .inr ⟨by simp only [ne_eq, h, not_false_eq_true, decide_true], n - 1, by omega_arith, by omega_arith, by omega_arith,
      by rw [u4, show 64 + 64 * (44 - n) + 64 = 64 + 64 * (44 - (n - 1)) by omega_arith], fun i hi => uz' i (by omega_arith), uM, uK⟩

/-- The entry: the registers, the saves, the zeroed slots and the constants. -/
theorem ventry_ok {s : State} {base : Addr} (hb : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa ventry s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ Saved base s.gpr t.mem ∧ LrSaved base s.gpr t.mem ∧
      t.gpr .x20 = 0 ∧ Keeps [.x12, .x20, .x4] s t ∧ Outside base 0 8192 s.mem t.mem ∧
      E t.mem base 0 = 0 ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d := by
  unfold ventry
  refine WP.seq (WP.mono (vhead_ok hb hw hn) fun a ⟨ha, a20, a4, sa, la, oa, ka⟩ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok ha.x3 ha.wr a20 a4) fun b ⟨zb, ob, kb⟩ => ?_)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mask12_ok b) fun c ⟨c12, kc, mc⟩ => ?_
  have hsc : Scr c base := ⟨(kc.1 _ (by decide)).trans ((kb.1 _ (by decide)).trans ha.x3), c12,
    by rw [kc.2.2, kb.2.2]; exact ha.wr, hn⟩
  have zs : ∀ i : Fin 22, ∀ w < 8, word c.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := zb (16 * i.val + w) (by omega_arith)
    rwa [mc, show slot i.val + 8 * w = slot 0 + 8 * (16 * i.val + w) by simp only [slot]; omega_arith]
  refine WP.mono (vconsts_ok hsc zs) fun t ⟨bt, e0, pB, dt, ot, kt⟩ => ?_
  have obc : Outside base (slot 0) 2816 a.mem c.mem := by rw [mc]; exact ob
  refine ⟨hsc.of_keeps kt (by decide), bt, (sa.outside obc (by decide)).outside ot (by decide),
    (la.outside obc (by simp only [LRS, slot]; omega_arith)).outside ot (by simp only [LRS]; omega_arith),
    by rw [kt.1 _ (by decide), kc.1 _ (by decide), kb.1 _ (by decide)]; exact a20,
    ((ka.trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans (kt.mono (by simp)), ?_, e0, pB, dt⟩
  exact ((oa.mono (by omega_arith) (by omega_arith)).trans (obc.mono (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith))).trans (ot.mono (by omega_arith) (by omega_arith))

end VG.Proof.Ed448.AArch64
