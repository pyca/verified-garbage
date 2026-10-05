import VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall
import VerifiedGarbage.Proof.X448.Wide.TailMul
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.AArch64.Target

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.PointwiseOps`. -/
section

/-! Untrusted: fused pointwise operations satisfy the existing slot contract. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem pointwiseAdd_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Pointwise.add o a b)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a + VG.Proof.X448.AArch64.F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [VG.Proof.X448.radix] at h1 h2
    omega
  refine WP.mono (pointwiseFused_ok hs ho ho8 fb ?_)
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_add ?_⟩
  · intro i hi t ts tm
    refine WP.mono (addEval_ok ts ha ha8 hb hb8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk⟩
    rw [input_limb tm ha hi, input_limb tm hb hi] at uv
    exact uv
  · rw [tv, VG.Proof.X448.valN_add]

theorem pointwiseSub_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Pointwise.sub o a b)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a - VG.Proof.X448.AArch64.F s.mem base b := by
  let f := VG.Proof.X448.difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : ∀ i < 16, f i < 2 ^ 62 := VG.Proof.X448.difference_bound ab
  refine WP.mono (pointwiseFused_ok hs ho ho8 fb ?_)
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_sub ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subEval_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk⟩
    simp only [VG.Proof.X448.difference, ea, eb] at uv
    exact uv
  · rw [Nat.add_mod, tv, ← Nat.add_mod, VG.Proof.X448.difference_val bb, Nat.add_mul_mod_self_right]

theorem pointwiseSmall_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (ab : Bounded s.mem base a) :
    WP isa (.block (Pointwise.small o a)) s fun t => VG.Proof.X448.AArch64.Op base o s t ∧ Bounded t.mem base o ∧
      VG.Proof.X448.AArch64.F t.mem base o = Spec.X448.a24 * VG.Proof.X448.AArch64.F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * VG.Proof.X448.radix < 2 ^ 62 := by decide
    exact Nat.lt_of_le_of_lt h hr
  refine WP.mono (pointwiseFused_ok hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_a24 ?_⟩
  · intro i hi t ts tm
    refine WP.mono (smallEval_ok ts ha ha8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk⟩
    rw [input_limb tm ha hi] at uv
    exact uv
  · rw [tv, VG.Proof.X448.valN_scale]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Swap`. -/
section

/-!
# X448 on AArch64: constant-time conditional swaps

An XOR mask exchanges the limbs without a branch or an address depending on
the swap bit.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& VG.Proof.X448.AArch64.mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& VG.Proof.X448.AArch64.mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [VG.Proof.X448.AArch64.mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [VG.Proof.X448.AArch64.mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem swapStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {x y i : Nat}
    (hx : VG.Proof.X448.AArch64.Slot x) (hy : VG.Proof.X448.AArch64.Slot y) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) (hi : i < 16) {sw : Bool} (hc : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block
      [VG.Impl.X448.AArch64.ld .x4 (x + 8 * i), VG.Impl.X448.AArch64.ld .x5 (y + 8 * i), .logic .eor .x .x7 .x4 .x5,
        .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
        .logic .eor .x .x5 .x5 .x7, VG.Impl.X448.AArch64.st .x4 (x + 8 * i), VG.Impl.X448.AArch64.st .x5 (y + 8 * i)]) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.X448.AArch64.off base (x + 8 * i))
        (if sw then VG.Proof.X448.AArch64.word s.mem base (y + 8 * i) else VG.Proof.X448.AArch64.word s.mem base (x + 8 * i))).writeW
        (VG.Proof.X448.AArch64.off base (y + 8 * i)) (if sw then VG.Proof.X448.AArch64.word s.mem base (x + 8 * i) else VG.Proof.X448.AArch64.word s.mem base (y + 8 * i)) ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7] s t := by
  have lx := hs.read (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have ly := hs.read (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  have wx := hs.write (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have wy := hs.write (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  have xe : (x + 8 * i) % 8 = 0 ∧ x + 8 * i < 32768 := by
    change x + 128 ≤ 3584 at hx; omega
  have ye : (y + 8 * i) % 8 = 0 ∧ y + 8 * i < 32768 := by
    change y + 128 ≤ 3584 at hy; omega
  apply WP.of_runBlock
  simp only [VG.Impl.X448.AArch64.ld, VG.Impl.X448.AArch64.st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, xe, ye, and_self,
    hs.x3, hc, lx, ly, wx, wy, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  simp only [(VG.Proof.X448.AArch64.xor_sel sw _ _).1, (VG.Proof.X448.AArch64.xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : VG.Proof.X448.AArch64.Slot x) (hy : VG.Proof.X448.AArch64.Slot y)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) (hn : n < 16) (hj : j < 16) (vx vy : BitVec 64) :
    let m' := (m.writeW (VG.Proof.X448.AArch64.off base (x + 8 * n)) vx).writeW (VG.Proof.X448.AArch64.off base (y + 8 * n)) vy
    limbs m' base x j = (if j = n then vx.toNat else limbs m base x j) ∧
    limbs m' base y j = (if j = n then vy.toNat else limbs m base y j) := by
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  dsimp only
  constructor
  · simp only [limbs, VG.Proof.X448.AArch64.word]
    rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)]
    rw [show m.readW (VG.Proof.X448.AArch64.off base (x + 8 * j)) 64 = VG.Proof.X448.AArch64.word m base (x + 8 * j) from rfl]
    change (VG.Proof.X448.AArch64.word (m.writeW (VG.Proof.X448.AArch64.off base (x + 8 * n)) vx) base (x + 8 * j)).toNat = _
    rw [word_write m base (by omega) (by omega)]
    split <;> rfl
  · change (VG.Proof.X448.AArch64.word ((m.writeW (VG.Proof.X448.AArch64.off base (x + 8 * n)) vx).writeW (VG.Proof.X448.AArch64.off base (y + 8 * n)) vy)
      base (y + 8 * j)).toNat = _
    rw [word_write (m.writeW (VG.Proof.X448.AArch64.off base (x + 8 * n)) vx) base (by omega) (by omega)]
    by_cases h : j = n
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      apply congrArg BitVec.toNat
      exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap all sixteen limbs under the mask, preserving all other bytes. -/
theorem cswap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {x y : Nat} (hx : VG.Proof.X448.AArch64.Slot x) (hy : VG.Proof.X448.AArch64.Slot y)
    (hx8 : x % 8 = 0) (hy8 : y % 8 = 0)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) {sw : Bool} (hc : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (VG.Impl.X448.AArch64.cswap x y)) s fun t =>
      (∀ i < 16, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
      (∀ i < 16, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
      Outside2 base x 128 y 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
    (∀ i < n, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
    Outside2 base x (8 * n) y (8 * n) s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7] s t
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block
      [VG.Impl.X448.AArch64.ld .x4 (x + 8 * n), VG.Impl.X448.AArch64.ld .x5 (y + 8 * n), .logic .eor .x .x7 .x4 .x5,
        .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
        .logic .eor .x .x5 .x5 .x7, VG.Impl.X448.AArch64.st .x4 (x + 8 * n), VG.Impl.X448.AArch64.st .x5 (y + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .x6 (by decide)).trans hc
    refine WP.mono (VG.Proof.X448.AArch64.swapStep_ok (hs.of_keeps tk (by decide)) hx hy hx8 hy8 hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : limbs t.mem base x n = limbs s.mem base x n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have ey : limbs t.mem base y n = limbs s.mem base y n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have pair := fun (j : Nat) (hj : j < 16) => VG.Proof.X448.AArch64.pair_write (m := t.mem) (base := base) hx hy hxy hn hj
      (if sw then VG.Proof.X448.AArch64.word t.mem base (y + 8 * n) else VG.Proof.X448.AArch64.word t.mem base (x + 8 * n))
      (if sw then VG.Proof.X448.AArch64.word t.mem base (x + 8 * n) else VG.Proof.X448.AArch64.word t.mem base (y + 8 * n))
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact ty j (by omega)
    · refine (tm.mono (by omega) (by omega)).trans ?_
      intro p hp hq
      rw [um, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega : y + 8 * n + 8 ≤ 8192) p (by omega),
        VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega : x + 8 * n + 8 ≤ 8192) p (by omega)]
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Env`. -/
section

/-!
# X448 on AArch64: the working space as field-element slots

Field operations update one of twenty-two slots, preserving bounded limbs in
every slot. The frame excludes saved registers, the swap bit and the scalar's
decoded bits.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev Index := Fin 22
abbrev Env := VG.Proof.X448.AArch64.Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : VG.Proof.X448.AArch64.Index) : Spec.X448.Fe := VG.Proof.X448.AArch64.F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : VG.Proof.X448.AArch64.Index, Bounded m base (slot i.val)

def workRegs : List Reg := .x7 :: VG.Proof.X448.AArch64.clob

structure Keep (base : Addr) (s t : State) : Prop where
  regs : Keeps VG.Proof.X448.AArch64.workRegs s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem Keep.refl (base : Addr) (s : State) : VG.Proof.X448.AArch64.Keep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.AArch64.Keep base s t) (h' : VG.Proof.X448.AArch64.Keep base t u) :
    VG.Proof.X448.AArch64.Keep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Keep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem slot_bound (i : VG.Proof.X448.AArch64.Index) : VG.Proof.X448.AArch64.Slot (slot i.val) := by
  simp only [VG.Proof.X448.AArch64.Slot, slot, ACC]
  have := i.isLt
  omega

theorem slot_aligned (i : VG.Proof.X448.AArch64.Index) : slot i.val % 8 = 0 := by
  simp only [slot]; omega

theorem slot_sep {i j : VG.Proof.X448.AArch64.Index} (h : i ≠ j) : slot i.val + 128 ≤ slot j.val ∨ slot j.val + 128 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega

theorem Op.keep {base : Addr} {o : VG.Proof.X448.AArch64.Index} {s t : State} (h : VG.Proof.X448.AArch64.Op base (slot o.val) s t) : VG.Proof.X448.AArch64.Keep base s t := by
  refine ⟨h.keeps.mono (fun _ hr => List.mem_cons_of_mem _ hr), ?_⟩
  intro p hp hq
  apply h.mem p _ hq
  have := o.isLt
  simp only [slot]
  omega

theorem E_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.AArch64.Index} (h : FieldMem base (slot o.val) m m') :
    VG.Proof.X448.AArch64.E m' base = Function.update (VG.Proof.X448.AArch64.E m base) o (VG.Proof.X448.AArch64.F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, VG.Proof.X448.AArch64.E]
  · rw [Function.update_of_ne hi]
    simp only [VG.Proof.X448.AArch64.E, VG.Proof.X448.AArch64.F]
    rw [h.fe (VG.Proof.X448.AArch64.slot_sep hi) (VG.Proof.X448.AArch64.slot_bound i)]

theorem bounded_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.AArch64.Index} (h : FieldMem base (slot o.val) m m')
    (hm : VG.Proof.X448.AArch64.BoundedEnv m base) (ho : Bounded m' base (slot o.val)) : VG.Proof.X448.AArch64.BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (VG.Proof.X448.AArch64.slot_sep hi) (VG.Proof.X448.AArch64.slot_bound i) hj]
    exact hm i j hj

def opMul (o a b : VG.Proof.X448.AArch64.Index) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := Function.update e o (e a * e b)
def opAdd (o a b : VG.Proof.X448.AArch64.Index) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := Function.update e o (e a + e b)
def opSub (o a b : VG.Proof.X448.AArch64.Index) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := Function.update e o (e a - e b)
def opA24 (o a : VG.Proof.X448.AArch64.Index) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : VG.Proof.X448.AArch64.Index) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := Function.update e o (e a)
def opSwap (x y : VG.Proof.X448.AArch64.Index) (sw : Bool) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) (o a b : VG.Proof.X448.AArch64.Index) :
    WP isa (Impl.X448.AArch64.Tail.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opMul o a b (VG.Proof.X448.AArch64.E s.mem base) :=
  WP.mono (Wide.tailMul_ok hs (VG.Proof.X448.AArch64.slot_bound o) (VG.Proof.X448.AArch64.slot_aligned o) (VG.Proof.X448.AArch64.slot_bound a) (VG.Proof.X448.AArch64.slot_aligned a) (VG.Proof.X448.AArch64.slot_bound b) (VG.Proof.X448.AArch64.slot_aligned b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.bounded_update h.mem hb bo, by rw [VG.Proof.X448.AArch64.E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) (o a b : VG.Proof.X448.AArch64.Index) :
    WP isa (.block (Pointwise.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opAdd o a b (VG.Proof.X448.AArch64.E s.mem base) :=
  WP.mono (VG.Proof.X448.AArch64.pointwiseAdd_ok hs (VG.Proof.X448.AArch64.slot_bound o) (VG.Proof.X448.AArch64.slot_aligned o) (VG.Proof.X448.AArch64.slot_bound a) (VG.Proof.X448.AArch64.slot_aligned a) (VG.Proof.X448.AArch64.slot_bound b) (VG.Proof.X448.AArch64.slot_aligned b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.bounded_update h.mem hb bo, by rw [VG.Proof.X448.AArch64.E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) (o a b : VG.Proof.X448.AArch64.Index) :
    WP isa (.block (Pointwise.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opSub o a b (VG.Proof.X448.AArch64.E s.mem base) :=
  WP.mono (VG.Proof.X448.AArch64.pointwiseSub_ok hs (VG.Proof.X448.AArch64.slot_bound o) (VG.Proof.X448.AArch64.slot_aligned o) (VG.Proof.X448.AArch64.slot_bound a) (VG.Proof.X448.AArch64.slot_aligned a) (VG.Proof.X448.AArch64.slot_bound b) (VG.Proof.X448.AArch64.slot_aligned b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.bounded_update h.mem hb bo, by rw [VG.Proof.X448.AArch64.E_update h.mem, e]; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) (o a : VG.Proof.X448.AArch64.Index) :
    WP isa (.block (Pointwise.small (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opA24 o a (VG.Proof.X448.AArch64.E s.mem base) :=
  WP.mono (VG.Proof.X448.AArch64.pointwiseSmall_ok hs (VG.Proof.X448.AArch64.slot_bound o) (VG.Proof.X448.AArch64.slot_aligned o) (VG.Proof.X448.AArch64.slot_bound a) (VG.Proof.X448.AArch64.slot_aligned a) (hb a)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.bounded_update h.mem hb bo, by rw [VG.Proof.X448.AArch64.E_update h.mem, e]; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) (o a : VG.Proof.X448.AArch64.Index) :
    WP isa (.block (copy (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opCopy o a (VG.Proof.X448.AArch64.E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (VG.Proof.X448.AArch64.slot_sep h)
  refine WP.mono (copy_ok hs (Nat.le_trans (VG.Proof.X448.AArch64.slot_bound o) (by decide))
    (Nat.le_trans (VG.Proof.X448.AArch64.slot_bound a) (by decide)) (VG.Proof.X448.AArch64.slot_aligned o) (VG.Proof.X448.AArch64.slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : VG.Proof.X448.AArch64.Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, VG.Proof.X448.AArch64.bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [VG.Proof.X448.AArch64.E_update op.mem, show VG.Proof.X448.AArch64.F t.mem base (slot o.val) = VG.Proof.X448.AArch64.F s.mem base (slot a.val) from
      congrArg VG.Proof.X448.toFe (VG.Proof.X448.valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base)
    (x y : VG.Proof.X448.AArch64.Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (VG.Impl.X448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opSwap x y sw (VG.Proof.X448.AArch64.E s.mem base) := by
  refine WP.mono (VG.Proof.X448.AArch64.cswap_ok hs (VG.Proof.X448.AArch64.slot_bound x) (VG.Proof.X448.AArch64.slot_bound y) (VG.Proof.X448.AArch64.slot_aligned x) (VG.Proof.X448.AArch64.slot_aligned y) (VG.Proof.X448.AArch64.slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : VG.Proof.X448.AArch64.Index, i ≠ x → i ≠ y → ∀ j < 16,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := VG.Proof.X448.AArch64.slot_sep hix
    have ey := VG.Proof.X448.AArch64.slot_sep hiy
    have hi := VG.Proof.X448.AArch64.slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 128 ≤ 3584 at hi; omega)]
  have fx : VG.Proof.X448.AArch64.E t.mem base x = if sw then VG.Proof.X448.AArch64.E s.mem base y else VG.Proof.X448.AArch64.E s.mem base x := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.valN_congr <;> exact tx
  have fy : VG.Proof.X448.AArch64.E t.mem base y = if sw then VG.Proof.X448.AArch64.E s.mem base x else VG.Proof.X448.AArch64.E s.mem base y := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, ?_, tk.1 _ (by decide), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega
  · intro i j hj
    by_cases hix : i = x
    · subst i; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · rw [other i hix hiy j hj]; exact hb i j hj
  · funext i
    by_cases hiy : i = y
    · subst i; rw [VG.Proof.X448.AArch64.opSwap, Function.update_self]; exact fy
    · rw [VG.Proof.X448.AArch64.opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.valN_congr (other i hix hiy))

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Ops`. -/
section

/-!
# X448 on AArch64: sequences of field operations

Slot-indexed operations interpret the implementation's field-operation lists
as environment updates.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

inductive FieldOp
  | mul (o a b : VG.Proof.X448.AArch64.Index)
  | add (o a b : VG.Proof.X448.AArch64.Index)
  | sub (o a b : VG.Proof.X448.AArch64.Index)
  | mulSmall (o a : VG.Proof.X448.AArch64.Index)
  | copy (o a : VG.Proof.X448.AArch64.Index)
  deriving DecidableEq

def FieldOp.impl : VG.Proof.X448.AArch64.FieldOp → Impl.X448.AArch64.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .add o a b => .add (slot o.val) (slot a.val) (slot b.val)
  | .sub o a b => .sub (slot o.val) (slot a.val) (slot b.val)
  | .mulSmall o a => .mulSmall (slot o.val) (slot a.val)
  | .copy o a => .copy (slot o.val) (slot a.val)

def FieldOp.apply : VG.Proof.X448.AArch64.FieldOp → VG.Proof.X448.AArch64.Env → VG.Proof.X448.AArch64.Env
  | .mul o a b => VG.Proof.X448.AArch64.opMul o a b
  | .add o a b => VG.Proof.X448.AArch64.opAdd o a b
  | .sub o a b => VG.Proof.X448.AArch64.opSub o a b
  | .mulSmall o a => VG.Proof.X448.AArch64.opA24 o a
  | .copy o a => VG.Proof.X448.AArch64.opCopy o a

def applyOps : List VG.Proof.X448.AArch64.FieldOp → VG.Proof.X448.AArch64.Env → VG.Proof.X448.AArch64.Env
  | [], e => e
  | op :: rest, e => VG.Proof.X448.AArch64.applyOps rest (op.apply e)

theorem fieldOp_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) (op : VG.Proof.X448.AArch64.FieldOp) :
    WP isa op.impl.code s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = op.apply (VG.Proof.X448.AArch64.E s.mem base) := by
  cases op with
  | mul o a b => exact VG.Proof.X448.AArch64.mulE hs hb o a b
  | add o a b => exact VG.Proof.X448.AArch64.addE hs hb o a b
  | sub o a b => exact VG.Proof.X448.AArch64.subE hs hb o a b
  | mulSmall o a => exact VG.Proof.X448.AArch64.a24E hs hb o a
  | copy o a => exact VG.Proof.X448.AArch64.copyE hs hb o a

theorem ops_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) (xs : List VG.Proof.X448.AArch64.FieldOp) :
    WP isa (ops (xs.map FieldOp.impl)) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.applyOps xs (VG.Proof.X448.AArch64.E s.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hb, rfl⟩
  | cons op rest ih =>
    change WP isa (.seq op.impl.code (ops (rest.map FieldOp.impl))) s _
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.AArch64.fieldOp_ok hs hb op) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, ?_⟩
    rw [ue, te]
    rfl

/-- The arithmetic part of one Montgomery-ladder step. -/
def stepFields : List VG.Proof.X448.AArch64.FieldOp :=
  [.add 5 1 2, .mul 9 5 5, .sub 6 1 2, .mul 10 6 6, .sub 11 9 10,
    .add 7 3 4, .sub 8 3 4, .mul 12 8 5, .mul 13 7 6,
    .add 3 12 13, .mul 3 3 3, .sub 4 12 13, .mul 4 4 4, .mul 4 0 4,
    .mul 1 9 10, .mulSmall 2 11, .add 2 9 2, .mul 2 11 2]

theorem stepFields_impl : stepFields.map FieldOp.impl = stepOps := by decide +kernel

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.BitStep`. -/
section

/-!
# X448 on AArch64: reading a scalar bit

The public counter selects a byte of the scalar-bit array. Only the XOR mask,
never control flow, depends on that bit and the previous swap bit.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- The start of `step`. -/
def stepPre : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x11 .x3 .x19, .ldrb .x4 .x11 BITS,
    ld .x5 SWAP, .logic .eor .x .x5 .x5 .x4, st .x4 SWAP,
    .movz .x .x6 0 0, .sub .x .x6 .x6 .x5]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 64) - (BitVec.ofNat 64 a ^^^ (BitVec.ofNat 8 b).setWidth 64) =
      VG.Proof.X448.AArch64.mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block VG.Proof.X448.AArch64.stepPre) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 t ∧ s'.gpr .x6 = VG.Proof.X448.AArch64.mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.x19, .x4, .x5, .x6, .x11] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 kt) := by
  have hb' : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 t := by
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have enc : BITS % 1 = 0 ∧ BITS < 4096 * 1 := by decide
  have encSwap : SWAP % 8 = 0 ∧ SWAP < 4096 * 8 := by decide
  have hswap' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.stepPre, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Size.bytes, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, hb', hs.x3, addr, enc, encSwap, and_self,
    off, Offset.add_add, Nat.add_comm t BITS, State.load, State.store,
    hin, hr, hw, read1_eq, read8_eq, write8_eq, hbit, hswap',
    Option.bind_some, Option.map_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  have ext : (BitVec.setWidth 32 (BitVec.ofNat 8 kt)).setWidth 64 =
      (BitVec.ofNat 8 kt).setWidth 64 := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  simp only [ext]
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [e0]; exact VG.Proof.X448.AArch64.mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial,
    by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Counters`. -/
section

/-!
# X448 on AArch64: loop counters

Setting and decrementing public counters preserves memory and every other
register.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64

/-- Set the ladder or squaring counter. -/
theorem setCounter_ok (s : State) (k : Nat) (hk : k < 2 ^ 16) :
    WP isa (.block [.movz .x .x19 (BitVec.ofNat 16 k) 0]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- Decrement the counter; the result is zero precisely on the last iteration. -/
theorem decCounter_ok {s : State} {k : Nat} (hk : k < 2 ^ 16)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ (s'.gpr .x19 == 0) = decide (k = 0) := by
  have hb' : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 k := by
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zero : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true,
    State.read, BitVec.setWidth_eq, hb', RegUpd.gpr_write_self, zero,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl, trivial⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Iter`. -/
section

/-!
# X448 on AArch64: the Montgomery ladder

Each iteration consumes one scalar bit and updates the five field slots
according to `ladderStep`.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def stepEnv (sw : Bool) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env :=
  VG.Proof.X448.AArch64.applyOps VG.Proof.X448.AArch64.stepFields (VG.Proof.X448.AArch64.opSwap 2 4 sw (VG.Proof.X448.AArch64.opSwap 1 3 sw e))

theorem cswap_fst (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem stepEnv_eval (e : VG.Proof.X448.AArch64.Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    VG.Proof.X448.AArch64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 0 = u ∧
    VG.Proof.X448.AArch64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    VG.Proof.X448.AArch64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    VG.Proof.X448.AArch64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    VG.Proof.X448.AArch64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [VG.Proof.X448.ladderStep_eq]
  simp only [↓reduceIte, VG.Proof.X448.AArch64.stepEnv, VG.Proof.X448.AArch64.applyOps, VG.Proof.X448.AArch64.stepFields, FieldOp.apply,
    VG.Proof.X448.AArch64.opMul, VG.Proof.X448.AArch64.opAdd, VG.Proof.X448.AArch64.opSub, VG.Proof.X448.AArch64.opA24, VG.Proof.X448.AArch64.opSwap, Function.update_apply,
    VG.Proof.X448.AArch64.cswap_fst, VG.Proof.X448.AArch64.cswap_snd, h0, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem swaps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base)
    {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (VG.Impl.X448.AArch64.cswap X2 X3 ++ VG.Impl.X448.AArch64.cswap Z2 Z3)) s fun t =>
      VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opSwap 2 4 sw (VG.Proof.X448.AArch64.opSwap 1 3 sw (VG.Proof.X448.AArch64.E s.mem base)) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.cswapE hs hb 1 3 (by decide) hm) fun t ⟨tk, tb, tc, te⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.cswapE (tk.scr hs) tb 2 4 (by decide) (tc.trans hm)) fun u ⟨uk, ub, _, ue⟩ =>
    ⟨tk.trans uk, ub, by rw [ue, te]⟩

theorem counter_zero {s : State} {n : Nat} (hn : n < 2 ^ 32)
    (hc : s.gpr .x19 = BitVec.ofNat 64 n) : (s.gpr .x19 == 0) = decide (n = 0) := by
  rw [hc]
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rfl
  · rw [decide_eq_false (by omega)]
    apply beq_false_of_ne
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact absurd this (by simp; omega)

/-- The complete loop invariant, including its memory frame. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : VG.Proof.X448.AArch64.BoundedEnv s.mem base
  regs : Keeps (.x19 :: VG.Proof.X448.AArch64.workRegs) s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 n
  mem : Outside2 base 16 2864 ACC 512 s₀.mem s.mem
  x1 : VG.Proof.X448.AArch64.E s.mem base 0 = u
  x2 : VG.Proof.X448.AArch64.E s.mem base 1 = (VG.Proof.X448.ladderAfter k u n).x2
  z2 : VG.Proof.X448.AArch64.E s.mem base 2 = (VG.Proof.X448.ladderAfter k u n).z2
  x3 : VG.Proof.X448.AArch64.E s.mem base 3 = (VG.Proof.X448.ladderAfter k u n).x3
  z3 : VG.Proof.X448.AArch64.E s.mem base 4 = (VG.Proof.X448.ladderAfter k u n).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (VG.Proof.X448.ladderAfter k u n).swap

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.AArch64.LInv base k u s₀ s (n + 1)) :
    WP isa VG.Impl.X448.AArch64.step s fun t => VG.Proof.X448.AArch64.LInv base k u s₀ t n ∧ (t.gpr .x19 == 0) = decide (n = 0) := by
  have hs := hi.scr
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (VG.Proof.X448.bit k n) := by
    rw [hi.mem _ (by rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
    exact hbits n hn
  rw [VG.Impl.X448.AArch64.step, WP.seq_iff,
    show stepHead = VG.Proof.X448.AArch64.stepPre ++ (VG.Impl.X448.AArch64.cswap X2 X3 ++ VG.Impl.X448.AArch64.cswap Z2 Z3) by
      simp only [stepHead, VG.Proof.X448.AArch64.stepPre, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.stepPre_ok hs hn hi.x19 (by have := VG.Proof.X448.bit_le k n; omega)
    (by have := VG.Proof.X448.ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.x3, (g₁ _ (by decide)).trans hs.mask, wr₁ ▸ hs.wr, hs.nowrap⟩
  have out₁ : Outside base SWAP 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by decide)
  have l₁ : ∀ i : VG.Proof.X448.AArch64.Index, ∀ j < 16, limbs s₁.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i j hj
    exact out₁.limbs (Or.inr (by simp only [slot, SWAP]; omega))
      (Nat.le_trans (VG.Proof.X448.AArch64.slot_bound i) (by decide)) hj
  have e₁ : VG.Proof.X448.AArch64.E s₁.mem base = VG.Proof.X448.AArch64.E s.mem base := by
    funext i; exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.valN_congr (l₁ i))
  have bb₁ : VG.Proof.X448.AArch64.BoundedEnv s₁.mem base := by
    intro i j hj; rw [l₁ i j hj]; exact hi.bounded i j hj
  refine WP.mono (VG.Proof.X448.AArch64.swaps_ok hs₁ bb₁ c₁) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_
  rw [← VG.Proof.X448.AArch64.stepFields_impl]
  refine WP.mono (VG.Proof.X448.AArch64.ops_ok (k₂.scr hs₁) bb₂ VG.Proof.X448.AArch64.stepFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_
  have core := k₂.trans k₃
  have b₃ : s₃.gpr .x19 = BitVec.ofNat 64 n := (core.regs.1 _ (by decide)).trans b₁
  have vals := VG.Proof.X448.AArch64.stepEnv_eval (VG.Proof.X448.AArch64.E s.mem base) (VG.Proof.X448.ladderAfter k u (n + 1)) k u n
    hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  have e₄ : VG.Proof.X448.AArch64.E s₃.mem base = VG.Proof.X448.AArch64.stepEnv (decide ((VG.Proof.X448.ladderAfter k u (n + 1)).swap ^^^ VG.Proof.X448.bit k n = 1))
      (VG.Proof.X448.AArch64.E s.mem base) := by rw [e₃, e₂, e₁]; rfl
  rw [← VG.Proof.X448.ladderAfter_step k u hn, ← e₄] at vals
  refine ⟨⟨core.scr hs₁, bb₃, ?_, b₃, ?_, vals.1, vals.2.1, vals.2.2.1,
    vals.2.2.2.1, vals.2.2.2.2, ?_⟩, VG.Proof.X448.AArch64.counter_zero (by omega) b₃⟩
  · refine hi.regs.trans ⟨?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    intro r hr
    have hwork : r ∉ VG.Proof.X448.AArch64.workRegs := fun h => hr (List.mem_cons_of_mem _ h)
    have hpre : r ∉ [Reg.x19, .x4, .x5, .x6, .x11] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide)⟩
    rw [core.regs.1 r hwork, g₁ r hpre]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p (by omega) hq, out₁ p (by simp only [SWAP]; omega)]
  · rw [core.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP, ACC]; omega) (by decide),
      m₁, VG.Proof.X448.ladderAfter_step k u hn]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.BitWrite`. -/
section

/-!
# X448 on AArch64: expanding scalar bytes

Each byte is expanded into eight bytes holding its bits, through public
offsets in the working space.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, VG.Proof.X448.AArch64.sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    off base d = off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => ofs base x) h
    simp only [VG.Proof.X448.AArch64.ofs_off' base hd, VG.Proof.X448.AArch64.ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) : (m.writeW (off base d) v) x = m x := by
  rw [VG.Proof.X448.AArch64.writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (VG.Proof.X448.AArch64.ofs_off' base hd) hx

theorem write1_eq (m : Mem) (p : Addr) (v : BitVec 8) : m.write p 1 v = m.writeW p v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    (((b.setWidth 64 >>> j) &&& (1 : BitVec 64)).setWidth 32).setWidth 8 =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

def bitJ (j : Nat) : List Instr :=
  [.lsr .x .x5 .x4 j, .logic .and .x .x5 .x5 .x8, .strb .x5 .x11 (BITS + j)]

theorem bitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .x11 = off base (8 * i)) (hc : s.gpr .x8 = 1)
    {b : BitVec 8} (ha : s.gpr .x4 = b.setWidth 64) {j : Nat} (hj : j < 8) :
    WP isa (.block (VG.Proof.X448.AArch64.bitJ j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ Keeps [.x5] s t := by
  have w := hs.write (d := BITS + (8 * i + j)) (n := 1) (by simp only [BITS]; omega)
  have enc : (BITS + j) % 1 = 0 ∧ BITS + j < 4096 := by simp only [BITS]; omega
  have shift : j < 64 := by omega
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.bitJ, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, shift, addr, enc, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, hp, hc, ha, off, Offset.add_add,
    show 8 * i + (BITS + j) = BITS + (8 * i + j) by omega,
    State.store, w, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, VG.Proof.X448.AArch64.write1_eq, VG.Proof.X448.AArch64.bit_byte b j hj, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Expanding eight bits preserves each byte already written. -/
theorem byteBits_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .x11 = off base (8 * i)) (hc : s.gpr .x8 = 1)
    {b : BitVec 8} (ha : s.gpr .x4 = b.setWidth 64) :
    WP isa (.block ((List.range 8).flatMap VG.Proof.X448.AArch64.bitJ)) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (VG.Proof.X448.AArch64.bitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.AArch64.bitJ_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans hp) ((tk.1 _ (by decide)).trans hc)
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, VG.Proof.X448.AArch64.writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [VG.Proof.X448.AArch64.off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact VG.Proof.X448.AArch64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.BitBody`. -/
section

/-!
# X448 on AArch64: one scalar byte

The public byte counter selects a scalar byte, expands it, and advances the
loop.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def bitHead : List Instr :=
  [.add .x .x11 .x1 .x19, .ldrb .x4 .x11 0,
    .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11]

def bitTail : List Instr := [.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 56]

def bitRegs : List Reg := [.x4, .x5, .x19, .x11, .x8]

theorem bitHead_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    {i : Nat} (hb : s.gpr .x19 = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block VG.Proof.X448.AArch64.bitHead) s fun t =>
      t.gpr .x4 = (s.mem (off k i)).setWidth 64 ∧ t.gpr .x11 = off base (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x11] s t := by
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.bitHead, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, hk, hb, hs.x3,
    addr, Nat.reduceMod, Nat.reduceMul, and_self, BitVec.add_zero,
    State.load, hkr, read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, off]
    have := (s.mem (k + BitVec.ofNat 64 i)).isLt
    omega
  · apply congrArg (base + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    change (i % 2 ^ 64 * 8) % 2 ^ 64 = (8 * i) % 2 ^ 64
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 56) (hb : s.gpr .x19 = BitVec.ofNat 64 i) :
    WP isa (.block VG.Proof.X448.AArch64.bitTail) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 56) ∧
      t.mem = s.mem ∧ Keeps [.x19, .x11] s t := by
  have check : ∀ n < 56,
      ((BitVec.ofNat 64 n + BitVec.ofNat 64 1 - BitVec.ofNat 64 56) == 0) = decide (n + 1 = 56) :=
    by decide +kernel
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.bitTail, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write, hb, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(BitVec.ofNat_add _ _).symm, check i hi, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    {i : Nat} (hi : i < 56) (hb : s.gpr .x19 = BitVec.ofNat 64 i) (hc : s.gpr .x8 = 1)
    (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 56) ∧
      t.gpr .x8 = 1 ∧ Keeps VG.Proof.X448.AArch64.bitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (VG.Proof.X448.AArch64.bitHead ++ (List.range 8).flatMap VG.Proof.X448.AArch64.bitJ ++ VG.Proof.X448.AArch64.bitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.bitHead_ok hs hk hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  have tc : t.gpr .x8 = 1 := (tk.1 _ (by decide)).trans hc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.byteBits_ok (hs.of_keeps tk (by decide)) (by omega) tp tc ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .x19 = BitVec.ofNat 64 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (VG.Proof.X448.AArch64.bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tc), ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Clamp`. -/
section

/-!
# X448 on AArch64: clamping the scalar bits

Clear bits zero and one, and set bit 447, as RFC 7748 requires.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def clamp : List Instr :=
  [.movz .x .x4 0 0, .strb .x4 .x3 BITS, .strb .x4 .x3 (BITS + 1),
    .movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base BITS) (0 : BitVec 8)).writeW (off base (BITS + 1))
    (0 : BitVec 8)).writeW (off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.strb .x4 .x3 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) ((s.gpr .x4).setWidth 8) ∧ Keeps [] s t := by
  have w := hs.write (d := d) (n := 1) (by omega)
  have enc : d % 1 = 0 ∧ d < 4096 := ⟨by omega, hd⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self,
    hs.x3, State.store, w, State.read, ite_true, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun _ _ => rfl, rfl, rfl⟩
  rw [VG.Proof.X448.AArch64.write1_eq]
  apply congrArg (s.mem.writeW (off base d))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Size.bits]
  omega

theorem putByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 16) :
    WP isa (.block [.movz .x .x4 v 0, .strb .x4 .x3 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (v.setWidth 8) ∧
      t.gpr .x4 = v.setWidth 64 ∧ Keeps [.x4] s t := by
  change WP isa (.block (([.movz .x .x4 v 0] : List Instr) ++ [.strb .x4 .x3 d])) s _
  rw [WP.block_append_iff]
  have set : WP isa (.block [.movz .x .x4 v 0]) s fun t =>
      t.gpr .x4 = v.setWidth 64 ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr
  refine WP.mono set fun t ⟨tv, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.storeByte_ok (hs.of_keeps tk (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  refine ⟨?_, (uk.1 _ (by decide)).trans tv, tk.trans (uk.mono (by simp))⟩
  rw [um, tm, tv]
  apply congrArg (s.mem.writeW (off base d))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt
  omega

theorem clamp_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block VG.Proof.X448.AArch64.clamp) s fun t => t.mem = VG.Proof.X448.AArch64.clampMem s.mem base ∧ Keeps [.x4] s t := by
  change WP isa (.block (([.movz .x .x4 0 0, .strb .x4 .x3 BITS] : List Instr) ++
    ([.strb .x4 .x3 (BITS + 1)] : List Instr) ++
    [.movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.putByte_ok hs (by decide : BITS < 4096) 0) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Bits`. -/
section

/-!
# X448 on AArch64: the scalar's decoded bits

The loop expands all 56 bytes before applying the RFC 7748 scalar clamp.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Proof.X448

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  x1 : s.gpr .x1 = k
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x8 = 1
  gpr : ∀ r, r ∉ VG.Proof.X448.AArch64.bitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 448 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 56, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 56 → VG.Proof.X448.AArch64.BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) (.nonzero .x .x11)) s fun s' => VG.Proof.X448.AArch64.BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .nonzero .x .x11)
    (Q := fun s' => VG.Proof.X448.AArch64.BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ VG.Proof.X448.AArch64.BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.X448.AArch64.bitsBody_ok hb.scr hb.x1 hi hb.x19 hb.one (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.X448.AArch64.BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.x3, (g' _ (by decide)).trans hb.scr.mask, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.x1, b', one', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
  rcases Nat.lt_or_ge (i + 1) 56 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 56), Bool.not_false],
      56 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 55 := by omega
    exact .inl ⟨rfl, inv⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- `bits`: byte `t` of `BITS` is bit `t` of the decoded scalar, for `t < 448`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ VG.Proof.X448.AArch64.bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (VG.Proof.X448.bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => VG.Proof.X448.AArch64.BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, hs.wr, hs.nowrap⟩, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
      Outside.refl _ _ _ _, fun t ht => absurd ht (by omega)⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.x3
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.mask
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hk
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; rfl
    · rw [RegUpd.gpr_write_self]; rfl
    · have h19 : r ≠ .x19 := fun h => hr (by subst r; decide)
      have h8 : r ≠ .x8 := fun h => hr (by subst r; decide)
      simp only [RegUpd.gpr_write, h19, h8, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (VG.Proof.X448.AArch64.clamp_ok h₂.scr) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine ⟨fun r hr => ?_, k₃.2.1.trans h₂.rd, k₃.2.2.trans h₂.wr, fun x hx => ?_, fun t ht => ?_⟩
  · rw [k₃.1 r (by intro he; simp only [List.mem_singleton] at he; subst r; exact hr (by decide))]
    exact h₂.gpr r hr
  · rw [m₃, VG.Proof.X448.AArch64.clampMem]
    have o : ∀ d, BITS ≤ d → d < BITS + 448 → ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [VG.Proof.X448.AArch64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 447) (by omega) (by omega)),
      VG.Proof.X448.AArch64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 1) (by omega) (by omega)),
      VG.Proof.X448.AArch64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o BITS (by omega) (by omega))]
    exact h₂.mem x hx
  · rw [m₃, VG.Proof.X448.AArch64.clampMem, scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [VG.Proof.X448.AArch64.writeW8_apply, VG.Proof.X448.AArch64.off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 2 by omega, ite_false]
      rw [h₂.bits t (by omega), VG.Proof.X448.AArch64.getD_bytesAt _ _ (by omega)]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.DecodeStore`. -/
section

/-!
# X448 on AArch64: storing decoded limb pairs

Each seven-byte chunk is split into two limbs and stored into both copies of
the input coordinate.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def storePair (i : Nat) : List Instr :=
  [.logic .and .x .x7 .x4 .x12, VG.Impl.X448.AArch64.st .x7 (X1 + 16 * i), VG.Impl.X448.AArch64.st .x7 (X3 + 16 * i),
    .lsr .x .x4 .x4 28, VG.Impl.X448.AArch64.st .x4 (X1 + 16 * i + 8), VG.Impl.X448.AArch64.st .x4 (X3 + 16 * i + 8)]

def pairMem (m : Mem) (base : Addr) (i v : Nat) : Mem :=
  (((m.writeW (VG.Proof.X448.AArch64.off base (X1 + 16 * i)) (BitVec.ofNat 64 (v % VG.Proof.X448.radix))).writeW
    (VG.Proof.X448.AArch64.off base (X3 + 16 * i)) (BitVec.ofNat 64 (v % VG.Proof.X448.radix))).writeW
    (VG.Proof.X448.AArch64.off base (X1 + 16 * i + 8)) (BitVec.ofNat 64 (v / VG.Proof.X448.radix))).writeW
    (VG.Proof.X448.AArch64.off base (X3 + 16 * i + 8)) (BitVec.ofNat 64 (v / VG.Proof.X448.radix))

theorem storePair_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {i : Nat} (hi : i < 8) :
    WP isa (.block (VG.Proof.X448.AArch64.storePair i)) s fun t =>
      t.mem = VG.Proof.X448.AArch64.pairMem s.mem base i (s.gpr .x4).toNat ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x7] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (VG.Proof.X448.AArch64.off base d) 8 := fun _ hd => hs.write hd
  have low : s.gpr .x4 &&& (0x0fffffff : BitVec 64) = BitVec.ofNat 64 ((s.gpr .x4).toNat % VG.Proof.X448.radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [and28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : VG.Proof.X448.radix < 2 ^ 64))]
  have high : s.gpr .x4 >>> 28 = BitVec.ofNat 64 ((s.gpr .x4).toNat / VG.Proof.X448.radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [shr28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .x4).isLt)]
  have enc : ∀ d, d % 8 = 0 → d + 8 ≤ 8192 → d % 8 = 0 ∧ d < 32768 :=
    fun d hd hb => ⟨hd, by omega⟩
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.storePair, VG.Impl.X448.AArch64.st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, hs.x3, hs.mask,
    enc (X1 + 16 * i) (by simp only [X1, slot]; omega) (by simp only [X1, slot]; omega),
    enc (X3 + 16 * i) (by simp only [X3, slot]; omega) (by simp only [X3, slot]; omega),
    enc (X1 + 16 * i + 8) (by simp only [X1, slot]; omega) (by simp only [X1, slot]; omega),
    enc (X3 + 16 * i + 8) (by simp only [X3, slot]; omega) (by simp only [X3, slot]; omega),
    w (X1 + 16 * i) (by simp only [X1, slot]; omega),
    w (X3 + 16 * i) (by simp only [X3, slot]; omega),
    w (X1 + 16 * i + 8) (by simp only [X1, slot]; omega),
    w (X3 + 16 * i + 8) (by simp only [X3, slot]; omega),
    Nat.reduceLT, and_self, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [low, high]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem pairMem_limbs (m : Mem) (base : Addr) {i j v : Nat} (hi : i < 8) (hj : j < 16)
    (hv : v < VG.Proof.X448.radix * VG.Proof.X448.radix) :
    limbs (VG.Proof.X448.AArch64.pairMem m base i v) base X1 j =
      (if j = 2 * i + 1 then v / VG.Proof.X448.radix else if j = 2 * i then v % VG.Proof.X448.radix else limbs m base X1 j) ∧
    limbs (VG.Proof.X448.AArch64.pairMem m base i v) base X3 j =
      (if j = 2 * i + 1 then v / VG.Proof.X448.radix else if j = 2 * i then v % VG.Proof.X448.radix else limbs m base X3 j) := by
  have lo : (BitVec.ofNat 64 (v % VG.Proof.X448.radix)).toNat = v % VG.Proof.X448.radix := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : VG.Proof.X448.radix < 2 ^ 64))]
  have high : (BitVec.ofNat 64 (v / VG.Proof.X448.radix)).toNat = v / VG.Proof.X448.radix := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans ((Nat.div_lt_iff_lt_mul (by decide)).mpr hv)
      (by decide : VG.Proof.X448.radix < 2 ^ 64))]
  let m₁ := (m.writeW (VG.Proof.X448.AArch64.off base (X1 + 8 * (2 * i))) (BitVec.ofNat 64 (v % VG.Proof.X448.radix))).writeW
    (VG.Proof.X448.AArch64.off base (X3 + 8 * (2 * i))) (BitVec.ofNat 64 (v % VG.Proof.X448.radix))
  have p₁ := VG.Proof.X448.AArch64.pair_write (m := m) (base := base) (x := X1) (y := X3) (n := 2 * i)
    (by decide) (by decide) (by decide) (by omega) hj (BitVec.ofNat 64 (v % VG.Proof.X448.radix)) (BitVec.ofNat 64 (v % VG.Proof.X448.radix))
  have p₂ := VG.Proof.X448.AArch64.pair_write (m := m₁) (base := base) (x := X1) (y := X3) (n := 2 * i + 1)
    (by decide) (by decide) (by decide) (by omega) hj (BitVec.ofNat 64 (v / VG.Proof.X448.radix)) (BitVec.ofNat 64 (v / VG.Proof.X448.radix))
  have index0 : 8 * (2 * i) = 16 * i := by omega
  have index1 : 8 * (2 * i + 1) = 16 * i + 8 := by omega
  simp only [m₁, index0, index1, ← Nat.add_assoc, lo, high] at p₁ p₂
  rw [p₁.1, p₁.2] at p₂
  exact p₂

theorem pairMem_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 8) (v : Nat) :
    Outside2 base X1 (16 * (i + 1)) X3 (16 * (i + 1)) m (VG.Proof.X448.AArch64.pairMem m base i v) := by
  intro p hx hy
  simp only [VG.Proof.X448.AArch64.pairMem]
  have x0 : X1 + 16 * i + 8 ≤ 8192 := by simp only [X1, slot]; omega
  have x1 : X1 + 16 * i + 8 + 8 ≤ 8192 := by simp only [X1, slot]; omega
  have y0 : X3 + 16 * i + 8 ≤ 8192 := by simp only [X3, slot]; omega
  have y1 : X3 + 16 * i + 8 + 8 ≤ 8192 := by simp only [X3, slot]; omega
  rw [VG.Proof.X448.AArch64.writeW_outside _ _ _ y1 p (by omega), VG.Proof.X448.AArch64.writeW_outside _ _ _ x1 p (by omega),
    VG.Proof.X448.AArch64.writeW_outside _ _ _ y0 p (by omega), VG.Proof.X448.AArch64.writeW_outside _ _ _ x0 p (by omega)]

theorem decodePair_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {i : Nat} (hi : i < 8)
    (hp : s.gpr .x2 = p) (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (VG.Proof.X448.AArch64.off p (7 * i + j)) 1) :
    WP isa (.block (decodePair i)) s fun t =>
      t.mem = VG.Proof.X448.AArch64.pairMem s.mem base i (VG.Proof.X448.chunk s.mem p i) ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7, .x8] s t := by
  change WP isa (.block (readSeven i ++ VG.Proof.X448.AArch64.storePair i)) s _
  rw [WP.block_append_iff]
  refine WP.mono (readSeven_ok hp hi hr) fun t ⟨tv, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.storePair_ok (hs.of_keeps tk (by decide)) hi) fun u ⟨um, uk⟩ => ?_
  refine ⟨?_, tk.trans (uk.mono ?_)⟩
  · rw [um, tv, tm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.DecodeAll`. -/
section

/-!
# X448 on AArch64: all input-coordinate bytes

Eight limb pairs fill the two coordinate slots. The input lies outside the
writable working space.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Equal input bytes give equal seven-byte chunks. -/
theorem chunk_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 8)
    (h : ∀ j < 56, m' (VG.Proof.X448.AArch64.off p j) = m (VG.Proof.X448.AArch64.off p j)) : VG.Proof.X448.chunk m' p i = VG.Proof.X448.chunk m p i := by
  apply congrArg VG.Proof.X25519.leNum
  simp only [Spec.X448.bytesAt]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  rw [Offset.add_add]
  exact h _ (by omega)

theorem decodeAll_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.AArch64.off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.AArch64.ofs base (VG.Proof.X448.AArch64.off p j)) :
    WP isa (.block ((List.range 8).flatMap decodePair)) s fun t =>
      (∀ j < 16, limbs t.mem base X1 j = VG.Proof.X448.decoded s.mem p j) ∧
      (∀ j < 16, limbs t.mem base X3 j = VG.Proof.X448.decoded s.mem p j) ∧
      Outside2 base X1 128 X3 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7, .x8] s t := by
  let inv := fun n (t : State) =>
    (∀ j < 2 * n, limbs t.mem base X1 j = VG.Proof.X448.decoded s.mem p j) ∧
    (∀ j < 2 * n, limbs t.mem base X3 j = VG.Proof.X448.decoded s.mem p j) ∧
    Outside2 base X1 (16 * n) X3 (16 * n) s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7, .x8] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (decodePair n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp := (tk.1 .x2 (by decide)).trans hp
    have tr : ∀ j < 7, InRegions (t.rd ++ t.wr) (VG.Proof.X448.AArch64.off p (7 * n + j)) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr _ (by omega)
    have byte : ∀ j < 56, t.mem (VG.Proof.X448.AArch64.off p j) = s.mem (VG.Proof.X448.AArch64.off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [X1, slot]; omega)) (Or.inr (by simp only [X3, slot]; omega))
    have chunkEq := VG.Proof.X448.AArch64.chunk_congr hn byte
    refine WP.mono (VG.Proof.X448.AArch64.decodePair_ok (hs.of_keeps tk (by decide)) hn tp tr) fun u ⟨um, uk⟩ => ?_
    rw [chunkEq] at um
    have pair := fun (j : Nat) (hj : j < 16) => VG.Proof.X448.AArch64.pairMem_limbs t.mem base hn hj (chunk_lt s.mem p n)
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h1 : j = 2 * n + 1
      · rw [ite_eq_left h1, h1, decoded_odd]
      · rw [ite_eq_right h1]
        by_cases h0 : j = 2 * n
        · rw [ite_eq_left h0, h0, decoded_even]
        · rw [ite_eq_right h0]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h1 : j = 2 * n + 1
      · rw [ite_eq_left h1, h1, decoded_odd]
      · rw [ite_eq_right h1]
        by_cases h0 : j = 2 * n
        · rw [ite_eq_left h0, h0, decoded_even]
        · rw [ite_eq_right h0]; exact ty j (by omega)
    · rw [um]
      exact (tm.mono (by omega) (by omega)).trans (VG.Proof.X448.AArch64.pairMem_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.FinalSwap`. -/
section

/-!
# X448 on AArch64: the swap after the ladder

The final swap bit selects the coordinates to be converted back to affine
form.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem mask_of : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 16) - BitVec.ofNat 64 a =
    VG.Proof.X448.AArch64.mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block [ld .x5 SWAP, .movz .x .x6 0 0, .sub .x .x6 .x6 .x5]) s
      fun t => t.gpr .x6 = VG.Proof.X448.AArch64.mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ Keeps [.x5, .x6] s t := by
  have hr := hs.read (d := SWAP) (n := 8) (by decide)
  have enc : SWAP % 8 = 0 ∧ SWAP < 32768 := by decide
  have hw' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw := hw
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, enc, and_self,
    hs.x3, hr, read8_eq, hw', Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.X448.AArch64.mask_of sw hsw, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block lastSwap) s fun t => VG.Proof.X448.AArch64.Keep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧
      VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.opSwap 2 4 (decide (sw = 1)) (VG.Proof.X448.AArch64.opSwap 1 3 (decide (sw = 1)) (VG.Proof.X448.AArch64.E s.mem base)) := by
  rw [lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : VG.Proof.X448.AArch64.Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  refine WP.mono (VG.Proof.X448.AArch64.swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Initial`. -/
section

/-!
# X448 on AArch64: initial field values

Every slot starts with bounded limbs. The decoded coordinates are retained,
and the ladder starts with X2 = 1, Z2 = 0, Z3 = 1, and a zero swap bit.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def zeroSlots : List Instr :=
  [.movz .x .x4 0 0] ++ (List.range 32).map (fun i => st .x4 (X2 + 8 * i)) ++
    (List.range 288).map (fun i => st .x4 (Z3 + 8 * i))

theorem zeroSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block VG.Proof.X448.AArch64.zeroSlots) s fun t =>
      (∀ i : VG.Proof.X448.AArch64.Index, ∀ j < 16, limbs t.mem base (slot i.val) j =
        if i = 0 ∨ i = 3 then limbs s.mem base (slot i.val) j else 0) ∧
      t.gpr .x4 = 0 ∧ Outside base X2 2688 s.mem t.mem ∧ Keeps [.x4] s t := by
  rw [VG.Proof.X448.AArch64.zeroSlots, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroX4_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok ts (by decide : X2 + 8 * 32 ≤ 8192) (by decide) tz) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (fill_ok (ts.of_keeps uk (by decide)) (by decide : Z3 + 8 * 288 ≤ 8192) (by decide)
    ((uk.1 _ (by decide)).trans tz)) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tz), ?_, ?_⟩
  · intro i j hj
    have il := i.isLt
    by_cases h0 : i = 0
    · subst i
      rw [ite_eq_left (Or.inl rfl)]
      change (word v.mem base (64 + 8 * j)).toNat = _
      rw [vm.word (by change 64 + 8 * j + 8 ≤ 576 ∨ _; omega) (by omega),
        um.word (by change 64 + 8 * j + 8 ≤ 192 ∨ _; omega) (by omega), tm]
      rfl
    · by_cases h3 : i = 3
      · subst i
        rw [ite_eq_left (Or.inr rfl)]
        change (word v.mem base (448 + 8 * j)).toNat = _
        rw [vm.word (by change 448 + 8 * j + 8 ≤ 576 ∨ _; omega) (by omega),
          um.word (by change _ ∨ 192 + 8 * 32 ≤ 448 + 8 * j; omega) (by omega), tm]
        rfl
      · rw [ite_eq_right (not_or_intro h0 h3)]
        have i0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
        have i3 : i.val ≠ 3 := fun h => h3 (Fin.ext h)
        rcases Nat.lt_or_ge i.val 3 with h | h
        · have index : slot i.val + 8 * j = X2 + 8 * (16 * (i.val - 1) + j) := by
            simp only [slot, X2]; omega
          change (word v.mem base (slot i.val + 8 * j)).toNat = 0
          rw [vm.word (Or.inl (by simp only [slot, Z3]; omega)) (by simp only [slot]; omega), index]
          exact uf _ (by omega)
        · have index : slot i.val + 8 * j = Z3 + 8 * (16 * (i.val - 4) + j) := by
            simp only [slot, Z3]; omega
          change (word v.mem base (slot i.val + 8 * j)).toNat = 0
          rw [index]
          exact vf _ (by omega)
  · rw [← tm]
    exact (um.mono (by omega) (by omega)).trans (vm.mono (by decide) (by decide))
  · exact tk.trans ((uk.trans vk).mono (fun _ hr => False.elim (List.not_mem_nil hr)))

def initialMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base SWAP) (0 : BitVec 64)).writeW (off base X2) (1 : BitVec 64)).writeW
    (off base Z3) (1 : BitVec 64)

theorem initialStores_ok {s : State} {base : Addr} (hs : Scr s base) (hz : s.gpr .x4 = 0) :
    WP isa (.block [st .x4 SWAP, .movz .x .x4 1 0, st .x4 X2, st .x4 Z3]) s
      fun t => t.mem = VG.Proof.X448.AArch64.initialMem s.mem base ∧ Keeps [.x4] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 := fun _ hd => hs.write hd
  have es : SWAP % 8 = 0 ∧ SWAP < 32768 := by decide
  have ex : X2 % 8 = 0 ∧ X2 < 32768 := by decide
  have ez : Z3 % 8 = 0 ∧ Z3 < 32768 := by decide
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.store, RegUpd.gpr_write, RegUpd.wr_write, BitVec.setWidth_eq,
    es, ex, ez, and_self, hs.x3, hz, w SWAP (by decide), w X2 (by decide), w Z3 (by decide),
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem initialMem_limb (m : Mem) (base : Addr) (i : VG.Proof.X448.AArch64.Index) {j : Nat} (hj : j < 16) :
    limbs (VG.Proof.X448.AArch64.initialMem m base) base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else limbs m base (slot i.val) j := by
  have il := i.isLt
  have hd : slot i.val + 8 * j + 8 ≤ 8192 := by simp only [slot]; omega
  have hm : (slot i.val + 8 * j) % 8 = 0 := by simp only [slot]; omega
  have es : slot i.val + 8 * j ≠ SWAP := by simp only [slot, SWAP]; omega
  have ex : slot i.val + 8 * j = X2 ↔ i = 1 ∧ j = 0 := by
    simp only [slot, X2]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have ez : slot i.val + 8 * j = Z3 ↔ i = 4 ∧ j = 0 := by
    simp only [slot, Z3]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [limbs, VG.Proof.X448.AArch64.initialMem]
  rw [word_write_aligned _ base (by decide) hd (by decide) hm,
    word_write_aligned _ base (by decide) hd (by decide) hm,
    word_write_aligned _ base (by decide) hd (by decide) hm, ite_eq_right es]
  simp only [ex, ez]
  by_cases h1 : i = 1 <;> by_cases h4 : i = 4 <;> by_cases h0 : j = 0 <;>
    simp only [h1, h4, h0, and_true, and_false, or_true, or_false,
      true_or, ite_true, ite_false] <;> rfl

theorem initialMem_outside (m : Mem) (base : Addr) : Outside base 16 2864 m (VG.Proof.X448.AArch64.initialMem m base) := by
  intro p hp
  simp only [VG.Proof.X448.AArch64.initialMem]
  rw [writeW_outside _ _ _ (by decide : Z3 + 8 ≤ 8192) p (by simp only [Z3, slot]; omega),
    writeW_outside _ _ _ (by decide : X2 + 8 ≤ 8192) p (by simp only [X2, slot]; omega),
    writeW_outside _ _ _ (by decide : SWAP + 8 ≤ 8192) p (by simp only [SWAP]; omega)]

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base)
    (h0 : Bounded s.mem base X1) (h3 : Bounded s.mem base X3) :
    WP isa (.block initSlots) s fun t =>
      VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base 0 = VG.Proof.X448.AArch64.E s.mem base 0 ∧ VG.Proof.X448.AArch64.E t.mem base 1 = 1 ∧
      VG.Proof.X448.AArch64.E t.mem base 2 = 0 ∧ VG.Proof.X448.AArch64.E t.mem base 3 = VG.Proof.X448.AArch64.E s.mem base 3 ∧ VG.Proof.X448.AArch64.E t.mem base 4 = 1 ∧
      word t.mem base SWAP = 0 ∧ Outside base 16 2864 s.mem t.mem ∧ Keeps [.x4] s t := by
  change WP isa (.block (VG.Proof.X448.AArch64.zeroSlots ++ [st .x4 SWAP, .movz .x .x4 1 0,
    st .x4 X2, st .x4 Z3])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.zeroSlots_ok hs) fun t ⟨tf, tz, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.initialStores_ok (hs.of_keeps tk (by decide)) tz) fun u ⟨um, uk⟩ => ?_
  have lf : ∀ i : VG.Proof.X448.AArch64.Index, ∀ j < 16, limbs u.mem base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else
        if i = 0 ∨ i = 3 then limbs s.mem base (slot i.val) j else 0 := by
    intro i j hj
    rw [um, VG.Proof.X448.AArch64.initialMem_limb _ _ i hj, tf i j hj]
  have zval : VG.Proof.X448.valN (fun _ => 0) 16 = 0 := by decide
  have oval : VG.Proof.X448.valN (fun j => if j = 0 then 1 else 0) 16 = 1 := by decide +kernel
  have l0 : ∀ j < 16, limbs u.mem base X1 j = limbs s.mem base X1 j := by
    intro j hj
    have h := lf (⟨0, by decide⟩ : VG.Proof.X448.AArch64.Index) j hj
    dsimp only [X1]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l1 : ∀ j < 16, limbs u.mem base X2 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨1, by decide⟩ : VG.Proof.X448.AArch64.Index) j hj
    dsimp only [X2]
    simpa (config := {decide := true}) only [true_or, true_and, ite_false] using h
  have l2 : ∀ j < 16, limbs u.mem base Z2 j = 0 := by
    intro j hj
    have h := lf (⟨2, by decide⟩ : VG.Proof.X448.AArch64.Index) j hj
    dsimp only [Z2]
    simpa (config := {decide := true}) only [false_or, false_and, ite_false] using h
  have l3 : ∀ j < 16, limbs u.mem base X3 j = limbs s.mem base X3 j := by
    intro j hj
    have h := lf (⟨3, by decide⟩ : VG.Proof.X448.AArch64.Index) j hj
    dsimp only [X3]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l4 : ∀ j < 16, limbs u.mem base Z3 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨4, by decide⟩ : VG.Proof.X448.AArch64.Index) j hj
    dsimp only [Z3]
    simpa (config := {decide := true}) only [or_true, true_and, ite_false] using h
  refine ⟨?_, congrArg VG.Proof.X448.toFe (VG.Proof.X448.valN_congr l0), ?_, ?_, congrArg VG.Proof.X448.toFe (VG.Proof.X448.valN_congr l3), ?_, ?_, ?_, tk.trans uk⟩
  · intro i j hj
    rw [lf i j hj]
    split
    · decide
    · split
      · rename_i h
        rcases h with rfl | rfl
        · exact h0 j hj
        · exact h3 j hj
      · decide
  · change VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe u.mem base X2) = 1
    rw [show VG.Proof.X448.AArch64.fe u.mem base X2 = VG.Proof.X448.valN (fun j => if j = 0 then 1 else 0) 16 from VG.Proof.X448.valN_congr l1, oval]
    exact VG.Proof.X448.toFe_one
  · change VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe u.mem base Z2) = 0
    rw [show VG.Proof.X448.AArch64.fe u.mem base Z2 = VG.Proof.X448.valN (fun _ => 0) 16 from VG.Proof.X448.valN_congr l2, zval]
    exact VG.Proof.X448.toFe_zero
  · change VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe u.mem base Z3) = 1
    rw [show VG.Proof.X448.AArch64.fe u.mem base Z3 = VG.Proof.X448.valN (fun j => if j = 0 then 1 else 0) 16 from VG.Proof.X448.valN_congr l4, oval]
    exact VG.Proof.X448.toFe_one
  · rw [um, VG.Proof.X448.AArch64.initialMem,
      word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [um]
    exact (tm.mono (by decide) (by decide)).trans (VG.Proof.X448.AArch64.initialMem_outside _ _)

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Setup`. -/
section

/-!
# X448 on AArch64: reading the arguments

Setup saves the two callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  word m base 0 = g .x19 ∧ word m base 8 = g .x20

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.X448.AArch64.Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h16 : 16 ≤ o) : VG.Proof.X448.AArch64.Saved base g m' :=
  ⟨(ho.word (Or.inl (by omega)) (by decide)).trans h.1,
    (ho.word (Or.inl h16) (by decide)).trans h.2⟩

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.X448.AArch64.Saved base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : 16 ≤ x) (hy : 16 ≤ y) :
    VG.Proof.X448.AArch64.Saved base g m' :=
  ⟨(ho.word (Or.inl (by omega)) (Or.inl (by omega)) (by decide)).trans h.1,
    (ho.word (Or.inl hx) (Or.inl hy) (by decide)).trans h.2⟩

def setupHead : List Instr :=
  [st .x19 0, st .x20 8, .addImm .x .x20 .x0 0,
    .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1]

theorem setupHead_ok {s : State} {base : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block VG.Proof.X448.AArch64.setupHead) s fun t =>
      Scr t base ∧ t.gpr .x20 = s.gpr .x0 ∧ t.gpr .x2 = s.gpr .x2 ∧
      VG.Proof.X448.AArch64.Saved base s.gpr t.mem ∧ Outside base 0 16 s.mem t.mem ∧ Keeps [.x20, .x12] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun _ hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.setupHead, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.store, hc, w 0 (by decide), w 8 (by decide),
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq,
    BitVec.shiftLeft_zero, RegUpd.gpr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨hc, ?_, hw, hn⟩, BitVec.add_zero _, trivial, ?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [RegUpd.gpr_write_self]; decide
  · change VG.Proof.X448.AArch64.Saved base s.gpr ((s.mem.writeW (off base 0) (s.gpr .x19)).writeW (off base 8) (s.gpr .x20))
    constructor
    · rw [word_write_aligned _ base (by decide) (by decide) (by decide) (by decide),
        ite_eq_right (by decide)]
      exact Mem.readW_writeW_self64 _ _ _
    · exact Mem.readW_writeW_self64 _ _ _
  · exact ((writeW_outside s.mem base _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ base _ (d := 8) (by decide)).mono (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

def setupRegs : List Reg := [.x4, .x5, .x7, .x8, .x20, .x12]

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ t.gpr .x20 = s.gpr .x0 ∧ Keeps VG.Proof.X448.AArch64.setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ VG.Proof.X448.AArch64.Saved base s.gpr t.mem ∧
      VG.Proof.X448.AArch64.E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      VG.Proof.X448.AArch64.E t.mem base 1 = 1 ∧ VG.Proof.X448.AArch64.E t.mem base 2 = 0 ∧
      VG.Proof.X448.AArch64.E t.mem base 3 = VG.Proof.X448.AArch64.E t.mem base 0 ∧ VG.Proof.X448.AArch64.E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  change WP isa (.block (VG.Proof.X448.AArch64.setupHead ++ ((List.range 8).flatMap decodePair ++ initSlots))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.setupHead_ok hc hw hn) fun t ⟨ts, tp, tr, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.decodeAll_ok ts (tr.trans hp)
    (by intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_bound _ _ _
  have ub3 : Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_bound _ _ _
  have uv0 : VG.Proof.X448.AArch64.E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t.mem p 56)) := by
    apply congrArg toFe
    exact (VG.Proof.X448.valN_congr ux).trans (VG.Proof.X448.decoded_val t.mem p 8)
  have uv3 : VG.Proof.X448.AArch64.E u.mem base 3 = VG.Proof.X448.AArch64.E u.mem base 0 := congrArg toFe ((VG.Proof.X448.valN_congr uy).trans (VG.Proof.X448.valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (VG.Proof.X448.AArch64.initSlots_ok (ts.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tp),
    (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm.mono (by decide) (by decide)).trans ?_,
    (tv.outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show Outside base 0 8192 t.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega) (by simp only [X3, slot]; omega)).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Pack`. -/
section

/-!
# X448 on AArch64: writing seven-byte chunks

Each pair of bounded limbs is combined in a register and written with seven
byte stores.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev packed (m : Mem) (base : Addr) (i : Nat) : Nat :=
  limbs m base X2 (2 * i) + VG.Proof.X448.radix * limbs m base X2 (2 * i + 1)

theorem packed_bound {m : Mem} {base : Addr} (hb : Bounded m base X2) {i : Nat} (hi : i < 8) :
    VG.Proof.X448.AArch64.packed m base i < 2 ^ 56 := by
  have h0 := hb (2 * i) (by omega)
  have h1 := hb (2 * i + 1) (by omega)
  simp only [VG.Proof.X448.AArch64.packed, VG.Proof.X448.radix] at h0 h1 ⊢
  omega

def packHead (i : Nat) : List Instr :=
  [ld .x4 (X2 + 16 * i + 8), .lsl .x .x4 .x4 28,
    ld .x5 (X2 + 16 * i), .add .x .x4 .x4 .x5]

theorem packHead_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 8) :
    WP isa (.block (VG.Proof.X448.AArch64.packHead i)) s fun t =>
      (t.gpr .x4).toNat = VG.Proof.X448.AArch64.packed s.mem base i ∧ t.mem = s.mem ∧ Keeps [.x4, .x6, .x5] s t := by
  have lo := hs.read (d := X2 + 16 * i) (n := 8) (by simp only [X2, slot]; omega)
  have lh := hs.read (d := X2 + 16 * i + 8) (n := 8) (by simp only [X2, slot]; omega)
  have b := VG.Proof.X448.AArch64.packed_bound hb hi
  have he0 : X2 + 16 * i = X2 + 8 * (2 * i) := by omega
  have he1 : X2 + 16 * i + 8 = X2 + 8 * (2 * i + 1) := by omega
  have le : (X2 + 16 * i) % 8 = 0 ∧ X2 + 16 * i < 32768 := by simp only [X2, slot]; omega
  have he : (X2 + 16 * i + 8) % 8 = 0 ∧ X2 + 16 * i + 8 < 32768 := by simp only [X2, slot]; omega
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.packHead, ld, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Size.bytes, Nat.reduceLT, BitVec.setWidth_eq, addr, le, he, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs.x3, State.load, lo, lh, read8_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · rw [he1, he0, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (limbs s.mem base X2 (2 * i + 1) * VG.Proof.X448.radix % 2 ^ 64 +
      limbs s.mem base X2 (2 * i)) % 2 ^ 64 = _
    change limbs s.mem base X2 (2 * i) + VG.Proof.X448.radix * limbs s.mem base X2 (2 * i + 1) < _ at b
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact Nat.add_comm _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]

def packByte (i j : Nat) : List Instr :=
  [.strb .x4 .x1 (7 * i + j), .lsr .x .x4 .x4 8]

theorem packByte_ok {s : State} {p : Addr} {i j : Nat} (hp : s.gpr .x1 = p) (hi : i < 8) (hj : j < 7)
    (hw : InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block (VG.Proof.X448.AArch64.packByte i j)) s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x4).toNat / 256 ∧
      t.mem = s.mem.writeW (off p (7 * i + j)) (BitVec.ofNat 8 (s.gpr .x4).toNat) ∧ Keeps [.x4] s t := by
  have enc : (7 * i + j) % 1 = 0 ∧ 7 * i + j < 4096 := by omega
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.packByte, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, addr, enc, and_self,
    State.store, hp, hw, ite_true, Option.bind_some, VG.Proof.X448.AArch64.write1_eq,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · apply congrArg (s.mem.writeW (off p (7 * i + j)))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem writeSeven_ok {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .x1 = p)
    (hw : ∀ j < 7, InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block ((List.range 7).flatMap (VG.Proof.X448.AArch64.packByte i))) s fun t =>
      (∀ j < 7, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .x4).toNat / 256 ^ j)) ∧
      Outside p (7 * i) 7 s.mem t.mem ∧ Keeps [.x4] s t := by
  let inv := fun n (t : State) =>
    (t.gpr .x4).toNat = (s.gpr .x4).toNat / 256 ^ n ∧
    (∀ j < n, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .x4).toNat / 256 ^ j)) ∧
    Outside p (7 * i) n s.mem t.mem ∧ Keeps [.x4] s t
  have st : ∀ n t, n < 7 → inv n t → WP isa (.block (VG.Proof.X448.AArch64.packByte i n)) t (inv (n + 1)) := by
    intro n t hn ⟨ta, tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.AArch64.packByte_ok ((tk.1 _ (by decide)).trans hp) hi hn
      (by rw [tk.2.2]; exact hw n hn)) fun u ⟨ua, um, uk⟩ => ?_
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · rw [ua, ta, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    · intro j hj
      rw [um, VG.Proof.X448.AArch64.writeW8_apply]
      simp only [VG.Proof.X448.AArch64.off_eq_iff p (d := 7 * i + j) (e := 7 * i + n) (by omega) (by omega)]
      by_cases h : j = n
      · rw [ite_eq_left (by omega), h, ta]
      · rw [ite_eq_right (by omega)]; exact tf j (by omega)
    · intro q hq
      rw [um, VG.Proof.X448.AArch64.writeW8_outside _ _ _ (by omega) (by omega)]
      exact tm q (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv st 7 (by decide) s
    ⟨by rw [Nat.pow_zero, Nat.div_one], fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨_, tf, tm, tk⟩ => ⟨tf, tm, tk⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Output`. -/
section

/-!
# X448 on AArch64: the output buffer

Output stores cover exactly 56 bytes. The disjoint working space retains the
source limbs and saved registers until the function restores them.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem packPair_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 8) (hp : s.gpr .x1 = p)
    (hw : ∀ j < 7, InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block (packPair i)) s fun t =>
      VG.Proof.X448.chunk t.mem p i = VG.Proof.X448.AArch64.packed s.mem base i ∧ Outside p (7 * i) 7 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  change WP isa (.block (VG.Proof.X448.AArch64.packHead i ++ (List.range 7).flatMap (VG.Proof.X448.AArch64.packByte i))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.packHead_ok hs hb hi) fun t ⟨ta, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.writeSeven_ok hi ((tk.1 _ (by decide)).trans hp)
    (by intro j hj; rw [tk.2.2]; exact hw j hj)) fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨?_, tm ▸ um, (tk.mono ?_).trans (uk.mono ?_)⟩
  · have bytes : Spec.X448.bytesAt u.mem (off p (7 * i)) 7 =
        VG.Proof.X25519.leBytes 7 (VG.Proof.X448.AArch64.packed s.mem base i) := by
      apply List.map_congr_left
      intro j hj
      rw [Offset.add_add, uf j (List.mem_range.mp hj), ta]
    change VG.Proof.X25519.leNum _ = _
    rw [bytes]
    exact leNum_leBytes (VG.Proof.X448.AArch64.packed_bound hb hi)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 8 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega : 0 + n ≤ 56) (hfar _ (by omega))))

theorem output_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 8).flatMap packPair)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (VG.Proof.X448.AArch64.fe s.mem base X2) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.chunk t.mem p i = VG.Proof.X448.AArch64.packed s.mem base i) ∧ Outside p 0 (7 * n) s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t
  have st : ∀ n t, n < 8 → inv n t → WP isa (.block (packPair n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 16, limbs t.mem base X2 j = limbs s.mem base X2 j := by
      intro j hj
      exact congrArg BitVec.toNat (VG.Proof.X448.AArch64.output_word tm (by omega) (by simp only [X2, slot]; omega) hfar)
    have tb : Bounded t.mem base X2 := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (VG.Proof.X448.AArch64.packPair_ok (hs.of_keeps tk (by decide)) tb hn ((tk.1 _ (by decide)).trans hp)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega))) fun u ⟨uv, um, uk⟩ => ?_
    have pv : VG.Proof.X448.AArch64.packed t.mem base n = VG.Proof.X448.AArch64.packed s.mem base n := by
      rw [VG.Proof.X448.AArch64.packed, eq (2 * n) (by omega), eq (2 * n + 1) (by omega)]
    refine ⟨?_, (tm.mono (by decide) (by omega)).trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans pv
    · have bytes : Spec.X448.bytesAt u.mem (off p (7 * i)) 7 = Spec.X448.bytesAt t.mem (off p (7 * i)) 7 := by
        apply List.map_congr_left
        intro j hj
        have hj := List.mem_range.mp hj
        rw [Offset.add_add]
        exact um _ (Or.inl (by rw [VG.Proof.X448.AArch64.ofs_off' p (by omega)]; omega))
      change VG.Proof.X25519.leNum _ = _
      rw [bytes]; exact tf i (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv st 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨VG.Proof.X448.packed_bytes hb tf, tm, tk⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Select`. -/
section

/-!
# X448 on AArch64: selecting the canonical representative

An XOR mask selects each limb from the original value or the carried temporary
value.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def selectStep (i : Nat) : List Instr :=
  [VG.Impl.X448.AArch64.ld .x4 (X2 + 8 * i), VG.Impl.X448.AArch64.ld .x5 (TMP + 8 * i), .logic .eor .x .x5 .x5 .x4,
    .logic .and .x .x5 .x5 .x7, .logic .eor .x .x4 .x4 .x5, VG.Impl.X448.AArch64.st .x4 (X2 + 8 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {i : Nat} (hi : i < 16)
    {sw : Bool} (hc : s.gpr .x7 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (VG.Proof.X448.AArch64.selectStep i)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (X2 + 8 * i))
        (if sw then VG.Proof.X448.AArch64.word s.mem base (TMP + 8 * i) else VG.Proof.X448.AArch64.word s.mem base (X2 + 8 * i)) ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  have lx := hs.read (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega)
  have ly := hs.read (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have wx := hs.write (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega)
  have xe : (X2 + 8 * i) % 8 = 0 ∧ X2 + 8 * i < 32768 := by simp only [X2, slot]; omega
  have ye : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.selectStep, VG.Impl.X448.AArch64.ld, VG.Impl.X448.AArch64.st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, xe, ye, and_self,
    hs.x3, hc, lx, ly, wx, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  rw [BitVec.xor_comm (VG.Proof.X448.AArch64.word s.mem base (TMP + 8 * i)), (VG.Proof.X448.AArch64.xor_sel sw _ _).1]
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem select_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {sw : Bool} (hc : s.gpr .x7 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block ((List.range 16).flatMap VG.Proof.X448.AArch64.selectStep)) s fun t =>
      (∀ i < 16, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
      VG.Proof.X448.AArch64.Outside base X2 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
    VG.Proof.X448.AArch64.Outside base X2 (8 * n) s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t
  have st : ∀ n t, n < 16 → inv n t → WP isa (.block (VG.Proof.X448.AArch64.selectStep n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.AArch64.selectStep_ok (hs.of_keeps tk (by decide)) hn ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.AArch64.Outside base (X2 + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [X2, slot]; omega)
    refine ⟨?_, (tm.mono (by omega) (by omega)).trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.AArch64.word u.mem base (X2 + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [X2, slot]; omega) (by simp only [X2, slot]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h,
        tm.word (Or.inr (by simp only [X2, slot, TMP]; omega)) (by simp only [TMP]; omega),
        tm.word (Or.inr (by omega)) (by simp only [X2, slot]; omega)]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 16) inv st 16 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Freeze`. -/
section

/-!
# X448 on AArch64: canonical reduction

The final carry selects the unique representative below the prime, using only
a mask on secret data.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem freezeMask_ok {s : State} {c : Nat} (hc : (s.gpr .x6).toNat = c) (hb : c < 2) :
    WP isa (.block [.movz .x .x7 0 0, .sub .x .x7 .x7 .x6]) s fun t =>
      t.gpr .x7 = VG.Proof.X448.AArch64.mask (decide (c = 1)) ∧ t.mem = s.mem ∧ Keeps [.x7] s t := by
  have he : s.gpr .x6 = BitVec.ofNat 64 c := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 16) - BitVec.ofNat 64 a =
      VG.Proof.X448.AArch64.mask (decide (a = 1)) := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, BitVec.setWidth_eq,
    RegUpd.gpr_write, he, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨hm c hb, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block freeze) s fun t =>
      Bounded t.mem base X2 ∧ VG.Proof.X448.AArch64.fe t.mem base X2 = VG.Proof.X448.AArch64.fe s.mem base X2 % Spec.X448.P ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.workRegs s t := by
  change WP isa (.block ((copy TMP X2 ++ [0, 8].flatMap (fun i =>
    [ld .x4 (TMP + 8 * i), .addImm .x .x4 .x4 1,
      st .x4 (TMP + 8 * i)])) ++ (pass TMP TMP ++
    (([.movz .x .x7 0 0, .sub .x .x7 .x7 .x6] : List Instr) ++
      (List.range 16).flatMap VG.Proof.X448.AArch64.selectStep)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (freezePrep_ok hs hb) fun t ⟨tf, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok (hs.of_keeps tk (by decide)) (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
    tf (VG.Proof.X448.freezeCoeff_bound hb)) fun u ⟨uf, uc, um, uk⟩ => ?_
  have cb : VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff (limbs s.mem base X2)) 16 < 2 := by
    rw [VG.Proof.X448.freeze_carry hb]; split <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.freezeMask_ok uc cb) fun v ⟨vc, vm, vk⟩ => ?_
  have vs := ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.select_ok vs vc) fun w ⟨wf, wm, wk⟩ => ?_
  have outside : Outside base TMP 128 s.mem v.mem := by rw [vm]; exact tm.trans um
  have lf : ∀ i < 16, limbs w.mem base X2 i =
      if VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff (limbs s.mem base X2)) 16 = 1 then
        VG.Proof.X448.digit (VG.Proof.X448.freezeCoeff (limbs s.mem base X2)) i else limbs s.mem base X2 i := by
    intro i hi
    rw [wf i hi, outside.limbs (d := X2) (by decide) (by decide) hi, vm, uf i hi]
    simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, (FieldMem.work outside (by decide) (by decide)).trans (FieldMem.output wm),
    (tk.mono ?_).trans ((uk.mono ?_).trans ((vk.mono ?_).trans (wk.mono ?_)))⟩
  · intro i hi; rw [lf i hi]; split
    · exact VG.Proof.X448.digit_lt _ _
    · exact hb i hi
  · change VG.Proof.X448.valN (limbs w.mem base X2) 16 = _
    rw [VG.Proof.X448.valN_congr lf]
    by_cases h : VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff (limbs s.mem base X2)) 16 = 1
    · simp only [h, ite_true]
      exact (ite_eq_left h).symm.trans (VG.Proof.X448.freeze_value hb)
    · simp only [h, ite_false]
      exact (ite_eq_right h).symm.trans (VG.Proof.X448.freeze_value hb)
  · intro r hr; exact List.mem_cons_of_mem _ hr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Finish`. -/
section

/-!
# X448 on AArch64: the result and restored registers

The final multiplication, canonical reduction and encoding produce the affine
coordinate. The two callee-saved registers are then restored from the disjoint
working space.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem Outside.frame {base : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 n m m') :
    Frame [⟨base, n⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  change 0 + n ≤ (x - base).toNat
  omega))

theorem FieldMem.whole {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m')
    (ho : o + 128 ≤ 8192) : Outside base 0 8192 m m' := fun p hp =>
  h p (by omega) (by simp only [ACC]; omega)

theorem Outside2.whole {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : Outside2 base x nx y ny m m') (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) :
    Outside base 0 8192 m m' := fun p hp => h p (by omega) (by omega)

theorem Saved.field {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.X448.AArch64.Saved base g m)
    {o : Nat} (hm : FieldMem base o m m') (ho : 16 ≤ o) : VG.Proof.X448.AArch64.Saved base g m' :=
  ⟨(hm.word (Or.inl (by omega)) (by decide)).trans h.1,
    (hm.word (Or.inl ho) (by decide)).trans h.2⟩

theorem restore_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : VG.Proof.X448.AArch64.Saved base g s.mem) :
    WP isa (.block [ld .x19 0, ld .x20 8]) s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ t.mem = s.mem ∧ Keeps [.x19, .x20] s t := by
  have hr := hs.read (d := 0) (n := 8) (by decide)
  have hr' := hs.read (d := 8) (n := 8) (by decide)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.load, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq,
    hs.x3, hr, hr', RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, read8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨hsv.1, hsv.2, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem moveOutput_ok (s : State) :
    WP isa (.block [.addImm .x .x1 .x20 0]) s fun t =>
      t.gpr .x1 = s.gpr .x20 ∧ t.mem = s.mem ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

def finishRegs : List Reg := .x19 :: .x20 :: VG.Proof.X448.AArch64.workRegs

theorem finish_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) {g : Reg → BitVec 64} (sv : VG.Proof.X448.AArch64.Saved base g s.mem) :
    WP isa finish s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ Keeps VG.Proof.X448.AArch64.finishRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (VG.Proof.X448.AArch64.E s.mem base 1 * VG.Proof.X448.AArch64.E s.mem base 21) := by
  refine WP.seq (WP.mono (Wide.tailMul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.1 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.output_ok vs vb ((vk.1 _ (by decide)).trans ((uk.1.1 _ (by decide)).trans hp))
    (by intro j hj; rw [vk.2.2, uk.1.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : VG.Proof.X448.AArch64.Saved base g w.mem :=
    ⟨(VG.Proof.X448.AArch64.output_word wm (by decide) (by decide) hfar).trans svv.1,
      (VG.Proof.X448.AArch64.output_word wm (by decide) (by decide) hfar).trans svv.2⟩
  refine WP.mono (VG.Proof.X448.AArch64.restore_ok ws svw) fun t ⟨tb, tr, tm, tk⟩ => ?_
  refine ⟨tb, tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans (tk.mono ?_))), ?_, ?_⟩
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · rw [tm]
    exact (((uk.2.whole (by decide)).trans (vm.whole (by decide))).frame.mono (by simp)).trans
      (wm.frame.mono (by simp))
  · rw [tm, wv, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Square`. -/
section

/-!
# X448 on AArch64: runs of squarings

The inversion reuses field multiplication in a loop with its own counter. The
field slots and memory frame compose exactly as they do for straight-line
operation lists.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.x19 :: VG.Proof.X448.AArch64.workRegs) s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem IKeep.refl (base : Addr) (s : State) : VG.Proof.X448.AArch64.IKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem IKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.AArch64.IKeep base s t) (h' : VG.Proof.X448.AArch64.IKeep base t u) :
    VG.Proof.X448.AArch64.IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.IKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Keep.ikeep {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Keep base s t) : VG.Proof.X448.AArch64.IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : VG.Proof.X448.AArch64.IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : VG.Proof.X448.AArch64.Env → VG.Proof.X448.AArch64.Env) : Prop :=
  ∀ s, Scr s base → VG.Proof.X448.AArch64.BoundedEnv s.mem base → WP isa code s fun t =>
    VG.Proof.X448.AArch64.IKeep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = f (VG.Proof.X448.AArch64.E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : VG.Proof.X448.AArch64.Env → VG.Proof.X448.AArch64.Env}
    (h₁ : VG.Proof.X448.AArch64.ISpec base c₁ f) (h₂ : VG.Proof.X448.AArch64.ISpec base c₂ g) :
    VG.Proof.X448.AArch64.ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

theorem opsI (base : Addr) (xs : List VG.Proof.X448.AArch64.FieldOp) :
    VG.Proof.X448.AArch64.ISpec base (ops (xs.map FieldOp.impl)) (VG.Proof.X448.AArch64.applyOps xs) := fun _ hs hb =>
  WP.mono (VG.Proof.X448.AArch64.ops_ok hs hb xs) fun _ ⟨tk, tb, te⟩ => ⟨tk.ikeep, tb, te⟩

def opSqn (o : VG.Proof.X448.AArch64.Index) (n : Nat) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := Function.update e o (Proof.X448.sqn (e o) n)

theorem opMul_update (o : VG.Proof.X448.AArch64.Index) (e : VG.Proof.X448.AArch64.Env) (v : Spec.X448.Fe) :
    VG.Proof.X448.AArch64.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.X448.AArch64.opMul, Function.update_self, Function.update_idem]

theorem sqnI (base : Addr) (o : VG.Proof.X448.AArch64.Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    VG.Proof.X448.AArch64.ISpec base (Impl.X448.AArch64.sqn (slot o.val) n) (VG.Proof.X448.AArch64.opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.AArch64.sqn, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.AArch64.setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : VG.Proof.X448.AArch64.IKeep base s t := VG.Proof.X448.AArch64.counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ VG.Proof.X448.AArch64.IKeep base s u ∧ VG.Proof.X448.AArch64.BoundedEnv u.mem base ∧
    u.gpr .x19 = BitVec.ofNat 64 m ∧
    VG.Proof.X448.AArch64.E u.mem base = Function.update (VG.Proof.X448.AArch64.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.AArch64.E s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.AArch64.mulE (ku.scr hs) bu o o o) fun v ⟨kv, bv, ev⟩ => ?_
    have cv : v.gpr .x19 = BitVec.ofNat 64 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (VG.Proof.X448.AArch64.decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : VG.Proof.X448.AArch64.IKeep base s w := ku.trans (kv.ikeep.trans (VG.Proof.X448.AArch64.counter_keep wg wm wr ww))
    have bw : VG.Proof.X448.AArch64.BoundedEnv w.mem base := wm ▸ bv
    have ew : VG.Proof.X448.AArch64.E w.mem base = Function.update (VG.Proof.X448.AArch64.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.AArch64.E s.mem base o) (n - m)) := by
      rw [wm, ev, eu, VG.Proof.X448.AArch64.opMul_update, ← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, State.read, BitVec.setWidth_eq, bne, wz]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Inv`. -/
section

/-!
# X448 on AArch64: inversion

The addition chain updates slots 14–21 and leaves the ladder's coordinates
available for the final multiplication and encoding.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- The field slots after the inversion's addition chain. -/
def invEnv (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env :=
  let e := VG.Proof.X448.AArch64.applyOps [.copy 14 2] e
  let e := VG.Proof.X448.AArch64.opSqn 14 1 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 14 14 2, .copy 15 14] e
  let e := VG.Proof.X448.AArch64.opSqn 15 2 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 15 15 14, .copy 16 15] e
  let e := VG.Proof.X448.AArch64.opSqn 16 4 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 16 16 15, .copy 17 16] e
  let e := VG.Proof.X448.AArch64.opSqn 17 8 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 17 17 16, .copy 18 17] e
  let e := VG.Proof.X448.AArch64.opSqn 18 16 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 18 18 17, .copy 19 18] e
  let e := VG.Proof.X448.AArch64.opSqn 19 32 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 19 19 18, .copy 20 19] e
  let e := VG.Proof.X448.AArch64.opSqn 20 64 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.AArch64.opSqn 20 64 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.AArch64.opSqn 20 16 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 20 20 17] e
  let e := VG.Proof.X448.AArch64.opSqn 20 8 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 20 20 16] e
  let e := VG.Proof.X448.AArch64.opSqn 20 4 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 20 20 15] e
  let e := VG.Proof.X448.AArch64.opSqn 20 2 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 20 20 14, .copy 21 20] e
  let e := VG.Proof.X448.AArch64.opSqn 21 1 e
  let e := VG.Proof.X448.AArch64.applyOps [.mul 21 21 2] e
  let e := VG.Proof.X448.AArch64.opSqn 21 225 e
  let e := VG.Proof.X448.AArch64.opSqn 20 2 e
  VG.Proof.X448.AArch64.applyOps [.mul 20 20 2, .mul 21 21 20] e

theorem invert_spec (base : Addr) : VG.Proof.X448.AArch64.ISpec base Impl.X448.AArch64.invert VG.Proof.X448.AArch64.invEnv := by
  have h : VG.Proof.X448.AArch64.ISpec base _ _ :=
    (VG.Proof.X448.AArch64.opsI base [.copy 14 2]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 14 14 2, .copy 15 14]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 20 20 17]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 20 20 16]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 20 20 15]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 21 21 2]).seq <|
    (VG.Proof.X448.AArch64.sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.opsI base [.mul 20 20 2, .mul 21 21 20])
  exact h

theorem invEnv_eval (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.invEnv e 21 = Proof.X448.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.X448.AArch64.invEnv, VG.Proof.X448.AArch64.applyOps, FieldOp.apply, VG.Proof.X448.AArch64.opMul, VG.Proof.X448.AArch64.opCopy, VG.Proof.X448.AArch64.opSqn,
    Function.update_apply]
  rfl

theorem invEnv_x2 (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.invEnv e 1 = e 1 := by
  simp (config := {decide := true}) only [VG.Proof.X448.AArch64.invEnv, VG.Proof.X448.AArch64.applyOps, FieldOp.apply, VG.Proof.X448.AArch64.opMul, VG.Proof.X448.AArch64.opCopy, VG.Proof.X448.AArch64.opSqn,
    Function.update_apply, ite_true, ite_false]

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) :
    WP isa Impl.X448.AArch64.invert s fun t =>
      VG.Proof.X448.AArch64.IKeep base s t ∧ VG.Proof.X448.AArch64.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.E t.mem base = VG.Proof.X448.AArch64.invEnv (VG.Proof.X448.AArch64.E s.mem base) :=
  VG.Proof.X448.AArch64.invert_spec base s hs hb

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Ladder`. -/
section

/-!
# X448 on AArch64: all 448 ladder iterations

A decreasing public counter connects the loop to the specification's
descending fold over scalar bits.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → VG.Proof.X448.AArch64.LInv base k u s₀ s n →
      WP isa (.loop VG.Impl.X448.AArch64.step (.nonzero .x .x19)) s fun s' => VG.Proof.X448.AArch64.LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := VG.Impl.X448.AArch64.step) (c := .nonzero .x .x19)
    (Q := fun s' => VG.Proof.X448.AArch64.LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ VG.Proof.X448.AArch64.LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X448.AArch64.step_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, bne, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : ∀ s', s'.gpr .x19 = BitVec.ofNat 64 448 → (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.X448.AArch64.LInv base k u s₀ s' 448) :
    WP isa ladder s fun s' => VG.Proof.X448.AArch64.LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => VG.Proof.X448.AArch64.loop_ok hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Main`. -/
section

/-!
# X448 on AArch64: the whole function

The contract the proof is written against (the facts of
`Spec.X448.x448Contract` it uses, stated for AArch64), and the correctness of
`vg_x448` against it: every write is in the working space but the result's, so
the arguments are read unchanged, the callee-saved registers restored from the
working space, and the return address kept.
-/

namespace VG.Proof.X448

open VG VG.AArch64 in
/-- `vg_x448(out = x0, scalar = x1, point = x2, scratch = x3)`. -/
def x448AArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 56⟩
    let scalar : Region := ⟨s.gpr .x1, 56⟩
    let point : Region := ⟨s.gpr .x2, 56⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧
      (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.X448.bytesAt s'.mem (s.gpr .x0) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .x1) 56)
      (Spec.X448.bytesAt s.mem (s.gpr .x2) 56)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.X448

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Proof.X448

section
variable (s₀ : State)
abbrev outR : Region := ⟨s₀.gpr .x0, 56⟩
abbrev scalarR : Region := ⟨s₀.gpr .x1, 56⟩
abbrev pointR : Region := ⟨s₀.gpr .x2, 56⟩
abbrev scR : Region := ⟨s₀.gpr .x3, 8192⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.X448.AArch64.scalarR s₀, VG.Proof.X448.AArch64.pointR s₀]
  wr : s₀.wr = [VG.Proof.X448.AArch64.outR s₀, VG.Proof.X448.AArch64.scR s₀]
  out_sc : (VG.Proof.X448.AArch64.outR s₀).Disjoint (VG.Proof.X448.AArch64.scR s₀)
  scalar_sc : (VG.Proof.X448.AArch64.scalarR s₀).Disjoint (VG.Proof.X448.AArch64.scR s₀)
  point_sc : (VG.Proof.X448.AArch64.pointR s₀).Disjoint (VG.Proof.X448.AArch64.scR s₀)
  sc_fit : (s₀.gpr .x3).toNat + 8192 ≤ 2 ^ 64

theorem Pre.of (s₀ : State) (h : Proof.X448.x448AArch64.pre s₀) : VG.Proof.X448.AArch64.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : VG.Proof.X448.AArch64.Index)
    (hi : slot i.val + 128 ≤ o ∨ o + n ≤ slot i.val) : VG.Proof.X448.AArch64.E m' base i = VG.Proof.X448.AArch64.E m base i := by
  simp only [VG.Proof.X448.AArch64.E, VG.Proof.X448.AArch64.F]
  rw [h.fe hi (by have := i.isLt; simp only [slot]; omega)]

theorem correct {s₀ : State} (hp : VG.Proof.X448.AArch64.Pre s₀) :
    WP isa x448 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.X448.x448AArch64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .x3 = b := ⟨_, rfl⟩
  have hn : base.toNat + 8192 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .x2) j) 1 := fun j hj =>
    ⟨VG.Proof.X448.AArch64.pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x2) j) :=
    fun j hj => VG.Proof.X448.AArch64.far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x1) j) :=
    fun j hj => VG.Proof.X448.AArch64.far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [x448]
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.setup_ok hbase hw₀ hn rfl hr hd)
    fun s₁ ⟨hs₁, b₁, savedOut₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have kr : ∀ j < 56, InRegions (s₁.rd ++ s₁.wr) (off (s₀.gpr .x1) j) 1 := fun j hj =>
    ⟨VG.Proof.X448.AArch64.scalarR s₀, by rw [k₁.2.1, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.bits_ok hs₁ (k₁.1 _ (by decide)) kr kd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have k₂ : Keeps VG.Proof.X448.AArch64.bitRegs s₁ s₂ := ⟨g₂, rd₂, wr₂⟩
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.moveOutput_ok s₂) fun s₃ ⟨out₃, m₃, k₃⟩ => ?_)
  have k03 := k₁.then (k₂.then k₃)
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have sv₃ : VG.Proof.X448.AArch64.Saved base s₀.gpr s₃.mem := by rw [m₃]; exact sv₁.outside o₂ (by decide)
  have e₃ : ∀ i : VG.Proof.X448.AArch64.Index, VG.Proof.X448.AArch64.E s₃.mem base i = VG.Proof.X448.AArch64.E s₁.mem base i := by
    intro i; rw [m₃]; exact VG.Proof.X448.AArch64.E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₃ : VG.Proof.X448.AArch64.BoundedEnv s₃.mem base := by
    intro i j hj
    rw [m₃, o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact b₁ i j hj
  have kb := VG.Proof.X448.AArch64.bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.ladder_ok (s₀ := s₃) (s := s₃)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
    (fun t ht => by rw [m₃, bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨(hg _ (by decide)).trans hs₃.x3, (hg _ (by decide)).trans hs₃.mask, hw ▸ hs₃.wr, hn⟩, hm ▸ b₃,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₃ 0, x1₁], by rw [hm, e₃ 1, x2₁]; rfl,
      by rw [hm, e₃ 2, z2₁]; rfl, by rw [hm, e₃ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₃ 4, z3₁]; rfl,
      by rw [hm, m₃, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k36 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have out₆ : s₆.gpr .x1 = s₀.gpr .x0 :=
    (k36.1 _ (by decide)).trans (out₃.trans ((g₂ _ (by decide)).trans savedOut₁))
  have k06 := k03.then k36
  have hw₆ : ∀ j < 56, InRegions s₆.wr (off (s₀.gpr .x0) j) 1 := fun j hj =>
    ⟨VG.Proof.X448.AArch64.outR s₀, by rw [k06.2.2, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.X448.AArch64.finish_ok (k₆.scr hs₅) b₆ out₆ hw₆
    (fun j hj => VG.Proof.X448.AArch64.far_output (hbase ▸ hp.out_sc) hj) sv₆) fun s' ⟨rb, x20, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact x20
    all_goals exact kall.1 _ (by decide)
  · change Spec.X448.bytesAt s'.mem (s₀.gpr .x0) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, VG.Proof.X448.AArch64.invEnv_x2, VG.Proof.X448.AArch64.invEnv_eval, e₅]
    simp (config := {decide := true}) only [VG.Proof.X448.AArch64.opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, VG.Proof.X448.AArch64.cswap_fst, VG.Proof.X448.AArch64.cswap_fst]

end VG.Proof.X448.AArch64

end
