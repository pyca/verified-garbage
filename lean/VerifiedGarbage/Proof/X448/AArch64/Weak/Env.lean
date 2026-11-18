module

import VerifiedGarbage.Proof.Curve448.AArch64.Swap
public import VerifiedGarbage.Proof.X448.AArch64.Env
public import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
public import VerifiedGarbage.Impl.Curve448.AArch64
import VerifiedGarbage.Proof.Curve448.AArch64.Stage
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.X448.AArch64.Weak
import VerifiedGarbage.Proof.Curve448.AArch64.AddEval
public import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Proof.X448.Wide.Representation
public import VerifiedGarbage.Proof.X448.Wide.Word
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Curve448.AArch64.Product
import VerifiedGarbage.Proof.X448.Wide.Reduce
import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
import VerifiedGarbage.Proof.X448.Wide.LoadCached
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.X448.AArch64.Symmetric
public import VerifiedGarbage.Proof.X448.Wide.CacheRegs
public import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Proof.X448.Wide.Product
import VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumn
import VerifiedGarbage.Proof.Framework.Range

/-! ### `Curve448.AArch64.Square`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.SymmetricColumns`, which this module and modules that import it used -/

section

/-! Untrusted: the complete two-word coefficient array of a wide product. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem symmetricColumns_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (fc : ∀ i < 8, (s.gpr (Impl.X448.AArch64.Cached.cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) :
    WP isa (.block ((List.range 16).flatMap (Impl.X448.AArch64.Symmetric.column))) s fun t =>
      (∀ k < 16, coeff t.mem base ACC k = rows f f 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t := by
  let inv := fun n (t : State) =>
    (∀ k < 16, coeff t.mem base ACC k = if k < n then rows f f 8 k else coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (Impl.X448.AArch64.Symmetric.column n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (symmetricColumn_ok (hs.of_keeps tk (by decide)) hn (by
      intro i hi; rw [tk.1 _ (cacheReg_kept hi)]; exact fc i hi) fb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega_using []), uv]

    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega_using [h]
      change pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [outside_coeff um hsep (by simp only [ACC]; omega_using [hk])]
      change coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega_using [h])
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega_using [])], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.Curve448.AArch64

end

end

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem square_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (ab : Bounded s.mem base a) :
    WP isa (Impl.Curve448.AArch64.sqr o a) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  let f := limbs s.mem base a
  rw [Impl.Curve448.AArch64.sqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadCached_ok hs (by have := ha; change a + 128 ≤ 3584 at this; omega_using [this]) ha8)
    fun s₁ ⟨c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have fc : ∀ i < 8, (s₁.gpr (cacheReg i)).toNat = f i := by intro i hi; rw [c₁ i hi]
  rw [WP.block_append_iff]
  refine WP.mono (symmetricColumns_ok hs₁ fc ab) fun s₂ ⟨c₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have raw : ∀ i < 16, coeff s₂.mem base ACC i < 2 ^ 116 := by
    intro i hi; rw [c₂ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.Curve448.AArch64.rows_bound ab ab (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₂ raw) fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  have red := reduced_bound raw
  refine WP.mono (normalize_ok (hs₂.of_keeps k₃ (by decide)) ho ho8 r₃ red) fun t ⟨tf, tm, tk⟩ => ?_
  have val : fe t.mem base o % Spec.X448.P = (fe s.mem base a * fe s.mem base a) % Spec.X448.P := by
    rw [show fe t.mem base o = VG.Proof.X448.Wide.valN
        (folded (folded (reduced (coeff s₂.mem base ACC)))) 8 from
        VG.Proof.X448.Wide.valN_congr tf, twice_mod, reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₂, rows_val f f (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans (tk.mono (by decide))))
  · rw [m₁] at m₂
    exact (FieldMem.work m₂ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans tm)
  · intro i hi; rw [tf i hi]; exact twice_weak red i hi

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.Curve448.AArch64.mul o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [Impl.Curve448.AArch64.mul]
  by_cases h : a = b
  · rw [ite_eq_left h, ← h]; exact square_ok hs ho ho8 ha ha8 ab
  · rw [ite_eq_right h]; exact product_ok hs ho ho8 ha ha8 hb hb8 ab bb
end VG.Proof.Curve448.AArch64

end

end

/-! ### `Curve448.AArch64.Pointwise`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.SmallEval`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Proof.Ed25519.AArch64 (mulHi read_x mul_lo_hi)

theorem smallEval_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block (Impl.Curve448.AArch64.smallEval a i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = 39081 * limbs s.mem base a i ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega_using [hi, ha])
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega_using [ha8, hi, ha]
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.smallEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, ae, and_self, hs.x3, la, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · have h := mul_lo_hi (word s.mem base (a + 8 * i)) (BitVec.setWidth 64 (39081 : BitVec 16))
    rw [show (BitVec.setWidth 64 (39081 : BitVec 16)).toNat = 39081 by decide, Nat.mul_comm _ 39081] at h
    dsimp only [pair, mulHi, Size.bits] at h ⊢
    exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
end VG.Proof.Curve448.AArch64

end

end

/-! ### `Curve448.AArch64.SubEval`, which this module and modules that import it used -/

section

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem subEval_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (hi : i < 8)
    (ab : limbs s.mem base a i < weakBound) (bb : limbs s.mem base b i < weakBound) :
    WP isa (.block (Impl.Curve448.AArch64.subEval a b i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = difference (limbs s.mem base a) (limbs s.mem base b) i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega_using [hi, ha])
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega_using [hi, hb])
  have biasb := bias_ge i
  have biashi : bias i < 2 ^ 59 := by unfold bias; split <;> decide +kernel
  have biasword : (((((BitVec.setWidth 64 (if i = 4 then (0xfff8 : BitVec 16) else 0xfffc)) &&& ~~~((0xffff : BitVec 64) <<< 16)) ||| ((BitVec.setWidth 64 (0xffff : BitVec 16)) <<< 16)) &&& ~~~((0xffff : BitVec 64) <<< 32) ||| ((BitVec.setWidth 64 (0xffff : BitVec 16)) <<< 32)) &&& ~~~((0xffff : BitVec 64) <<< 48) ||| ((BitVec.setWidth 64 (0x03ff : BitVec 16)) <<< 48)).toNat = bias i := by
    by_cases h : i = 4 <;> simp only [h, ite_true, ite_false, bias] <;> decide +kernel
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega_using [ha8, hi, ha]
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega_using [hb8, hi, hb]
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.subEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero, BitVec.toNat_sub, BitVec.toNat_add, biasword]
    change (2 ^ 64 - limbs s.mem base b i +
      (limbs s.mem base a i + bias i) % 2 ^ 64) % 2 ^ 64 =
      limbs s.mem base a i + bias i - limbs s.mem base b i
    simp only [weakBound, radix] at ab bb biasb
    omega_using [ab, bb, biasb, biashi]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Curve448.AArch64

end

end

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Proof.X448.AArch64

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : Within (radix * 6) f := by
    intro i hi; have h1 := ab i hi; have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [weakBound, radix] at h1 h2 ⊢; omega_arith
  refine WP.mono (stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_add ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (addEval_ok ts ha ha8 hb hb8 hi (by rw [ea]; exact ab i hi) (by rw [eb]; exact bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [ea, eb] at uv; exact uv
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : Within (radix * 6) f := by
    intro i hi; have h := ab i hi
    change difference (limbs s.mem base a) (limbs s.mem base b) i < _
    simp only [difference, bias, weakBound, radix] at h ⊢
    split <;> omega_arith
  refine WP.mono (stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_sub ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subEval_ok ts ha ha8 hb hb8 hi (by rw [ea]; exact ab i hi) (by rw [eb]; exact bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    simp only [difference, ea, eb] at uv; exact uv
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb,
      Nat.mul_comm 4 Spec.X448.P, Nat.add_mul_mod_self_left]

theorem small_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (ab : Bounded s.mem base a) :
    WP isa (.block (Impl.Curve448.AArch64.small o a)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : Within (2 ^ 118) f := by
    intro i hi
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))) (by decide)
  refine WP.mono (stage_normalize hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_a24 ?_⟩
  · intro i hi t ts tm
    refine WP.mono (smallEval_ok ts ha ha8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [input_limb tm ha hi] at uv; exact uv
  · rw [tv, valN_scale]
end VG.Proof.Curve448.AArch64

end

end

/-!
# X448 on AArch64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Field operations update one
of twenty-two slots, preserving bounded limbs in every slot. The frame
excludes saved registers, the swap bit and the scalar's decoded bits.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.Curve448.AArch64
open VG.Impl.X448.AArch64.Weak
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe :=
  VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs m base o) 8)
abbrev Bounded := VG.Proof.Curve448.AArch64.Bounded
theorem valN_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    VG.Proof.X448.Wide.valN f n = VG.Proof.X448.Wide.valN g n := VG.Proof.X448.Wide.valN_congr h

abbrev Index := Fin 22
abbrev Env := Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : Index) : Spec.X448.Fe := F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bounded m base (slot i.val)

abbrev workRegs := VG.Proof.X448.AArch64.workRegs
abbrev Keep := VG.Proof.X448.AArch64.Keep

theorem slot_bound (i : Index) : Slot (slot i.val) := by
  simp only [Slot, slot, ACC]
  have := i.isLt
  omega_using []

theorem slot_aligned (i : Index) : slot i.val % 8 = 0 := by
  simp only [slot]; omega_using []

theorem slot_sep {i j : Index} (h : i ≠ j) : slot i.val + 128 ≤ slot j.val ∨ slot j.val + 128 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega_using [hn]

theorem E_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m') :
    E m' base = Function.update (E m base) o (F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, E]
  · rw [Function.update_of_ne hi]
    simp only [E, F]
    exact congrArg toFe (valN_congr (fun j hj =>
      h.limbs (slot_sep hi) (slot_bound i) (by omega_using [hj] : j < 16)))

theorem bounded_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m')
    (hm : BoundedEnv m base) (ho : Bounded m' base (slot o.val)) : BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (slot_sep hi) (slot_bound i) (by omega_using [hj] : j < 16)]
    exact hm i j hj

def opMul (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def opAdd (o a b : Index) (e : Env) : Env := Function.update e o (e a + e b)
def opSub (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def opA24 (o a : Index) (e : Env) : Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : Index) (e : Env) : Env := Function.update e o (e a)
def opSwap (x y : Index) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (Impl.Curve448.AArch64.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opMul o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.mul_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) * F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.Curve448.AArch64.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opAdd o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.add_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) + F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.Curve448.AArch64.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opSub o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.sub_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) - F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.small (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opA24 o a (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.small_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (hb a)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = Spec.X448.a24 * F s.mem base (slot a.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opCopy o a (E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (Nat.le_trans (slot_bound o) (by decide))
    (Nat.le_trans (slot_bound a) (by decide)) (slot_aligned o) (slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [E_update op.mem, show F t.mem base (slot o.val) = F s.mem base (slot a.val) from
      congrArg toFe (valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      E t.mem base = opSwap x y sw (E s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.cswap_ok hs (slot_bound x) (slot_bound y) (slot_aligned x) (slot_aligned y) (slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : Index, i ≠ x → i ≠ y → ∀ j < 8,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := slot_sep hix
    have ey := slot_sep hiy
    have hi := slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega_using [hj, ex]) (by omega_using [hj, ey]) (by change slot i.val + 128 ≤ 3584 at hi; omega_using [hj, hi])]
  have fx : E t.mem base x = if sw then E s.mem base y else E s.mem base x := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact tx
  have fy : E t.mem base y = if sw then E s.mem base x else E s.mem base y := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, ?_, tk.1 _ (by decide), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega_using [hp]
  · intro i j hj
    by_cases hix : i = x
    · subst i; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · rw [other i hix hiy j hj]; exact hb i j hj
  · funext i
    by_cases hiy : i = y
    · subst i; rw [opSwap, Function.update_self]; exact fy
    · rw [opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg toFe (valN_congr (other i hix hiy))

end VG.Proof.X448.AArch64.Weak
