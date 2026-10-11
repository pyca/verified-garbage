import VerifiedGarbage.Impl.Modes.Ops
import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The modes' operations on areas, for any target

The contents of the three areas of a step are `Areas`, a byte for each area
and offset. `Op.apply` is what an operation does to them, as a target's
code does in memory: it reads its sources (`width` bytes at their offsets)
before it writes its destination. `applyOps` applies a list of them in
order. `copyBlk_apply`, `xorBlk_apply` and `shiftIn_apply` state the effect
of the block copies, block XORs and CFB8's shift.

A target's code only touches the bytes of an area below its length
(`InBounds`), so an area's other bytes never matter (`Agree`,
`applyOps_agree`).
-/

namespace VG.Proof.Modes

open VG VG.Impl.Modes

/-- The contents of the areas. -/
abbrev Areas := Loc → Nat → Byte

/-- The bytes an operation writes. -/
def _root_.VG.Impl.Modes.Op.width (o : Op) : Nat := if o.wide then 4 else 1

/-- Byte `t` of what `o` writes, from the areas `a` before it. -/
def _root_.VG.Impl.Modes.Op.val (o : Op) (a : Areas) (t : Nat) : Byte :=
  a o.src (o.sOff + t) ^^^ match o.xr with
    | none => 0
    | some (l, off) => a l (off + t)

/-- The areas after `o`. -/
def _root_.VG.Impl.Modes.Op.apply (o : Op) (a : Areas) : Areas := fun l i =>
  if l = o.dst ∧ o.dOff ≤ i ∧ i < o.dOff + o.width then o.val a (i - o.dOff) else a l i

/-- The areas after the operations `os`, in order. -/
def applyOps (os : List Op) (a : Areas) : Areas := os.foldl (fun a o => o.apply a) a

@[simp] theorem applyOps_nil (a : Areas) : applyOps [] a = a := rfl

theorem applyOps_cons (o : Op) (os : List Op) (a : Areas) : applyOps (o :: os) a = applyOps os (o.apply a) := rfl

theorem applyOps_append (os os' : List Op) (a : Areas) : applyOps (os ++ os') a = applyOps os' (applyOps os a) := by
  simp [applyOps, List.foldl_append]

theorem applyOps_snoc (os : List Op) (o : Op) (a : Areas) : applyOps (os ++ [o]) a = o.apply (applyOps os a) := by
  rw [applyOps_append]; rfl

/-! ## Bounds -/

/-- Every byte `o` reads or writes is below its area's length in `len`. -/
def _root_.VG.Impl.Modes.Op.InBounds (len : Loc → Nat) (o : Op) : Prop :=
  o.dOff + o.width ≤ len o.dst ∧ o.sOff + o.width ≤ len o.src ∧
    ∀ l off, o.xr = some (l, off) → off + o.width ≤ len l

/-- `a` and `a'` agree below the areas' lengths. -/
def Agree (len : Loc → Nat) (a a' : Areas) : Prop := ∀ l i, i < len l → a l i = a' l i

theorem _root_.VG.Impl.Modes.Op.apply_agree {len : Loc → Nat} {o : Op} (ho : o.InBounds len) {a a' : Areas} (h : Agree len a a') :
    Agree len (o.apply a) (o.apply a') := by
  intro l i hi
  simp only [Op.apply]
  split
  · rename_i hl
    obtain ⟨-, h1, h2⟩ := hl
    simp only [Op.val]
    rw [h _ _ (by have := ho.2.1; omega)]
    congr 1
    split
    · rfl
    · rename_i l' off e
      exact h _ _ (by have := ho.2.2 l' off e; omega)
  · exact h l i hi

theorem applyOps_agree {len : Loc → Nat} : ∀ {os : List Op}, (∀ o ∈ os, o.InBounds len) →
    ∀ {a a' : Areas}, Agree len a a' → Agree len (applyOps os a) (applyOps os a')
  | [], _, _, _, h => h
  | o :: _, hb, _, _, h =>
    applyOps_agree (fun o' ho' => hb o' (List.mem_cons_of_mem _ ho'))
      (Op.apply_agree (hb o List.mem_cons_self) h)

/-! ## Blocks -/

theorem copyBlk_succ (bw : Nat) (dst src : Loc) :
    copyBlk (bw + 1) dst src = copyBlk bw dst src ++ [{ wide := true, dst, dOff := 4 * bw, src, sOff := 4 * bw }] := by
  simp [copyBlk, List.range_succ]

theorem xorBlk_succ (bw : Nat) (dst x y : Loc) :
    xorBlk (bw + 1) dst x y =
      xorBlk bw dst x y ++ [{ wide := true, dst, dOff := 4 * bw, src := x, sOff := 4 * bw, xr := some (y, 4 * bw) }] := by
  simp [xorBlk, List.range_succ]

theorem byte_xor_zero (x : Byte) : x ^^^ 0 = x := by simp

/-- Close a goal of nested `if`s on arithmetic conditions. -/
local macro "arith_ifs" : tactic =>
  `(tactic| ((repeat' split) <;> (try rw [byte_xor_zero]) <;>
    first | rfl | (exfalso; omega) | (congr 1; omega)))

/-- A block copy: `dst`'s first `4 bw` bytes are `src`'s. -/
theorem copyBlk_apply {dst src : Loc} (hne : dst ≠ src) (a : Areas) :
    ∀ bw l i, applyOps (copyBlk bw dst src) a l i = if l = dst ∧ i < 4 * bw then a src i else a l i
  | 0, l, i => by simp [copyBlk]
  | bw + 1, l, i => by
    rw [copyBlk_succ, applyOps_snoc]
    simp only [Op.apply, Op.val, Op.width, ite_true, copyBlk_apply hne a bw]
    by_cases hl : l = dst
    · subst hl
      simp only [true_and, Ne.symm hne, false_and, ite_false]
      arith_ifs
    · simp only [hl, false_and, ite_false]

/-- A block XOR: `dst`'s first `4 bw` bytes are `x`'s XORed with `y`'s
(which may be `dst` itself). -/
theorem xorBlk_apply (dst x y : Loc) (a : Areas) :
    ∀ bw l i, applyOps (xorBlk bw dst x y) a l i = if l = dst ∧ i < 4 * bw then a x i ^^^ a y i else a l i
  | 0, l, i => by simp [xorBlk]
  | bw + 1, l, i => by
    rw [xorBlk_succ, applyOps_snoc]
    simp only [Op.apply, Op.val, Op.width, ite_true, xorBlk_apply dst x y a bw]
    have h4 : ¬ (4 * bw + (i - 4 * bw) < 4 * bw) := by omega
    simp only [h4, and_false, ite_false]
    by_cases hl : l = dst
    · subst hl
      simp only [true_and]
      by_cases h1 : 4 * bw ≤ i ∧ i < 4 * bw + 4
      · rw [ite_eq_left h1, ite_eq_left (by omega), show 4 * bw + (i - 4 * bw) = i by omega]
      · rw [ite_eq_right h1]
        arith_ifs
    · simp only [hl, false_and, ite_false]

/-- The first `k` bytes of CFB8's shift. -/
theorem shiftBytes_apply (a : Areas) :
    ∀ k l i, applyOps ((List.range k).map fun i =>
        ({ wide := false, dst := .chn, dOff := i, src := .chn, sOff := i + 1 } : Op)) a l i =
      if l = .chn ∧ i < k then a .chn (i + 1) else a l i
  | 0, l, i => by simp
  | k + 1, l, i => by
    rw [List.range_succ, List.map_append, List.map_singleton, applyOps_snoc]
    simp only [Op.apply, Op.val, Op.width, Bool.false_eq_true, ite_false, shiftBytes_apply a k]
    have h4 : ¬ (k + 1 + (i - k) < k) := by omega
    simp only [h4, and_false, ite_false]
    by_cases hl : l = .chn
    · subst hl
      simp only [true_and]
      arith_ifs
    · simp only [hl, false_and, ite_false]

/-- CFB8's shift: the input block without its first byte, followed by the
data byte. -/
theorem shiftIn_apply (bw : Nat) (a : Areas) (l : Loc) (i : Nat) :
    applyOps (Mode.shiftIn bw) a l i =
      if l = .chn ∧ i < 4 * bw - 1 then a .chn (i + 1)
      else if l = .chn ∧ i = 4 * bw - 1 then a .dat 0 else a l i := by
  rw [Mode.shiftIn, applyOps_snoc]
  simp only [Op.apply, Op.val, Op.width, Bool.false_eq_true, ite_false, shiftBytes_apply]
  have hd : ¬ (Loc.dat = Loc.chn) := nofun
  simp only [hd, false_and, ite_false]
  by_cases hl : l = .chn
  · subst hl
    simp only [true_and]
    arith_ifs
  · simp only [hl, false_and, ite_false]

/-! ## Bounds of the modes' operations -/

theorem copyBlk_inBounds {len : Loc → Nat} {bw : Nat} {dst src : Loc} (hd : 4 * bw ≤ len dst)
    (hs : 4 * bw ≤ len src) : ∀ o ∈ copyBlk bw dst src, o.InBounds len := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  exact ⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun _ _ h => by cases h⟩

theorem xorBlk_inBounds {len : Loc → Nat} {bw : Nat} {dst x y : Loc} (hd : 4 * bw ≤ len dst)
    (hx : 4 * bw ≤ len x) (hy : 4 * bw ≤ len y) : ∀ o ∈ xorBlk bw dst x y, o.InBounds len := by
  intro o ho
  simp only [xorBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  exact ⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun l off h => by
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [Op.width]; omega⟩

theorem shiftIn_inBounds {len : Loc → Nat} {bw : Nat} (hbw : 0 < bw) (hc : 4 * bw ≤ len .chn)
    (hd : 1 ≤ len .dat) : ∀ o ∈ Mode.shiftIn bw, o.InBounds len := by
  intro o ho
  simp only [Mode.shiftIn, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ho
  rcases ho with ⟨i, hi, rfl⟩ | rfl
  · exact ⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun _ _ h => by cases h⟩
  · exact ⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun _ _ h => by cases h⟩

theorem xorByte_inBounds {len : Loc → Nat} (hd : 1 ≤ len .dat) (hb : 1 ≤ len .buf) :
    ({ wide := false, dst := .dat, dOff := 0, src := .dat, sOff := 0, xr := some (.buf, 0) } : Op).InBounds len :=
  ⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun l off h => by
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [Op.width]; omega⟩

end VG.Proof.Modes
