module

public import VerifiedGarbage.Proof.X448.AArch64.Swap
public import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.X448.AArch64.Copy
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.X448.AArch64.Mul

/-!
# X448 on AArch64: the working space as field-element slots

Field operations update one of twenty-two slots, preserving bounded limbs in
every slot. The frame excludes saved registers, the swap bit and the scalar's
decoded bits.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev Index := Fin 22
abbrev Env := Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : Index) : Spec.X448.Fe := F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bounded m base (slot i.val)

def workRegs : List Reg := .x7 :: clob

structure Keep (base : Addr) (s t : State) : Prop where
  regs : Keeps workRegs s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : Keep base s t) (h' : Keep base t u) :
    Keep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : Keep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem slot_bound (i : Index) : Slot (slot i.val) := by
  simp only [Slot, slot, ACC]
  have := i.isLt
  omega

theorem slot_aligned (i : Index) : slot i.val % 8 = 0 := by
  simp only [slot]; omega

theorem slot_sep {i j : Index} (h : i ≠ j) : slot i.val + 128 ≤ slot j.val ∨ slot j.val + 128 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega

theorem Op.keep {base : Addr} {o : Index} {s t : State} (h : Op base (slot o.val) s t) : Keep base s t := by
  refine ⟨h.keeps.mono (fun _ hr => List.mem_cons_of_mem _ hr), ?_⟩
  intro p hp hq
  apply h.mem p _ hq
  have := o.isLt
  simp only [slot]
  omega

def opMul (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def opSub (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def opCopy (o a : Index) (e : Env) : Env := Function.update e o (e a)
def opSwap (x y : Index) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

end VG.Proof.X448.AArch64
