module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.X448.X86_64.Env

import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.X448.X86_64.Setup

/-! A complete coordinate scan, with one final write to scratch. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.X448.X86_64
open VG.Proof.X448 (toFe)
open VG.Impl.X448.X86_64 (W slot stores)

abbrev ScanRegs : List Reg := .rax :: W

/-- The per-entry selection's memory and register contract. -/
def PickOk (pick : Nat → List Instr) (value : Mem → Addr → Nat → Spec.X448.Fe) : Prop :=
  ∀ (i : Nat), i < 17 → ∀ {s : State} {base : Addr}, Scr s base → ∀ {sw : Bool}, s.zf = sw →
    WP isa (.block (pick i)) s fun u =>
      toFe (rv u W) = (if sw then value s.mem base i else toFe (rv s W)) ∧ Keeps ScanRegs s u

private def picked (f : Nat → Spec.X448.Fe) (xs : List Nat) (d : Nat) (q : Spec.X448.Fe) :=
  xs.foldl (fun q i => if d = i then f i else q) q

private theorem picked_eq (f : Nat → Spec.X448.Fe) (xs : List Nat) (d : Nat) (q : Spec.X448.Fe) :
    picked f xs d q = if d ∈ xs then f d else q := by
  induction xs generalizing q with
  | nil => simp [picked]
  | cons i xs ih =>
    change picked f xs d (if d = i then f i else q) = _
    rw [ih]
    by_cases hi : d = i
    · subst i; simp
    · by_cases hx : d ∈ xs <;> simp [hi, hx]

private theorem entries_ok {pick : Nat → List Instr} {value : Mem → Addr → Nat → Spec.X448.Fe}
    (hp : PickOk pick value) (xs : List Nat) (hx : ∀ i ∈ xs, i < 17)
    {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 17)
    (hr : s.gpr .r15 = BitVec.ofNat 64 d) :
    WP isa (.block (scanEntries pick xs)) s fun u =>
      toFe (rv u W) = picked (value s.mem base) xs d (toFe (rv s W)) ∧ Keeps ScanRegs s u := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Keeps.refl _ _⟩
  | cons i xs ih =>
    rw [scanEntries, List.flatMap_cons, List.append_assoc, WP.block_append_iff]
    refine WP.mono (compareDigit_ok hd (hx i List.mem_cons_self) hr) fun v ⟨zv, kv⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (hp i (hx i List.mem_cons_self) (hs.of_keeps kv (by decide)) zv)
      fun w ⟨ew, kw⟩ => ?_
    refine WP.mono (ih (fun j hj => hx j (List.mem_cons_of_mem _ hj))
      ((hs.of_keeps kv (by decide)).of_keeps kw (by decide))
      ((kw.1 _ (by decide)).trans ((kv.1 _ (by decide)).trans hr))) fun u ⟨eu, ku⟩ => ?_
    refine ⟨?_, ((kv.mono (by simp)).trans kw).trans ku⟩
    rw [eu, ew, kw.2.1, kv.2.1]
    have ev : rv v W = rv s W := rv_congr (fun r _ => kv.1 r (by simp))
    rw [ev]
    simp only [decide_eq_true_eq, picked, List.foldl_cons]

/-- The selected coordinate is stored once; the digit and all other slots survive. -/
theorem scanCoord_ok {pick : Nat → List Instr} {value : Mem → Addr → Nat → Spec.X448.Fe}
    (hp : PickOk pick value) {s : State} {base : Addr} (hs : Scr s base)
    (i : Index) {d : Nat} (hd : d < 17) (hr : s.gpr .r15 = BitVec.ofNat 64 d) :
    WP isa (.block (scanCoord pick (slot i.val))) s fun u =>
      Keep base s u ∧ u.gpr .r15 = s.gpr .r15 ∧
      E u.mem base = Function.update (E s.mem base) i (value s.mem base d) := by
  rw [scanCoord, WP.block_append_iff]
  refine WP.mono (entries_ok hp (List.range 17) (fun j hj => List.mem_range.mp hj) hs hd hr)
    fun v ⟨ev, kv⟩ => ?_
  refine WP.mono (stores_E (hs.of_keeps kv (by decide)) i W rfl)
    fun u ⟨eu, ou, gu, ru, wu⟩ => ?_
  refine ⟨⟨?_, ru.trans kv.2.2.1, wu.trans kv.2.2.2, ?_⟩,
    (gu _).trans (kv.1 _ (by decide)), ?_⟩
  · intro r hr
    exact (gu r).trans (kv.1 r (fun h => hr ((show ∀ r ∈ ScanRegs, r ∈ clob from by decide) r h)))
  · rw [kv.2.1] at ou
    exact ou.mono (slot_ge i) (by have := slot_lt i; simp only [Impl.X448.X86_64.ACC] at this; omega)
  · rw [eu, ev, picked_eq, ite_eq_left (List.mem_range.mpr hd), kv.2.1]

end VG.Proof.Ed448.X86_64.Window
