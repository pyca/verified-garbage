module

import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Words
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Steps of the key search (x86)

The registers the controller uses for itself (`Scratch`), which no
callee-saved register is (`saved_ne`), and the words of its state through a
store (`Ctl.write'`) and on fewer offsets (`Ctl.sub`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The registers the controller uses for itself. -/
abbrev Scratch (r : Reg) : Prop := r = .eax ∨ r = .ecx ∨ r = .edx

theorem saved_ne {r q : Reg} (hq : Scratch q) (hr : r ∈ calleeSaved) : r ≠ q := by
  rcases hq with rfl | rfl | rfl <;> simp [calleeSaved] at hr <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- A store and the word it keeps. -/
theorem Ctl.write' {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0)
    (v : BitVec 32) : Ctl (m.writeW (addr S d) v) S (d :: ds) (upd f d v) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rw [readW_write hS v hd hd (Or.inl rfl)]; simp [upd]
  · exact h.write hS hA hd hd4 v e he

theorem Aligned.cons {ds : List Nat} (h : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) :
    Aligned (d :: ds) := fun e he => by
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨hd, hd4⟩
  · exact h e he

theorem Ctl.sub {m : Mem} {S : BitVec 32} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f)
    (hs : ∀ d ∈ ds', d ∈ ds) : Ctl m S ds' f := fun d hd => h d (hs d hd)

end VG.Proof.Ffdh.X86.KeySearch
