module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller

/-! # A round stage combines values, reusable modulus data and the nested-call ABI -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

structure Stage (g : Geometry) (capacity c : Nat) (p : BitVec 32)
    (A : Nat → Nat) (Js : List Nat) (V : Nat → BitVec 32) (Ds : List Nat) (s : State) : Prop where
  data : Data g A Js V Ds s
  modulus : Modulus g c s.mem
  caller : Caller g capacity p s
  noScratch : ∀ j ∈ Js, j ≠ 2 ∧ j ≠ 3

theorem Stage.mono {g : Geometry} {capacity c : Nat} {p : BitVec 32}
    {A A' : Nat → Nat} {Js Js' : List Nat} {V V' : Nat → BitVec 32} {Ds Ds' : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (arrays : ∀ j ∈ Js', j ∈ Js ∧ A j = A' j)
    (slots : ∀ d ∈ Ds', d ∈ Ds ∧ V d = V' d) : Stage g capacity c p A' Js' V' Ds' s :=
  ⟨S.data.mono arrays slots, S.modulus, S.caller, fun j mem => S.noScratch j (arrays j mem).1⟩

theorem Stage.keepMem {g : Geometry} {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s t : State}
    (S : Stage g capacity c p A Js V Ds s) {regs : List Reg} (K : VG.Proof.Mont.X86.Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (mem : t.mem = s.mem) : Stage g capacity c p A Js V Ds t := by
  refine ⟨⟨S.data.context.keepMem K base mem, ?_, ?_⟩, ?_, ?_, S.noScratch⟩
  · intro j known
    rw [mem]
    exact S.data.arrayValues j known
  · intro d known
    rw [mem]
    exact S.data.slotValues d known
  · rw [mem]; exact S.modulus
  · apply S.caller.keepFrame K sp
    rw [mem]
    exact Frame.refl _ _

end VG.Proof.MillerRabin.X86
