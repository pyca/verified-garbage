module

public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.InputBuffer
import VerifiedGarbage.Proof.Framework.Offset

/-! # Caller inputs and component addresses after argument installation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem Installed.input {base : Addr} {size keyArg pLenArg qLenArg : Nat}
    {args : List (Nat × Field)} {s t : State}
    (I : Installed base size args keyArg pLenArg qLenArg s t)
    {i len : Nat} {f : Field} (member : (i, f) ∈ args)
    (bound : (arg s i).toNat + len ≤ 2 ^ 32)
    (read : (⟨argumentPointer s i, len⟩ : Region) ∈ s.rd ++ s.wr)
    (apart : Region.Disjoint ⟨argumentPointer s i, len⟩ ⟨base, size⟩)
    (room : Pow.Room (s.gpr .esp) base size)
    (stack : Region.Disjoint ⟨argumentPointer s i, len⟩ (callStack (s.gpr .esp))) :
    CallerBuffer t base size (.input f) len ∧
    Spec.Rsa.bytesAt t.mem ((pointerValue base t (.input f)).setWidth 64) len =
      Spec.Rsa.bytesAt s.mem (argumentPointer s i) len := by
  have ptr := I.arguments (i, f) member
  refine ⟨inputBuffer I.keeps ptr bound ?_ apart
      (by rw [I.keeps.1 _ (by decide)]; exact room)
      (by rw [I.keeps.1 _ (by decide)]; exact stack),
    inputBytes_keep I.outside ptr (by omega) (by have := I.scr.nowrap; omega) apart⟩
  intro d k hd
  exact ⟨_, read, Offset.contains_base _ hd (by omega)⟩

theorem Installed.pointers {base : Addr} {size keyArg pLenArg qLenArg : Nat}
    {args : List (Nat × Field)} {s t : State}
    (I : Installed base size args keyArg pLenArg qLenArg s t)
    (keyMem : (keyArg, .p) ∈ args) :
    pointerValue base t (.input .q) = pointerValue base t (.input .p) + BitVec.ofNat 32 (arg s pLenArg).toNat ∧
    pointerValue base t (.input .g) = pointerValue base t (.input .p) + BitVec.ofNat 32 ((arg s pLenArg).toNat + (arg s qLenArg).toNat) ∧
    pointerValue base t (.input .y) = pointerValue base t (.input .p) + BitVec.ofNat 32 (2 * (arg s pLenArg).toNat + (arg s qLenArg).toNat) ∧
    pointerValue base t (.input .x) = pointerValue base t (.input .p) + BitVec.ofNat 32 (3 * (arg s pLenArg).toNat + (arg s qLenArg).toNat) := by
  rw [I.arguments (keyArg, .p) keyMem, I.qPointer, I.gPointer, I.yPointer, I.xPointer]
  have two : 2 * (arg s pLenArg).toNat + (arg s qLenArg).toNat =
      (arg s pLenArg).toNat + (arg s qLenArg).toNat + (arg s pLenArg).toNat := by omega
  have three : 3 * (arg s pLenArg).toNat + (arg s qLenArg).toNat =
      (arg s pLenArg).toNat + (arg s qLenArg).toNat + (arg s pLenArg).toNat + (arg s pLenArg).toNat := by omega
  simp only [two, three, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc, and_self]


theorem Installed.compare {base : Addr} {size keyArg pLenArg qLenArg : Nat}
    {args : List (Nat × Field)} {s t u : State}
    (I : Installed base size args keyArg pLenArg qLenArg s t)
    (K : Keeps [.eax] t u) (O : u.mem = t.mem) :
    Installed base size args keyArg pLenArg qLenArg s u := by
  refine ⟨I.scr.of_keeps K (by decide), ?_, ?_, ?_, ?_, ?_, ?_,
    I.keeps.trans (K.mono (by decide)), ?_⟩
  · rw [O]; exact I.saved
  · intro a ha; simpa only [pointerValue, O] using I.arguments a ha
  · simpa only [pointerValue, O] using I.qPointer
  · simpa only [pointerValue, O] using I.gPointer
  · simpa only [pointerValue, O] using I.yPointer
  · simpa only [pointerValue, O] using I.xPointer
  · rw [O]; exact I.outside

end VG.Proof.Dsa.X86
