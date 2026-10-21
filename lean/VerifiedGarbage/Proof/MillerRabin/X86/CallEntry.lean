module

import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame

/-! # Montgomery's arguments and the disjoint stack of an i686 round -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def mulArgs : List Reg := [.eax, .ecx, .ecx, .edx, .edi]

def mulEntry (g : Geometry) (s : State) : State :=
  (pushed mulArgs s).callEntry.withRegions
    [⟨argAddr (pushed mulArgs s).callEntry 0, 20⟩] [⟨g.W, g.L⟩]

structure MulArguments (g : Geometry) (capacity b : Nat) (s : State) : Prop where
  base : s.gpr .edi = BitVec.ofNat 32 g.W.toNat
  length : s.gpr .edx = BitVec.ofNat 32 capacity
  index : s.gpr .ecx = 6#32
  right : s.gpr .eax = BitVec.ofNat 32 b

theorem mulEntry_arg {g : Geometry} {s : State} {capacity b : Nat}
    (A : MulArguments g capacity b s) (fit : 24 ≤ (s.gpr .esp).toNat) {i : Nat} (index : i < 5) :
    arg (mulEntry g s) i = BitVec.ofNat 32
      (if i = 0 then g.W.toNat else if i = 1 then capacity else if i = 4 then b else 6) := by
  rw [mulEntry, arg_withRegions, callEntry_arg (rs := mulArgs) (s := s) fit (by decide : Reg.esp ∉ mulArgs) index]
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases casesI with rfl | rfl | rfl | rfl | rfl <;>
    simp only [mulArgs, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte, A.base, A.length, A.index, A.right] <;> rfl

theorem mulEntry_frame {g : Geometry} {s : State}
    (fit : 24 ≤ (s.gpr .esp).toNat) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 24)) :
    WorkspaceFrame g [] s.mem (mulEntry g s).mem := by
  have F := callEntry_frame (rs := mulArgs) fit (by decide : Reg.esp ∉ mulArgs)
  intro i index _
  apply F.bytes (R := ⟨g.W, g.L⟩)
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact far
  · have := nowrap
    change g.L ≤ 2 ^ 64
    omega
  · exact index

end VG.Proof.MillerRabin.X86
