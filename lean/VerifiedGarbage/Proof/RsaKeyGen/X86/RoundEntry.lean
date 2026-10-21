module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.RoundCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset

/-! # The shared round's two arguments and the workspace preserved by their push -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

def entry (g : Geometry) (s : State) : State :=
  (pushed args s).callEntry.withRegions
    [⟨argAddr (pushed args s).callEntry 0, 8⟩] [⟨g.W, g.L⟩]

structure Arguments (g : Geometry) (capacity : Nat) (s : State) : Prop where
  base : s.gpr .edi = BitVec.ofNat 32 g.W.toNat
  length : s.gpr .edx = BitVec.ofNat 32 capacity

theorem entry_arg {g : Geometry} {s : State} {capacity : Nat}
    (A : Arguments g capacity s) (fit : 12 ≤ (s.gpr .esp).toNat) {i : Nat} (index : i < 2) :
    arg (entry g s) i = BitVec.ofNat 32 (if i = 0 then g.W.toNat else capacity) := by
  rw [entry, arg_withRegions, callEntry_arg (rs := args) (s := s) fit (by decide : Reg.esp ∉ args) index]
  have casesI : i = 0 ∨ i = 1 := by omega
  rcases casesI with rfl | rfl <;>
    simp only [args, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte, A.base, A.length] <;> rfl

theorem entry_frame {g : Geometry} {s : State}
    (fit : 12 ≤ (s.gpr .esp).toNat) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 12)) :
    WorkspaceFrame g [] s.mem (entry g s).mem := by
  have F := callEntry_frame (rs := args) fit (by decide : Reg.esp ∉ args)
  intro i index _
  apply F.bytes (R := ⟨g.W, g.L⟩)
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact far
  · change g.L ≤ 2 ^ 64
    omega
  · exact index

end VG.Proof.RsaKeyGen.X86.RoundCall
