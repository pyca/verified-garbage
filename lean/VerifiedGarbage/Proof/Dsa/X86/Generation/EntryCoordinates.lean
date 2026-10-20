module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryGeometry
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryRegions

/-! # Relate the incoming cdecl arguments to the internal frame offsets -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont

theorem ParameterABI.entryBound {s : State} (A : ParameterABI s) :
    A.geometry.frameBase.toNat + 216 ≤ 2 ^ 32 := by
  rw [A.geometry.frame_toNat]
  change (s.gpr .esp - 164#32).toNat + 216 ≤ 2 ^ 32
  rw [sub_toNat (by have := A.stackLow; omega)]
  have := A.stackBound
  omega

theorem ParameterABI.argAddress {s : State} (A : ParameterABI s) {j : Nat} (bound : j < 12) :
    off A.geometry.frameBase (168 + 4 * j) = argAddr s j := by
  rw [A.frameBase]
  have room : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32 := by have := A.stackBound; omega
  change ((s.gpr .esp).setWidth 64 - 164#64) + BitVec.ofNat 64 (168 + 4 * j) =
    addr (s.gpr .esp) (4 + 4 * j)
  rw [addr_eq room]
  rw [show 168 + 4 * j = 164 + (4 + 4 * j) by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem ParameterABI.argsStack {s : State} (_A : ParameterABI s) :
    (⟨argAddr s 0, 48⟩ : Region).Disjoint ⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ := by
  change (⟨addr (s.gpr .esp) 4, 48⟩ : Region).Disjoint _
  rw [addr_eq (by have := _A.stackBound; omega)]
  exact Offset.disjoint_below _ (by decide)
theorem ParameterABI.argsContains {s : State} (A : ParameterABI s) {j : Nat} (bound : j < 12) :
    (⟨argAddr s 0, 48⟩ : Region).Contains (argAddr s j) 4 := by
  rw [← A.argAddress bound, ← A.argAddress (by decide : 0 < 12)]
  have eq : off A.geometry.frameBase (168 + 4 * j) = off (off A.geometry.frameBase 168) (4 * j) := by
    simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [eq]
  exact Offset.contains_base _ (by omega) (by omega)
end VG.Proof.Dsa.X86.Generation
