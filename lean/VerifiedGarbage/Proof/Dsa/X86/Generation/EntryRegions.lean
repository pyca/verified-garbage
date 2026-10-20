module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryGeometry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTape
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Internal frame and arena regions are subsets of the caller's reservations -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Impl.Dsa.Generation.Layout

theorem ParameterABI.frameBase {s : State} (A : ParameterABI s) :
    A.geometry.frameBase = (s.gpr .esp).setWidth 64 - 164#64 := by
  change (s.gpr .esp - 164#32).setWidth 64 = _
  exact Taint.sub_setWidth (by have := A.stackLow; omega)

theorem ParameterABI.frameSub {s : State} (A : ParameterABI s) :
    Region.Sub ⟨A.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩
      ⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ := by
  rw [A.frameBase, Offset.sub_ofNat_eq _ (a := 164) (b := 292) (by decide)]
  exact Offset.sub_base _ (by decide)

theorem ParameterABI.stackSub {s : State} (A : ParameterABI s) :
    Region.Sub ⟨A.geometry.frameBase - 128#64, 128⟩
      ⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ := by
  rw [A.frameBase, BitVec.sub_sub]
  change Region.Sub ⟨(s.gpr .esp).setWidth 64 - 292#64, 128⟩ _
  simpa only [BitVec.add_zero] using
    (Offset.sub_base ((s.gpr .esp).setWidth 64 - 292#64) (d := 0) (n := 128) (k := 292) (by decide))

theorem ParameterABI.arenaSub {s : State} (A : ParameterABI s) :
    Region.Sub ⟨A.geometry.base, usedBytes A.geometry.pLen⟩ (argRegion s 10 ((arg s 11).toNat * 8)) := by
  change Region.Sub ⟨argumentPointer s 10, usedBytes (arg s 2).toNat⟩ _
  simpa only [BitVec.add_zero] using
    (Offset.sub_base (argumentPointer s 10) (d := 0) (n := usedBytes (arg s 2).toNat)
      (k := (arg s 11).toNat * 8) (by simpa using A.arenaRoom))

def ParameterABI.tape {s : State} (A : ParameterABI s) (j len : Nat)
    (fit : (arg s j).toNat + len ≤ 2 ^ 32) (small : len < 2 ^ 32)
    (arena : (argRegion s j len).Disjoint (argRegion s 10 ((arg s 11).toNat * 8)))
    (stack : (⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ : Region).Disjoint (argRegion s j len)) :
    GenerationTape A.geometry where
  pointer := arg s j
  bytes := Spec.Rsa.bytesAt s.mem (argumentPointer s j) len
  size := by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using small
  fit := by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using fit
  arena := by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using arena.sub_right A.arenaSub
  frame := by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using stack.symm.sub_right A.frameSub
  stack := by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using stack.symm.sub_right A.stackSub

def ParameterABI.seeds {s : State} (A : ParameterABI s) : GenerationTape A.geometry :=
  A.tape 4 (arg s 5).toNat A.seedsBound (arg s 5).isLt A.seedsScratch A.stackSeeds

def ParameterABI.hs {s : State} (A : ParameterABI s) : GenerationTape A.geometry :=
  A.tape 6 (arg s 7).toNat A.hsBound (arg s 7).isLt A.hsScratch A.stackHs

def ParameterABI.witnesses {s : State} (A : ParameterABI s) : GenerationTape A.geometry :=
  A.tape 8 (arg s 9).toNat A.witnessesBound (arg s 9).isLt A.witnessesScratch A.stackWitnesses
end VG.Proof.Dsa.X86.Generation
