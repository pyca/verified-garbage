module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryRegions
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryInitialize
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext

/-! # Instantiate the search plan directly from the external arguments -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def ParameterABI.plan {s : State} (A : ParameterABI s) (W : Nat → BitVec 32) : SearchContextPlan where
  geometry := A.geometry
  seeds := A.seeds
  hs := A.hs
  witnesses := A.witnesses
  saved := initialWords (arg s) W
  wrapped := rfl
  hashesValue := rfl
  parent := rfl
  seedPointer := rfl
  seedLength := by simp only [ParameterABI.seeds, ParameterABI.tape, Spec.Rsa.bytesAt,
    List.length_map, List.length_range, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  hPointer := rfl
  hLength := by simp only [ParameterABI.hs, ParameterABI.tape, Spec.Rsa.bytesAt,
    List.length_map, List.length_range, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  witnessPointer := rfl
  witnessLength := by simp only [ParameterABI.witnesses, ParameterABI.tape, Spec.Rsa.bytesAt,
    List.length_map, List.length_range, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  hashPointer := rfl
  pLength := by simp only [ParameterABI.geometry, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  qLength := by simp only [ParameterABI.geometry, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
end VG.Proof.Dsa.X86.Generation
