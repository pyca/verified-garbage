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

end VG.Proof.MillerRabin.X86
