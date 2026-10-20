module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The public value being stripped determines every factor-loop decision -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

structure FactorPublic where
  base : Addr
  size : Nat
  value : Nat
  count : Nat

def FactorAt (n : Nat) (p : FactorPublic) (s : State) : Prop :=
  Scr s p.base p.size ∧ 0 < p.value ∧ p.value % 2 = 0 ∧
    slot n 8 + 8 * n ≤ p.size ∧ val32 s.mem p.base (slot n 8) (2 * n) = p.value ∧
    s.gpr .ebx = BitVec.ofNat 32 p.count

def FactorScratchAt (p : FactorPublic) (s : State) : Prop := Scr s p.base p.size
end VG.Proof.Dsa.X86.Generation
