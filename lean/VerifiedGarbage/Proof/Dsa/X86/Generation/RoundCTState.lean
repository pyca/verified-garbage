module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo

/-! # Public modulus, residue, and remaining squaring count for a primality round -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure RoundPublic where
  base : Addr
  modulus : Nat
  size : Nat
  value : Nat
  count : Nat

def RoundCoreAt (n : Nat) (p : RoundPublic) (s : State) : Prop := RoundReady p.base n p.modulus p.size s

def RoundAt (n : Nat) (p : RoundPublic) (s : State) : Prop :=
  RoundCoreAt n p s ∧ wordsVal s.mem p.base (slot n 6) n = p.value ∧
    s.mem.readW (off p.base roundCount) 32 = BitVec.ofNat 32 p.count ∧ p.count < 2 ^ 32

def RoundComparedAt (n : Nat) (p : RoundPublic) (s : State) : Prop :=
  RoundAt n p s ∧ s.zf = some (decide (¬ (p.value = 1 ∨ p.value = p.modulus - 1)))

def roundSquared (p : RoundPublic) : RoundPublic := {p with value := p.value * p.value % p.modulus}

theorem roundCore_pins (n : Nat) : Pins (RoundCoreAt n) [.edi] := by
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (hs.context.scr.edi_toNat.trans ht.context.scr.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
