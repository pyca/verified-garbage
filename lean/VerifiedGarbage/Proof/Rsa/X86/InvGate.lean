module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Mont.Words32
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass

/-! # Public prime lengths and their bounds survive scratch arithmetic -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

 structure InvGate (args : Nat → BitVec 32) (base : Addr) (size P Q : Nat) (s : State) : Prop where
  nArg : CallArgument s base size 7 (args 7)
  pArg : CallArgument s base size 9 (args 9)
  qArg : CallArgument s base size 11 (args 11)
  pBound : P<256^(args 9).toNat
  qBound : Q<256^(args 11).toNat

 theorem InvGate.keep {args : Nat → BitVec 32} {base : Addr} {size P Q : Nat} {s t : State} {regs : List Reg}
    (h : InvGate args base size P Q s) (K : Keeps regs s t) (sp : .esp∉regs)
    (O : Outside base 0 size s.mem t.mem) : InvGate args base size P Q t :=
    ⟨h.nArg.keep K sp O,h.pArg.keep K sp O,h.qArg.keep K sp O,h.pBound,h.qBound⟩

 theorem prime_bound {x bytes n : Nat} (hx : x<256^bytes) (hb : bytes≤4*n) : x<2^(32*n) := by
  have hp : 256^bytes≤256^(4*n) := Nat.pow_le_pow_right (by decide) hb
  have eq : 256^(4*n)=2^(32*n) := by
    change (2^8)^(4*n)=2^(32*n)
    rw [←Nat.pow_mul]; congr 1; omega
  rw [eq] at hp
  omega

 theorem odd_modulus_bound {p n : Nat} (hn : 0<n) (hp : p<2^(32*n)) : 2*(p/2)+1<2^(32*n) := by
  have even : 2^(32*n)%2=0 := by
    rw [show 32*n=(32*n-1)+1 by omega,Nat.pow_succ]
    omega
  omega

 theorem prefix_eq {m : Mem} {base : Addr} {d n w : Nat} (hw : n≤w)
    (small : val32 m base d w<2^(32*n)) : val32 m base d n=val32 m base d w := by
  have split := val32_append m base d n (w-n)
  rw [show n+(w-n)=w by omega] at split
  have high : val32 m base (d+4*n) (w-n)=0 := by
    by_contra h
    have bound := Nat.mul_le_mul_left (2^(32*n)) (show 1≤val32 m base (d+4*n) (w-n) by omega)
    omega
  rw [split,high,Nat.mul_zero,Nat.add_zero]

end VG.Proof.Rsa.X86.CrtValuesRt
