module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Sized
public import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
public import VerifiedGarbage.Proof.Bignum.X86.PublicControls
public import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
public import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # The room for the calls of public RSA at a run-time width

The room for the multiplications' calls below `esp` (`Room`), which the
contract's 96 bytes of stack give.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicContext
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What the calls need beyond `PublicInputs`. -/
structure Room (base : Addr) (bytes : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  hbase : (args 8).toNat = base.toNat
  hbytes : bytes = (args 9).toNat * 8
  room : CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32

theorem Room.keep {base : Addr} {bytes : Nat} {args : Nat → BitVec 32} {s t : State} (X : Room base bytes args s)
    {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) : Room base bytes args t :=
  ⟨X.hbase, X.hbytes, by rw [K.1 _ sp]; exact X.room, by rw [K.1 _ sp]; exact X.top⟩

end VG.Proof.Bignum.X86.PublicRt
