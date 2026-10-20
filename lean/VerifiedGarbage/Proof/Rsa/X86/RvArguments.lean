module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame

/-! # Public cdecl arguments remain available throughout recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (stackAddress)
open VG.Impl.Rsa.X86.Keys

theorem KS.argument {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) {i : Nat} {v : BitVec 32}
    (arg : CallArgument s0 g.B g.Z i v) (apart : ∀ r ∈ stageR g, Region.Disjoint ⟨stackAddress s0 i, 4⟩ r) :
    CallArgument s g.B g.Z i v :=
  arg.frame h.rest (by decide) h.frame apart

end VG.Proof.Rsa.X86.Recover
