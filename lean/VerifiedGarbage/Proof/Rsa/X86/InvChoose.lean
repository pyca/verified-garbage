module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.InvChoice
import VerifiedGarbage.Proof.Rsa.X86.InvGuard
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
import Mathlib.Util.CompileInductive

/-! # Correct selection and fallback for the three public RSA widths -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)

 theorem inverseChoose_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q desired w n : Nat} {s : State} {fallback : Prog isa}
    (h : InvInput args base size len P Q s) (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0)
    (dl : desired<2^32) (widthChoice : kw desired=w)
    (other : ∀ u,InvInput args base size len P Q u → WP isa fallback u (InvPost base size len P Q u)) :
    WP isa (VG.Impl.Rsa.X86.InvBatch.choose desired w n fallback) s (InvPost base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.InvBatch.choose
  refine WP.seq (WP.mono (guard_ok h dl nl) fun u g => ?_)
  refine WP.mono (Q:=InvPost base size len P Q u)
    (WP.ite (decide (Eligible args desired n)) g.cf ?_ ?_)
    fun t post => post.pre_rest g.keeps (by decide) g.mem
  · intro yes
    obtain ⟨length,pb,qb⟩ := of_decide_eq_true yes
    obtain ⟨a,al,aw,arg⟩ := g.input.ws.lenArg
    change kw a=kw len at aw
    have eq : BitVec.ofNat 32 a=BitVec.ofNat 32 desired :=
      (Option.some.inj (arg.readSrc.symm.trans g.input.gate.nArg.readSrc)).trans length
    have ae := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt dl] at ae
    have width : kw len=w := by rw [←aw,ae,widthChoice]
    exact inverseBody_ok g.input hn nl hw he width (by omega) (by omega)
  · intro _; exact other u g.input

omit rsaBatchLaw in
 theorem inverseDispatch_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.CrtValuesRt.inverseChoice s (InvPost base size len P Q s) :=
  inverseFallback_ok h

end VG.Proof.Rsa.X86.CrtValuesRt
