module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.InvChoice
import VerifiedGarbage.Proof.Rsa.X86.InvGuard
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch

/-! # Correct selection and fallback for the three public RSA widths -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)

 theorem inverseDispatch_ok [VG.Proof.Rsa.X86.BatchLaw] {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.dispatch lay (VG.Impl.Rsa.X86.KeyRt.inverse lay)) s
      (InvPost base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.dispatch
  refine WP.seq (WP.mono (guard_ok h) fun u g => ?_)
  refine WP.mono (Q := InvPost base size len P Q u)
    (WP.ite (decide (Eligible args)) g.cf ?_ ?_)
    fun t post => post.pre_rest g.keeps (by decide) g.mem
  · intro yes
    obtain ⟨m16, big, pb, qb⟩ := of_decide_eq_true yes
    obtain ⟨a, al, aw, arg⟩ := g.input.ws.lenArg
    change kw a = kw len at aw
    have eq : BitVec.ofNat 32 a = args 7 := Option.some.inj (arg.readSrc.symm.trans g.input.gate.nArg.readSrc)
    have ae := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ae
    have nwl : VG.Proof.Rsa.X86.InvBatchRt.nw len = a / 8 := by
      have aw' := aw
      simp only [kw, Spec.Rsa.modulusWords] at aw'
      simp only [VG.Proof.Rsa.X86.InvBatchRt.nw, kw, Spec.Rsa.modulusWords]; omega
    exact inverseBodyRt_ok g.input (by omega) (by omega) (by omega) (by omega)
  · intro _; exact inverseFallback_ok g.input

end VG.Proof.Rsa.X86.CrtValuesRt
