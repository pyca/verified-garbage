module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.InvChoice
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch

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
  obtain ⟨a,al,aw,arg⟩ := h.ws.lenArg
  change kw a=kw len at aw
  unfold VG.Impl.Rsa.X86.InvBatch.choose
  refine WP.seq (WP.mono (invCompare_ok h arg dl) fun u ⟨hu,ku,mu,zu,cu⟩ => ?_)
  refine WP.mono (Q:=InvPost base size len P Q u) (WP.ite (decide (BitVec.ofNat 32 a=BitVec.ofNat 32 desired)) zu ?_ ?_)
    fun t post => post.pre_rest ku (by decide) mu
  · intro yes
    have e := congrArg BitVec.toNat (of_decide_eq_true yes)
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt dl] at e
    have width : kw len=w := by rw [←aw,e,widthChoice]
    refine WP.seq (WP.mono (invCompare_ok hu hu.gate.pArg (by omega : 4*n+1<2^32)) fun v ⟨hv,kv,mv,zv,cv⟩ => ?_)
    refine WP.mono (Q:=InvPost base size len P Q v) (WP.ite (decide ((args 9).toNat<4*n+1)) cv ?_ ?_) fun t post => post.pre_rest kv (by decide) mv
    · intro py
      have pb : (args 9).toNat≤4*n := by have := of_decide_eq_true py; omega
      refine WP.seq (WP.mono (invCompare_ok hv hv.gate.qArg (by omega : 4*n+1<2^32)) fun z ⟨hz,kz,mz,zz,cz⟩ => ?_)
      refine WP.mono (Q:=InvPost base size len P Q z) (WP.ite (decide ((args 11).toNat<4*n+1)) cz ?_ ?_) fun t post => post.pre_rest kz (by decide) mz
      · intro qy
        exact inverseBody_ok hz hn nl hw he width pb (by have := of_decide_eq_true qy; omega)
      · intro _; exact other z hz
    · intro _; exact other v hv
  · intro _; exact other u hu

 theorem inverseDispatch_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa (VG.Impl.Rsa.X86.InvBatch.dispatch (VG.Impl.Rsa.X86.KeyRt.inverse lay)) s
      (InvPost base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.InvBatch.dispatch
  exact inverseChoose_ok h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun u hu =>
    inverseChoose_ok hu (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun v hv =>
      inverseChoose_ok hv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun z hz => inverseFallback_ok hz

end VG.Proof.Rsa.X86.CrtValuesRt
