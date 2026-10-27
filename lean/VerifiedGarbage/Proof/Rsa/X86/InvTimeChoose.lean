module
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
meta import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
import VerifiedGarbage.Proof.Rsa.X86.InvTimeBody
import VerifiedGarbage.Proof.Rsa.X86.InvTimeCheck
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Rsa.X86.InvTimeCompare
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
import VerifiedGarbage.Proof.Rsa.X86.InvGuard
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.TimeCheck
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
import Mathlib.Util.CompileInductive

/-! # Public guards join before selecting a single inverse path -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.CrtValuesRt VG.Proof.Rsa.X86.KeyRt

theorem guard64_check :
    (VG.Taint.check taint τ (VG.Impl.Rsa.X86.InvBatch.guard 256 32)
      (VG.Taint.hintOf taint τ (VG.Impl.Rsa.X86.InvBatch.guard 256 32))).isSome=true := by taint_decide

theorem guard96_check :
    (VG.Taint.check taint τ (VG.Impl.Rsa.X86.InvBatch.guard 384 48)
      (VG.Taint.hintOf taint τ (VG.Impl.Rsa.X86.InvBatch.guard 384 48))).isSome=true := by taint_decide

theorem guard128_check :
    (VG.Taint.check taint τ (VG.Impl.Rsa.X86.InvBatch.guard 512 64)
      (VG.Taint.hintOf taint τ (VG.Impl.Rsa.X86.InvBatch.guard 512 64))).isSome=true := by taint_decide

variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw

theorem choose_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' desired w n : Nat} {sp : BitVec 32} {fallback : Prog isa}
    (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (small : desired<2^32) (widthChoice : kw desired=w)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (check : (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n)
      hint).isSome=true)
    (guardCheck : (VG.Taint.check taint τ (VG.Impl.Rsa.X86.InvBatch.guard desired n)
      (VG.Taint.hintOf taint τ (VG.Impl.Rsa.X86.InvBatch.guard desired n))).isSome=true)
    (other : RelCT isa (Pair args base size len P Q P' Q' sp) fallback (fun _ _ => True)) :
    RelCT isa (Pair args base size len P Q P' Q' sp) (VG.Impl.Rsa.X86.InvBatch.choose desired w n fallback) (fun _ _ => True) := by
  let F (p q : Nat) (u : State) := InvInput args base size len p q u ∧ Public args base size sp u ∧
    u.cf=some (decide (Eligible args desired n))
  have ready {p q : Nat} {s : State} (h : InvInput args base size len p q s) (pub : Public args base size sp s) :
      WP isa (VG.Impl.Rsa.X86.InvBatch.guard desired n) s (F p q) := by
    refine WP.mono (guard_ok h small nl) fun u g => ⟨g.input,?_,g.cf⟩
    exact pub.keep g.keeps (by decide) (by rw [g.mem]; exact Outside.refl _ _ _ _)
  have trace : RelCT isa (Pair args base size len P Q P' Q' sp)
      (VG.Impl.Rsa.X86.InvBatch.guard desired n) (fun _ _ => True) :=
    (RelCT.taint (A:=taint) τ (fun _ _ h => agree h.1.1.ws.ws.workspace h.2.1.ws.ws.workspace h.1.2 h.2.2)
      guardCheck).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  unfold VG.Impl.Rsa.X86.InvBatch.choose
  refine RelCT.seq ((trace.wp (F₁:=F P Q) (F₂:=F P' Q')
    (fun _ _ h => ⟨ready h.1.1 h.1.2,ready h.2.1 h.2.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine RelCT.ite (fun s t h => by change s.cf=t.cf; rw [h.1.2.2,h.2.2.2]) ?_ ?_
  · intro s t tr ur sf tf ⟨⟨hs,ht⟩,yes⟩ es et
    have good : Eligible args desired n := by
      change s.cf=some true at yes
      rw [hs.2.2] at yes
      exact of_decide_eq_true (Option.some.inj yes)
    have width := publicWidth hs.1
    rw [good.1,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,widthChoice] at width
    exact inverseBody_trace hn nl hw he width.symm (by have := good.2.1; omega) check
      _ _ _ _ _ _ ⟨⟨hs.1,hs.2.1⟩,⟨ht.1,ht.2.1⟩⟩ es et
  · exact other.mono (fun _ _ h => ⟨⟨h.1.1.1,h.1.1.2.1⟩,⟨h.1.2.1,h.1.2.2.1⟩⟩) (fun _ _ _ => trivial)

omit rsaBatchLaw in
theorem dispatch_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' : Nat} {sp : BitVec 32} :
    RelCT isa (Pair args base size len P Q P' Q' sp) VG.Impl.Rsa.X86.CrtValuesRt.inverseChoice (fun _ _ => True) := by
  exact (RelCT.taint (A:=sseTaint) τ (fun _ _ h => agree h.1.1.ws.ws.workspace h.2.1.ws.ws.workspace h.1.2 h.2.2) fallback_check.choose_spec).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Rsa.X86.InvTiming
