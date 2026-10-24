module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordEnv
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyMath
import VerifiedGarbage.Proof.Framework.Omega

/-! The public table traversal implements the same reviewed exact-domain rule as ARMv7. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def PolicyTableAt (B p : Addr) : List Policy.Group → State → Prop
 | [],_ => True
 | g::gs,s => PolicyRecordAt B p g s ∧ PolicyTableAt B (off p (8+3*g.len)) gs s

theorem PolicyTableAt.after_mem {B p : Addr} {gs : List Policy.Group} {s t : State} {rs : List Reg}
 (h : PolicyTableAt B p gs s) (mem : t.mem=s.mem) (rest : Keep rs s t) : PolicyTableAt B p gs t := by
 induction gs generalizing p with
 | nil => trivial
 | cons g gs ih => exact ⟨h.1.after_mem mem rest,ih h.2⟩

def policyWidth (N k : Nat) (dom : List Byte) : List Policy.Group → Nat
 | [] => N
 | g::gs => if k=g.len ∧ dom=g.domain.take dom.length then min N g.bits else policyWidth N k dom gs

theorem policyWidth_rule (N k : Nat) (dom : List Byte) (gs : List Policy.Group)
 (positive : ∀ g∈gs,0<g.bits) :
 policyWidth N k dom gs=
  let cap := VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList gs k dom
  if cap=0 then N else min N cap := by
 induction gs with
 | nil => rfl
 | cons g gs ih =>
   simp only [policyWidth,VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList]
   change (if k=g.len ∧ dom=g.domain.take dom.length then min N g.bits else policyWidth N k dom gs)=
    (if (if g.len=k ∧ dom=g.domain.take dom.length then g.bits else
     VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList gs k dom)=0 then N else
     min N (if g.len=k ∧ dom=g.domain.take dom.length then g.bits else
     VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList gs k dom))
   by_cases yes : k=g.len ∧ dom=g.domain.take dom.length
   · have reverse : g.len=k ∧ dom=g.domain.take dom.length := ⟨yes.1.symm,yes.2⟩
     rw [ite_eq_left yes,ite_eq_left reverse,ite_eq_right (by have := positive g (by simp);omega)]
   · have no : ¬(g.len=k ∧ dom=g.domain.take dom.length) := fun h => yes ⟨h.1.symm,h.2⟩
     rw [ite_eq_right yes,ite_eq_right no]
     exact ih (fun a ha => positive a (by simp [ha]))

end VG.Proof.Ffdh.AArch64.Cached
