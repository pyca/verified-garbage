module

public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.RelCT

/-! # Public temporary words in a private RSA workspace

The checker sees a single writable region. Executions in that restricted
view lift to the caller's permissions; determinism gives the same trace.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.WorkspaceTaint
open VG VG.X86 VG.Proof.Mont.X86

 def dom (minimum : Nat) : VG.X86.Taint.T :=
  {regs:=.ofList [.edi,.esp],flags:=false,lens:=[minimum],bases:=[(.edi,0,0)]}

def view (s : State) (base : Addr) (size : Nat) : State :=
  s.withRegions s.rd [⟨base,size⟩]

theorem view_scr {s : State} {base : Addr} {size : Nat} (h : Scr s base size) :
    Scr (view s base size) base size :=
  ⟨h.edi,by simp only [view,State.withRegions_wr,List.mem_singleton],h.nowrap,h.stk⟩

theorem view_wf {s : State} {base : Addr} {size minimum : Nat} (h : Scr s base size) (hm : minimum≤size) :
    VG.X86.Taint.Wf (dom minimum) (view s base size) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro _
    refine ⟨List.Forall₂.cons hm List.Forall₂.nil,?_,?_⟩
    · simp only [view,State.withRegions_wr,List.pairwise_singleton]
    · intro r hr
      simp only [view,State.withRegions_wr,List.mem_singleton] at hr
      subst r
      exact h.nowrap
  · intro p hp
    simp only [dom,List.mem_singleton] at hp
    subst p
    change addr (s.gpr .edi) 0=base
    simpa only [addr,BitVec.add_zero] using h.edi
  · intro p hp
    cases hp
  · intro hp
    change 0<0 at hp
    omega
  · intro p hp
    cases hp
  · change (s.gpr .esp).toNat+0<2^32
    simpa only [Nat.add_zero] using (s.gpr .esp).isLt
  · intro p hp
    cases hp
  · intro hp
    change 0<0 at hp
    omega

theorem view_agree {s t : State} {base : Addr} {size minimum : Nat}
    (hs : Scr s base size) (ht : Scr t base size) (hm : minimum≤size) (sp : s.gpr .esp=t.gpr .esp) :
    VG.X86.Taint.Agree (dom minimum) (view s base size) (view t base size) := by
  refine ⟨⟨?_,fun h => nomatch h⟩,fun _ => rfl,view_wf hs hm,view_wf ht hm,
    VG.X86.Taint.slotsOk_empty,VG.X86.Taint.slotsAgree_empty,?_,?_⟩
  · intro r hr
    simp only [dom,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.edi_toNat.trans ht.edi_toNat.symm)
    · exact sp
  · intro hp
    change 0<0 at hp
    omega
  · intro k _ hk
    change k<0 at hk
    omega

theorem lift_exec {s z : State} {base : Addr} {size : Nat} {c : Prog isa} {tr : List Leak}
    (hs : Scr s base size) (he : Exec isa c (view s base size) tr z) :
    Exec isa c s tr (z.withRegions s.rd s.wr) := by
  have cw : Covers (view s base size).wr s.wr := by
    apply Covers.of_mem
    intro r hr
    simp only [view,State.withRegions_wr,List.mem_singleton] at hr
    subst r
    exact hs.wr
  have cr : Covers ((view s base size).rd++(view s base size).wr) (s.rd++s.wr) :=
    (Covers.refl s.rd).append cw
  have E := VG.X86.Exec.widen he cr cw
  simpa only [view,State.withRegions_withRegions,State.withRegions_self] using E

theorem trace_eq {s t sf tf : State} {base : Addr} {size minimum : Nat} {c : Prog isa} {tr ur : List Leak}
    (hs : Scr s base size) (ht : Scr t base size) (hm : minimum≤size) (sp : s.gpr .esp=t.gpr .esp)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (hc : (VG.Taint.check taint (dom minimum) c hint).isSome=true)
    (left : WP isa c (view s base size) (fun _ => True)) (right : WP isa c (view t base size) (fun _ => True))
    (es : Exec isa c s tr sf) (et : Exec isa c t ur tf) : tr=ur := by
  obtain ⟨a,sa,ea,_⟩ := left
  obtain ⟨b,tb,eb,_⟩ := right
  have H := (VG.RelCT.taint (A:=taint) (dom minimum) (fun _ _ h => h) hc
    _ _ _ _ _ _ (view_agree hs ht hm sp) ea eb).1
  exact (Exec.det (lift_exec hs ea) es).1.symm.trans (H.trans (Exec.det (lift_exec ht eb) et).1)

end VG.Proof.Rsa.X86.WorkspaceTaint
