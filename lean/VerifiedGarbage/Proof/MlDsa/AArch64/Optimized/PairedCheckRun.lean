import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckStep

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

structure CheckReady (hint : Bool) (s : State) : Prop where
  q : ∀e<4,vword (s.v .v31) e=8380417#32
  bias : ∀e<4,vword (s.v .v8) e=4194304#32
  neg : hint=true → ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e
  zero : hint=true → ∀e<4,vword (s.v .v13) e=0

theorem CheckReady.frame {hint : Bool} {s t : State} (h : CheckReady hint s)
    (hf : StepFrame checkRegs s t) : CheckReady hint t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v12 (by decide),hf.vec .v11 (by decide)]; exact h.neg
  · rw [hf.vec .v13 (by decide)]; exact h.zero

theorem constantsAt_frame {s t : State} (hf : StepFrame checkRegs s t) : constantsAt t=constantsAt s := by
  unfold constantsAt
  rw [hf.vec .v11 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem Banks.checkFrame {s t : State} {v : Values} (h : Banks s v) (hf : StepFrame checkRegs s t) : Banks t v := by
  intro p j
  rw [hf.vec _ ((show ∀p:Fin 2,∀j:Fin 8,(bankRegs p)[j.val]∉checkRegs by decide) p j)]
  exact h p j

def checkRunCode (hint : Bool) (js : List (Fin 2 × Fin 8)) : List Instr :=
  js.flatMap fun (p,j) => checkCode hint (bankRegs p)[j.val] (1024*p.val+128*j.val)

theorem checkRun_ok (hint : Bool) (js : List (Fin 2 × Fin 8))
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : Banks s v) (hc : CheckReady hint s)
    (hr : ∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (k : ∀t,StepFrame checkRegs s t →
      dataAt t=checkRun hint v (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) js →
      WP isa (.block rest) t Q) :
    WP isa (.block (checkRunCode hint js++rest)) s Q := by
  induction js generalizing s with
  | nil => exact k s ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ rfl
  | cons op js ih =>
    simp only [checkRunCode,List.flatMap_cons,List.append_assoc]
    have hn : (bankRegs op.1)[op.2.val]≠.v27 :=
      (show ∀p:Fin 2,∀j:Fin 8,(bankRegs p)[j.val]≠.v27 by decide) op.1 op.2
    refine checkStep_ok hint _ hn (by constructor <;> omega)
      (hr op.1 op.2).1 (hr op.1 op.2).2.1 (hr op.1 op.2).2.2
      hc.q hc.bias hc.neg hc.zero fun a ha hda => ?_
    refine ih (hv.checkFrame ha) (hc.frame ha) ?_ fun t ht hdt => ?_
    · simpa only [ha.rd,ha.wr,ha.gpr] using hr
    · refine k t ((ha.trans ht).mono (by simp)) ?_
      rw [hdt,ha.gpr,constantsAt_frame ha,hda,hv op.1 op.2]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
