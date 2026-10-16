module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ResumeTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraStepTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64

theorem stepTiming (A B : Spec.Sha3.State) (p a b c : Addr) : StepTiming A B p a b c := by
  intro s u n _ hs hu ss us sp
  exact extraStep_relCT
    ⟨hs.context,hs.ptr,ss,hs.pair,accepted_length A n,accepted_length B n,hs.left,hs.right,hs.saveLeft,hs.saveRight⟩
    ⟨hu.context,hu.ptr,us,hu.pair,accepted_length A n,accepted_length B n,hu.left,hu.right,hu.saveLeft,hu.saveRight⟩ sp

theorem extraPair_relCT {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (ps : Progress A B 3 p a b c s) (pu : Progress A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c) (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u) Impl.MlKem.AArch64.Paired.extraPair
      (fun t v=>ResumePost A B p a b s t ∧ ResumePost A B p a b u v) :=
  resume_relCT (stepTiming A B p a b c) ps pu ss us sp

end VG.Proof.MlKem.AArch64.Paired
