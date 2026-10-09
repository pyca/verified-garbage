import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskTail
import VerifiedGarbage.Spec.MlDsa.CommitTail

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)

def hashReads (p : Params) (s : State) : List Region :=
  [⟨pa s (.x26,0),64⟩,⟨pa s (sc oW1),p.k*w1Len p⟩,⟨pa s (sc oMS),64⟩]
def hashWrites (p : Params) (s : State) : List Region :=
  [⟨pa s (sc oCT),cLen p⟩,⟨pa s t1P,2048⟩,⟨pa s t4P,1024⟩]

theorem hash_pre {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) {S : Nat} {s s1 : State}
    (L : Lay S (sgR p) (sgW p) s) (h1 : Args (hashArgs p) s s1) :
    (commitTailContract abi (p.k*w1Len p) (cLen p) S).pre
      (s1.callEntry.withRegions (hashReads p s) (hashWrites p s)) := by
  sig_pre [commitTailContract,commitTailSig,AArch64.abi,VG.AArch64.argRegs]
  rw [h1.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
    h1.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
    h1.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
    h1.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
    h1.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.sp h1]
  simp only [hashReads,hashWrites]
  and_intros
  all_goals first
    | with_reducible rfl
    | exact True.intro
    | exact wfP_of (Lay.spS L)
    | exact resv fun _ hr=>by
        rw [stackBelow_mem hr]
        refine conj_cons (L.stkD (p:=(.x26,0)) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oW1) (l:=p.k*w1Len p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oCT) (l:=cLen p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=t1P) (l:=2048) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oMS) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        exact conj_cons (L.stkD (p:=t4P) (l:=1024) (by rcases hp with rfl|rfl <;> decide)) conj_nil
    | exact Lay.disj L (by rcases hp with rfl|rfl <;> decide)
    | exact (Lay.disj L (by rcases hp with rfl|rfl <;> decide)).symm
    | exact Lay.nwp L (by rcases hp with rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.Cached
