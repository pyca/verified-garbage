module
public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch
import VerifiedGarbage.Proof.Rsa.X86.InvChoice
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # Joining public guards before the single inverse fallback -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

def Eligible (args : Nat → BitVec 32) (desired n : Nat) : Prop :=
  args 7=BitVec.ofNat 32 desired ∧ (args 9).toNat<4*n+1 ∧ (args 11).toNat<4*n+1
instance (args : Nat → BitVec 32) (desired n : Nat) : Decidable (Eligible args desired n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

structure Guarded (args : Nat → BitVec 32) (base : Addr) (size len P Q desired n : Nat)
    (s t : State) : Prop where
  input : InvInput args base size len P Q t
  keeps : Keeps [.eax] s t
  mem : t.mem=s.mem
  cf : t.cf=some (decide (Eligible args desired n))

theorem reject_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.InvBatch.reject s fun t =>
      InvInput args base size len P Q t ∧ Keeps [.eax] s t ∧ t.mem=s.mem ∧ t.cf=some false := by
  refine cmpBoth rfl fun t T _ cf => WP.block_nil ?_
  have K : Keeps [.eax] s t := T.keeps _
  exact ⟨h.rest K (by decide) (by decide) T.mem,K,T.mem,by simpa using cf⟩

theorem guard_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q desired n : Nat} {s : State}
    (h : InvInput args base size len P Q s) (small : desired<2^32) (nl : n≤1024) :
    WP isa (VG.Impl.Rsa.X86.InvBatch.guard desired n) s (Guarded args base size len P Q desired n s) := by
  unfold VG.Impl.Rsa.X86.InvBatch.guard
  refine WP.seq (WP.mono (invCompare_ok h h.gate.nArg small) fun u ⟨hu,ku,mu,zu,_⟩ => ?_)
  refine WP.ite (decide (args 7=BitVec.ofNat 32 desired)) zu ?_ ?_
  · intro yes
    have eq := of_decide_eq_true yes
    refine WP.seq (WP.mono (invCompare_ok hu hu.gate.pArg (by omega : 4*n+1<2^32)) fun v ⟨hv,kv,mv,_,cv⟩ => ?_)
    refine WP.ite (decide ((args 9).toNat<4*n+1)) cv ?_ ?_
    · intro py
      refine WP.mono (invCompare_ok hv hv.gate.qArg (by omega : 4*n+1<2^32)) fun z ⟨hz,kz,mz,_,cz⟩ => ?_
      refine ⟨hz,(ku.trans kv).trans kz,mz.trans (mv.trans mu),?_⟩
      simpa only [Eligible,eq,true_and,of_decide_eq_true py] using cz
    · intro py
      refine WP.mono (reject_ok hv) fun z ⟨hz,kz,mz,cz⟩ => ?_
      refine ⟨hz,(ku.trans kv).trans kz,mz.trans (mv.trans mu),?_⟩
      simpa only [Eligible,of_decide_eq_false py,and_false,false_and,decide_false] using cz
  · intro no
    refine WP.mono (reject_ok hu) fun z ⟨hz,kz,mz,cz⟩ => ?_
    refine ⟨hz,ku.trans kz,mz.trans mu,?_⟩
    simpa only [Eligible,of_decide_eq_false no,false_and,decide_false] using cz

end VG.Proof.Rsa.X86.CrtValuesRt
