module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptInput
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateNative
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The native cached attempt implements the exact reviewed ABI postcondition. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem keyStatus_lt_four (a : Spec.Ffdh.Parameters) (x : Nat) : Spec.Ffdh.keyStatus a x<4 :=by
 unfold Spec.Ffdh.keyStatus
 split
 · decide
 · split <;>decide

theorem attempt_correct (M : Mont) {s : State} (pre : attemptPre s) :
 WP isa (Generate.code M.mm) s fun t =>abiPreserved s t ∧ attemptPost s t :=by
 let g:=attempt_geometry pre
 let q:=attemptFront s g
 have ns:=attempt_native_state g
 refine WP.mono (generateNative_ok M ns.scratch q.body.scalar.words q.body.scalar.positive q.body.scalar.size
  q.body.scalar.shape q.body.scalar.domLength q.checked q.body.scalar.modulus q.generator q.policy q.body.table
  ns.view ns.domainSource ns.randomSource ns.rbLength ns.xArg ns.yArg ns.domArg ns.dlArg ns.lenArg ns.randArg
  ns.readB ns.readCtx ns.stackB ns.stackCtx q.body.bitsPositive q.body.bitsBound q.body.width
  g.writeX g.writeY g.outsideX g.outsideY g.separateRand g.separateDomain g.separateContext g.separateOutputs) ?_
 rintro t ⟨status,outputs,rest⟩
 refine ⟨abiPreserved_of_keep rest,?_,outputs⟩
 change t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s)) at status
 change ((t.gpr .x0).setWidth 32).toNat=Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s)
 rw [status]
 exact VG.Proof.Ffdh.AArch64.setWidth32_ofNat (Nat.lt_trans (keyStatus_lt_four _ _) (by decide))

/-- Callable form used by the verified rejection controller. -/
theorem attempt_callable (M : Mont) (s : State) (pre : attemptContract.pre s) :
 ∃trace t,Exec isa (Generate.code M.mm) s trace t ∧ abiPreserved s t ∧ attemptContract.post s t :=by
 obtain ⟨trace,t,run,preserved,post⟩:=attempt_correct M pre
 exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.Cached
