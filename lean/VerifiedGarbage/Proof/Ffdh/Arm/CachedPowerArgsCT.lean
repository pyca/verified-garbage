module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerArgs
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerLoad
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
meta import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! Context metadata is read only through public pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem metadataSave_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0 ∧ s.gpr .r4=t.gpr .r4)
    (.seq (.block VG.Impl.Ffdh.Arm.CachedPower.metadata) (.block VG.Impl.Ffdh.Arm.CachedPower.save)) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0,.r4]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact h.1
  · exact h.2

theorem args_ct {p : Inputs} {l : ScalarLayout p} {slots : List Nat} (h52 : 52∈slots) :
    RelCT isa (fun s t => (SampleContext p l slots s ∧ ArithmeticReady p.base p.len p.w s) ∧
      (SampleContext p l slots t ∧ ArithmeticReady p.base p.len p.w t) ∧ s.sp=t.sp)
      VG.Impl.Ffdh.Arm.CachedPower.args (fun _ _ => True) := by
  let Loaded := fun s : State => ArithmeticReady p.base p.len p.w s ∧ s.gpr .r4=p.cachedContext
  have loadWP (s : State) (h : SampleContext p l slots s ∧ ArithmeticReady p.base p.len p.w s) :
      WP isa (.block VG.Impl.Ffdh.Arm.CachedPower.load) s Loaded := by
    refine WP.mono (load_ok s h.1 h52) ?_
    rintro t ⟨⟨_,_,pointer,mem⟩,rest⟩
    exact ⟨h.2.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.2.ptr),pointer⟩
  have controlsWP (s : State) (h : Loaded s) :
      WP isa (.block VG.Impl.Bignum.Arm.expControls) s Loaded := by
    refine WP.mono (expControls_ok s h.1) ?_
    rintro t ⟨ready,_,_,_,_,rest⟩
    exact ⟨ready,(rest.gpr .r4 (by simp)).trans h.2⟩
  unfold VG.Impl.Ffdh.Arm.CachedPower.args
  refine relCT_chain
    ((stackLoads_ct [(.r1,16),(.r2,20),(.r4,52)]).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    loadWP loadWP ?_
  exact relCT_chain
    (expControls_ct.mono (fun _ _ h => h.1.1.ptr.trans h.2.1.1.ptr.symm) (fun _ _ h => h))
    controlsWP controlsWP
    (metadataSave_ct.mono (fun _ _ h => ⟨h.1.1.ptr.trans h.2.1.1.ptr.symm,h.1.2.trans h.2.1.2.symm⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.CachedPower
