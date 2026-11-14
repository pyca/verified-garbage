module

public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.LaneTaint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

def nativeContract : Contract isa :=
  Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst abi 3456

theorem native_contract_satisfiable : ∃s,nativeContract.pre s := by
  implies_sat [nativeContract,Spec.EcKey.P521.inst,Spec.Ecdh.Instance.exchangeContract,
    Spec.Ecdh.Instance.exchangeSig,Spec.P521.curve,Spec.EcKey.scratchWords,abi,argRegs]
    [VG.Proof.Ecdh.AArch64.P521.satState] using VG.Proof.Ecdh.AArch64.P521.satState

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock000 outerBlock172)

def nativeSavedState (s : State) : State := s.setV .v31 (setLane (s.v .v31) 64 1 (s.gpr .x26))

theorem native_prologue_ok (s : State) : WP isa (.block outerBlock000) s (fun t => t=nativeSavedState s) := by
  change WP isa (.block [.vop (.ins .d2 .v31 1 .x26)]) s _
  apply WP.of_runBlock
  simp only [runBlock_cons,exec_ins (show 1<2 by decide),runStep_some,runBlock_nil,
    Option.some.injEq,exists_eq_left']
  rfl

theorem native_saved_high (s : State) : ((nativeSavedState s).v .v31).extractLsb' 64 64=s.gpr .x26 := by
  simp only [nativeSavedState,RegUpd.v_setV_self]
  have h := LaneTaint.extract_setLane (s.v .v31) (s.gpr .x26) (i:=1) (j:=1) (by decide) (by decide)
  simpa only [Nat.mul_one,ite_true] using h

theorem native_pre_saved {s : State} (h : nativeContract.pre s) : nativeContract.pre (nativeSavedState s) := h

theorem native_post_saved (s t : State) : nativeContract.post (nativeSavedState s) t ↔ nativeContract.post s t := Iff.rfl

theorem native_epilogue_ok (s : State) :
    WP isa (.block outerBlock172) s fun t =>
      t.gpr .x26=(s.v .v31).extractLsb' 64 64 ∧ Keeps [.x26] s t ∧ t.v=s.v := by
  change WP isa (.block [.umov .x .x26 .v31 1]) s _
  apply WP.of_runBlock
  simp only [runBlock_cons,exec_umov (show 1<2 by decide),runStep_some,runBlock_nil,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · simp only [RegUpd.gpr_write_self,BitVec.setWidth_eq]
  · intro r hr
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)
  all_goals rfl

def nativeRestoredState (s : State) : State := s.write .x .x26 (laneOf s .v31 1)

theorem native_prologue_exec (s : State) : Exec isa (.block outerBlock000) s [] (nativeSavedState s) :=
  Exec.block rfl

theorem native_epilogue_exec (s : State) : Exec isa (.block outerBlock172) s [] (nativeRestoredState s) :=
  Exec.block rfl

theorem native_saved_gpr (s : State) : (nativeSavedState s).gpr=s.gpr := rfl
theorem native_saved_mem (s : State) : (nativeSavedState s).mem=s.mem := rfl
theorem native_saved_sp (s : State) : (nativeSavedState s).sp=s.sp := rfl
theorem native_saved_rd (s : State) : (nativeSavedState s).rd=s.rd := rfl
theorem native_saved_wr (s : State) : (nativeSavedState s).wr=s.wr := rfl

end VG.Proof.Weierstrass.AArch64.P521Native
