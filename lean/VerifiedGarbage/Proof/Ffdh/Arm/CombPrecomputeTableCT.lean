module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableLoopCT
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableInit
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControlCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasisStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialStore

/-! Public basis and subset loops construct every canonical context entry. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

private structure InitialDone (p : Inputs) (sp : BitVec 32) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p 1 s
  table : TablePrefix p 2 s.mem

theorem table_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} (odd : p.P%2=1)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p)) (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.table (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have initial (s : State) (h : InitialInput p sp s) :
      WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.initial (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
        (InitialDone p sp) := by
    refine WP.mono (initial_ok backend s h.1 h.2.1 h.2.2 odd) ?_
    rintro t ⟨memory,table,value,one,modulus,r2,_,_,_⟩
    refine ⟨⟨memory,modulus,odd,r2,one⟩,?_,table⟩
    change _ = _
    rw [value,entryValue]
    have e := VG.Proof.Rsa.FixedBaseComb.exponent_tooth (bits p) 0 (by decide)
    simpa only [Nat.pow_zero,Nat.zero_mul] using congrArg
      (fun E => Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P) e
  have initialized (s : State) (h : InitialDone p sp s) :
      WP isa (.block [.mov .r3 (.imm 2),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 36]) s
        (BasisInput p sp 1) := by
    refine WP.mono (tableInit_state s h.core h.power) ?_
    rintro t ⟨core,power,saved,frame,_⟩
    have ctx := h.core.memory.controlContextEq (by decide) frame
    have table : TablePrefix p 2 t.mem := by
      intro digit hd
      rw [ctx.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega))]
      exact h.table digit hd
    exact ⟨core,by simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using power,table,saved⟩
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.table
  exact relCT_chain (initial_ct backend odd) initial initial
    (relCT_chain ((controlInit_ct 2 36).mono (fun _ _ h => h.2.2) (fun _ _ h => h)) initialized initialized
      (tableLoop_ct backend (by decide : 0<1) (by decide : 1<5) positive fits))

end VG.Proof.Ffdh.Arm.CombBuilder
