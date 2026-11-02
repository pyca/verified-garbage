module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState

/-! Import the generator and reuse shared Montgomery initialization for the first two entries. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

private theorem operand (a : Nat) (ha : a=0 ∨ a=4) : Operand a := by
  rcases ha with rfl|rfl <;> simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]

theorem initialValues_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32}
    (h : Memory p sp s) (modulus : numAt s.mem (State.addr p.base) p.w 0=p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P) (odd : p.P%2=1) :
    WP isa (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32)
      (VG.Impl.Bignum.Arm.SharedWindow.init (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s
      fun t => Memory p sp t ∧ ExpState p.base p.len p.w p.P p.G 0 t ∧
        Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok s 1 56 32 h.context (by decide) (by decide) (by decide) h.ready
    (by decide) (by decide) h.context.gBytes (by rw [p.gLength]; have := p.minLength; omega)
    (by rw [p.gLength]; exact p.width.2.2.2.1) (by change BitVec.ofNat 32 p.k=_; rw [p.gLength])) ?_
  rintro u ⟨_contextU,readyU,generator,keeps,frameU,restU⟩
  have frameU' : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem u.mem :=
    frameU.mono (by simp)
  have memU := h.after_arithmetic readyU frameU' restU
  have fits : arrAt p.w 8≤8*p.len := h.ready.width ▸ h.ready.layout.2.2.1
  have modulusU := (keeps_array_num keeps fits (operand 0 (by simp)) (by decide)).trans modulus
  have r2U := (keeps_array_num keeps fits (operand 4 (by simp)) (by decide)).trans r2
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have callU : TwoExp.CallReady p.base sp p.len u := ⟨memU.calls.stack,memU.fixed⟩
  have r2bound : numAt u.mem (State.addr p.base) p.w 4<p.P := by
    rw [r2U]
    exact Nat.mod_lt _ (by rw [← modulusU]; have := readyU.modulus; omega)
  have r2value : numAt u.mem (State.addr p.base) p.w 4%p.P=2^(64*p.w)*2^(64*p.w)%p.P := by
    rw [r2U,Nat.mod_mod,← Nat.pow_add,show 64*p.w+64*p.w=128*p.w by omega]
  refine WP.mono (sharedWindowInit_ok K u readyU callU modulusU odd generator r2bound r2value) ?_
  rintro t ⟨exp,_headers,_call,frameT,restT⟩
  have localFrame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA u.sp 48] u.mem t.mem := by
    simpa only [K,← memU.fixed] using frameT
  have memT := memU.after_arithmetic exp.ready localFrame restT
  refine ⟨memT,exp,frameU'.trans ?_,restU.trans restT⟩
  simpa only [restU.sp] using localFrame

end VG.Proof.Ffdh.Arm.CombBuilder
