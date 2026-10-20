module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerArgs
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationTable
import VerifiedGarbage.Proof.Bignum.Arm.CombExpChoose
import VerifiedGarbage.Proof.Bignum.Arm.CombExpPhase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerMetadata
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! Cached exponentiation consumes the bounded sampled scalar without changing its buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem significant_below {p : Inputs} {l : ScalarLayout p} {s : State}
    (h : KeyCallMemory p s) :
    Region.Disjoint ⟨State.addr l.start,l.width⟩ (belowA s.sp 48) := by
  have fit := h.privateFits
  have lead := l.lead_lt
  rw [ScalarLayout.start,VG.Arm.addr_add (by omega)]
  exact h.privateValue.sub_left (Offset.sub_base _ (by unfold ScalarLayout.width; omega))

theorem correct (backend : MontBackend) (s : State) {p : Inputs} {l : ScalarLayout p}
    {slots : List Nat} {eb : List Byte}
    (context : SampleContext p l slots s) (cached : CachedGenerationContext p s)
    (calls : KeyCallMemory p s) (stable : stableSlots slots=true) (h52 : 52∈slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0=p.P) (odd : p.P%2=1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P)
    (exponent : Octets p.base l.start p.len eb s) (size : eb.length=l.width)
    (widthBound : bits p≤8*eb.length) (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows (bits p)<2^31)
    (widthFit : bits p<2^31) (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (scalarFit : Spec.Rsa.os2ip eb<2^(bits p))
    (tableSeparate : ∀r∈CombExp.writeRegions p.base s.sp p.len,
      Region.Disjoint ⟨State.addr (table p),32*(8*p.w)⟩ r) :
    WP isa (VG.Impl.Ffdh.Arm.CachedPower.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6=Spec.Rsa.powMod p.G (Spec.Rsa.os2ip eb) p.P ∧
      numAt t.mem (State.addr p.base) p.w 0=p.P ∧
      numAt t.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P ∧
      numAt t.mem (State.addr p.base) p.w 7=1 ∧
      Frame (CombExp.writeRegions p.base s.sp p.len) s.mem t.mem ∧ Rest roundClobbers s t := by
  let K := CombExp.kernel backend p.base l.start (table p) s.sp p.len p.w p.P p.G (bits p) eb
    widthBound (by have := l.width_bounds.2; have := p.maxLength; omega) scheduleFit widthFit scalarFit
  have source : CombDigit.Source l.start eb s := ⟨exponent.fits,exponent.readable,exponent.byte⟩
  have hp : CombExp.Persistent p.base l.start (table p) s.sp p.len p.w p.P p.G (bits p) eb s := by
    refine ⟨⟨calls.stack,rfl⟩,source,cached.table,?_,tableSeparate⟩
    intro r hr
    simp only [CombExp.writeRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact exponent.separate
    · rw [size]; exact significant_below calls
  rw [VG.Impl.Ffdh.Arm.CachedPower.code,WP.seq_iff]
  refine WP.mono (args_ok s context cached ready h52) ?_
  rintro u ⟨readyU,controlsU,arraysU,frameU,restU⟩
  have writes : Frame (CombExp.writeRegions p.base s.sp p.len) s.mem u.mem := frameU.mono (by simp [CombExp.writeRegions])
  have hpU := K.arithmetic.stable frameU restU hp
  have controls : CombExp.Controls p.base l.start (table p) eb.length (bits p) u := by
    rw [size]; exact controlsU
  refine WP.mono (CombExp.phase_ok K u readyU hpU controls
    ((arraysU 0 (by decide)).trans modulus) odd ((arraysU 4 (by decide)).trans r2)
    positive (by omega) scalarFit) ?_
  rintro t ⟨rd,value,m,rr,one,_,_,frameT,restT⟩
  have frame := writes.trans frameT
  have rest := restU.trans restT
  exact ⟨context.toContext.after_call calls frame rest rd.ptr (fun d hd=>(stableSlots_at stable hd).1),
    rd,value,m,rr,one,frame,rest⟩

end VG.Proof.Ffdh.Arm.CachedPower
