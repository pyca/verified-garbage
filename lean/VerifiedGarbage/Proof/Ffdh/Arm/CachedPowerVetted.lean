module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerMetadata
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationTable
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound
import VerifiedGarbage.Proof.Rsa.FixedBaseComb

/-! The reviewed scalar layout supplies the evaluator's public schedule bounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem vetted_correct (backend : MontBackend) (s : State) {p : Inputs}
    {slots : List Nat} {eb : List Byte}
    (context : SampleContext p (ScalarLayout.vetted p) slots s) (cached : CachedGenerationContext p s)
    (calls : KeyCallMemory p s) (stable : stableSlots slots=true) (h52 : 52∈slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0=p.P) (odd : p.P%2=1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P)
    (exponent : Octets p.base (ScalarLayout.vetted p).start p.len eb s)
    (size : eb.length=(ScalarLayout.vetted p).width)
    (scalarFit : Spec.Rsa.os2ip eb<2^(bits p)) :
    WP isa (VG.Impl.Ffdh.Arm.CachedPower.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6=Spec.Rsa.powMod p.G (Spec.Rsa.os2ip eb) p.P ∧
      numAt t.mem (State.addr p.base) p.w 0=p.P ∧
      numAt t.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P ∧
      numAt t.mem (State.addr p.base) p.w 7=1 ∧
      Frame (CombExp.writeRegions p.base s.sp p.len) s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0<bits p := CachedSample.bits_positive cached
  have bound : bits p≤8192 := CachedSample.bits_bound p
  have width : eb.length=(bits p+7)/8 := size.trans (CachedSample.layout_width p positive)
  have small := VG.Proof.Rsa.FixedBaseComb.rows_small bound
  exact correct backend s context cached calls stable h52 ready modulus odd r2 exponent size
    (by omega) small.2 (by omega) (VG.Proof.Rsa.FixedBaseComb.rows_pos positive) scalarFit
    (by
      intro r hr
      apply cached.tableSeparate r
      simp only [CombExp.writeRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [keyCallWrites,keyWrites])

end VG.Proof.Ffdh.Arm.CachedPower
