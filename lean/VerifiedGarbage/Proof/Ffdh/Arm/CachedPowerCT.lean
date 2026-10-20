module

import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPowerLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerPersistent
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackendTiming
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
import VerifiedGarbage.Proof.Bignum.Arm.CombExpPhaseCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerArgs
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound

/-! Cached native exponentiation hides independent sampled scalars. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm

private structure NativeInput (p : Inputs) (slots : List Nat) (eb : List Byte) (sp : BitVec 32)
    (s : State) : Prop where
  input : SamplePowerInput p (ScalarLayout.vetted p) slots eb s
  calls : KeyCallMemory p s
  cached : CachedGenerationContext p s
  sameSp : s.sp=sp

theorem code_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (_stable : stableSlots slots=true) (h52 : 52∈slots) (_h56 : 56∈slots) (_h32 : 32∈slots)
    (size1 : eb1.length=(ScalarLayout.vetted p).width) (size2 : eb2.length=(ScalarLayout.vetted p).width)
    (fit1 : Spec.Rsa.os2ip eb1<2^Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (fit2 : Spec.Rsa.os2ip eb2<2^Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (odd : p.P%2=1) :
    RelCT isa (fun s t => ((SamplePowerInput p (ScalarLayout.vetted p) slots eb1 s ∧ KeyCallMemory p s) ∧
        cachedGenerationEnvironment.holds p s) ∧
      ((SamplePowerInput p (ScalarLayout.vetted p) slots eb2 t ∧ KeyCallMemory p t) ∧
        cachedGenerationEnvironment.holds p t) ∧ cachedGenerationEnvironment.publicRel s t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CachedPower.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  have family (sp0 : BitVec 32) : RelCT isa (fun s t => NativeInput p slots eb1 sp0 s ∧
      NativeInput p slots eb2 sp0 t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CachedPower.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    let l := ScalarLayout.vetted p
    have positiveBits : 0<bits p := CachedSample.bits_positive h.1.cached
    have boundBits : bits p≤8192 := CachedSample.bits_bound p
    have publicWidth : l.width=(bits p+7)/8 := CachedSample.layout_width p positiveBits
    have widthBound : bits p≤8*l.width := by omega
    have widthFit : bits p<2^31 := by omega
    have bytesFit : l.width<2^32 := by
      have := l.width_bounds.2
      have := p.maxLength
      omega
    have scheduleFit := (VG.Proof.Rsa.FixedBaseComb.rows_small boundBits).2
    let K1 := CombExp.kernelAt backend p.base l.start (table p) sp0 p.len p.w l.width p.P p.G (bits p)
      eb1 size1 widthBound bytesFit scheduleFit widthFit fit1
    let K2 := CombExp.kernelAt backend p.base l.start (table p) sp0 p.len p.w l.width p.P p.G (bits p)
      eb2 size2 widthBound bytesFit scheduleFit widthFit fit2
    have timing : CombExp.Timing K1 K2 := CombExp.backendTiming backend p.base l.start (table p) sp0
      p.len p.w l.width p.P p.G (bits p) eb1 eb2 size1 size2 widthBound bytesFit scheduleFit widthFit fit1 fit2
    have argsReady (eb : List Byte) (size : eb.length=l.width) (a : State) (input : NativeInput p slots eb sp0 a) :
        WP isa VG.Impl.Ffdh.Arm.CachedPower.args a
          (CombExp.PhaseInput p.base l.start (table p) p.len p.w l.width (bits p) p.P
            (CombExp.Persistent p.base l.start (table p) sp0 p.len p.w p.P p.G (bits p) eb)) := by
      let A := CombExp.arithmetic backend p.base l.start (table p) sp0 p.len p.w p.P p.G (bits p) eb
      have hp := persistent input.cached input.calls input.input.exponent size input.sameSp
      refine WP.mono (args_ok a input.input.context input.cached input.input.ready h52) ?_
      rintro b ⟨ready,controls,arrays,frame,rest⟩
      exact ⟨ready,A.stable frame rest hp,controls,(arrays 0 (by decide)).trans input.input.modulus,
        (arrays 4 (by decide)).trans input.input.r2⟩
    have programCT := relCT_chain
      ((args_ct h52).mono
        (fun _ _ h => ⟨⟨h.1.input.context,h.1.input.ready⟩,⟨h.2.1.input.context,h.2.1.input.ready⟩,h.2.2⟩)
        (fun _ _ h => h))
      (fun a input => argsReady eb1 size1 a input)
      (fun a input => argsReady eb2 size2 a input)
      (CombExp.phase_ct K1 K2 timing odd (VG.Proof.Rsa.FixedBaseComb.rows_pos positiveBits) (by omega))
    exact programCT s t tr1 tr2 u v h e1 e2
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1.1,h.1.1.2,h.1.2,rfl⟩,⟨h.2.1.1.1,h.2.1.1.2,h.2.1.2,h.2.2.2.symm⟩,h.2.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm.CachedPower
