module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepare
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareState
import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarArgs
import VerifiedGarbage.Proof.Ffdh.Arm.SampleCut
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound
import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerMetadata
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationTable
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpChooseCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernelAt
import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerArgs
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.SampleSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import Init.Prelude
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateData
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateContractCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateSat
import VerifiedGarbage.Proof.Bignum.Arm.CombExpChoose
import VerifiedGarbage.Proof.Bignum.Arm.CombExpPhase
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Bignum.Arm.CombExp
import VerifiedGarbage.Proof.Bignum.Arm.CombExpControl
import VerifiedGarbage.Proof.Bignum.Arm.CombExpStepCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpLoop
import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
import VerifiedGarbage.Proof.Bignum.Arm.CombExpInitial
import VerifiedGarbage.Proof.Bignum.Arm.CombExpInitialCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerAt
/-! Cached attempts inherit every callable RSA Montgomery backend and caller transform. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyPrograms.lean`, which only this module imported.
section

/-! Cached attempts instantiate one shared callable Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm

def prepare : Prog isa := VG.Impl.Ffdh.Arm.CachedPrepare.code

def sample : Prog isa := VG.Impl.Ffdh.Arm.CachedSample.code

def tail (backend : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.KeyGenerate.tail
    (VG.Impl.Ffdh.Arm.CachedPower.code (MontCall.op backend.name backend.mul))

def code (backend : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample (tail backend)

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPowerCorrect.lean`, which only this module imported.
section

/-! Cached exponentiation consumes the bounded sampled scalar without changing its buffers. -/

section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
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
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombExpLoopCT.lean`, which only this module imported.
section

/-! The public number of remaining comb rows controls every back edge. -/

section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

structure LoopInput (base source table : BitVec 32) (len w bytes N M g x k : Nat)
    (P : State→Prop) (s : State) : Prop where
  power : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x k) s
  persistent : P s
  controls : Controls base source table bytes N s
  counter : Counter base k s

theorem rows_ct {base source table : BitVec 32} {len w bytes N M g x1 x2 count : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2) (ct : Timing K1 K2)
    (positive : 0<count) (bound : count≤Spec.Rsa.FixedBaseComb.rows N) (fits : count<2^32) :
    RelCT isa (fun s t => LoopInput base source table len w bytes N M g x1 count P1 s ∧
      LoopInput base source table len w bytes N M g x2 count P2 t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.CombExp.rows K1.arithmetic.op) (fun _ _ => True) := by
  let I := fun k s t => 0<k ∧ k≤Spec.Rsa.FixedBaseComb.rows N ∧ k<2^32 ∧
    LoopInput base source table len w bytes N M g x1 k P1 s ∧
    LoopInput base source table len w bytes N M g x2 k P2 t ∧ s.sp=t.sp
  have step : ∀ k, RelCT isa (I k) (VG.Impl.Bignum.Arm.CombExp.round K1.arithmetic.op) fun u v =>
      isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
      (isa.eval .ne u=some true → ∃ m<k, I m u v) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨positiveK,boundK,fitsK,left,right,sp⟩ := h
    have successor : k-1+1=k := by omega
    have timing := relCT_keep_sp (round_ct K1 K2 ct (i:=k-1) (by omega)) (fun _ _ h => h.2.2)
    have leftInput : RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x1 (k-1+1)) (k-1) P1 s := by
      simpa only [successor] using (show RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x1 k) (k-1) P1 s from
        ⟨left.power,left.persistent,left.controls,by simpa only [successor] using left.counter⟩)
    have rightInput : RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x2 (k-1+1)) (k-1) P2 t := by
      simpa only [successor] using (show RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x2 k) (k-1) P2 t from
        ⟨right.power,right.persistent,right.controls,by simpa only [successor] using right.counter⟩)
    obtain ⟨trace,sp'⟩ := timing s t tr1 tr2 u v ⟨leftInput,rightInput,sp⟩ e1 e2
    have correct1 := round_ok K1 s (i:=k-1) (by omega) (by omega) leftInput.power leftInput.persistent
      leftInput.controls leftInput.counter
    have correct2 := round_ok K2 t (i:=k-1) (by omega) (by omega) rightInput.power rightInput.persistent
      rightInput.controls rightInput.counter
    rw [←ct.same] at correct2
    obtain ⟨_,_,run1,power1,p1,controls1,counter1,zero1,_,_⟩ := correct1
    obtain ⟨_,_,run2,power2,p2,controls2,counter2,zero2,_,_⟩ := correct2
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [zero1,zero2]
    · intro again
      have nonzero : k-1≠0 := by
        intro zero
        change some (!u.z)=some true at again
        simp only [zero1,zero,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega,by omega,by omega,by omega,
        ⟨power1,p1,controls1,counter1⟩,⟨power2,p2,controls2,counter2⟩,sp'⟩
  unfold VG.Impl.Bignum.Arm.CombExp.rows
  exact (RelCT.loop I step count).mono
    (fun _ _ h => ⟨positive,bound,fits,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm.CombExp
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombExpPhaseCT.lean`, which only this module imported.
section

/-! Cached comb exponentiation reveals the fixed public row count. -/

section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

structure PhaseInput (base source table : BitVec 32) (len w bytes N M : Nat)
    (P : State→Prop) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  persistent : P s
  controls : Controls base source table bytes N s
  modulus : numAt s.mem (State.addr base) w 0=M
  r2 : numAt s.mem (State.addr base) w 4=2^(128*w)%M

private theorem initialInput_ok {base source table : BitVec 32} {len w bytes N M g x : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (odd : M%2=1)
    (s : State) (h : PhaseInput base source table len w bytes N M P s) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.initial K.arithmetic.op) s
      (LoopInput base source table len w bytes N M g x (Spec.Rsa.FixedBaseComb.rows N) P) := by
  refine WP.mono (initial_ok (g:=g) K.arithmetic s h.ready h.persistent h.controls h.modulus odd h.r2) ?_
  rintro t ⟨power,p,controls,counter,_,_⟩
  exact ⟨by simpa only [VG.Proof.Rsa.FixedBaseComb.high_top] using power,p,controls,counter⟩

private theorem rowsInput_ok {base source table : BitVec 32} {len w bytes N M g x : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows N) (fits : Spec.Rsa.FixedBaseComb.rows N<2^32)
    (s : State) (h : LoopInput base source table len w bytes N M g x (Spec.Rsa.FixedBaseComb.rows N) P s) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.rows K.arithmetic.op) s (TwoExp.OpInput base len w P 7) := by
  refine WP.mono (rows_ok K s positive (Nat.le_refl _) fits h.power h.persistent h.controls h.counter) ?_
  rintro t ⟨power,p,_,_,_,_⟩
  exact ⟨power.ready,p,by rw [power.one]; exact power.ready.modulus⟩

theorem phase_ct {base source table : BitVec 32} {len w bytes N M g x1 x2 : Nat}
    {P1 P2 : State→Prop} {regions1 regions2 : List Region}
    (K1 : Kernel base source table len w bytes N M g x1 P1 regions1)
    (K2 : Kernel base source table len w bytes N M g x2 P2 regions2) (ct : Timing K1 K2)
    (odd : M%2=1) (positive : 0<Spec.Rsa.FixedBaseComb.rows N) (fits : Spec.Rsa.FixedBaseComb.rows N<2^32) :
    RelCT isa (fun s t => PhaseInput base source table len w bytes N M P1 s ∧
      PhaseInput base source table len w bytes N M P2 t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.CombExp.phase K1.arithmetic.op) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombExp.phase
  refine relCT_chain ((initial_ct K1 K2 ct).mono
    (fun _ _ h => ⟨⟨h.1.ready,h.1.persistent⟩,⟨h.2.1.ready,h.2.1.persistent⟩,h.2.2⟩) (fun _ _ h => h))
    (fun s h => initialInput_ok K1 odd s h)
    (fun s h => by simpa only [ct.same] using initialInput_ok K2 odd s h) ?_
  exact relCT_chain (rows_ct K1 K2 ct positive (Nat.le_refl _) fits)
    (fun s h => rowsInput_ok K1 positive fits s h)
    (fun s h => by simpa only [ct.same] using rowsInput_ok K2 positive fits s h)
    (ct.op_ct 6 6 7
      (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp])
      (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp])
      (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]))

end VG.Proof.Bignum.Arm.CombExp
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentPowerLaw.lean`, which only this module imported.
section

/-! # The shared key-generation exponentiator's caller contract -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure EnvironmentPowerLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat} {eb : List Byte},
    SampleContext p (layout p) slots s → env.holds p s → KeyCallMemory p s → stableSlots slots = true →
    52 ∈ slots → 56 ∈ slots → 32 ∈ slots →
    ArithmeticReady p.base p.len p.w s →
    numAt s.mem (State.addr p.base) p.w 0 = p.P → p.P % 2 = 1 →
    numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P →
    Octets p.base (layout p).start p.len eb s → eb.length = (layout p).width →
    Spec.Rsa.os2ip eb < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) →
    WP isa code s fun t => Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod p.G (Spec.Rsa.os2ip eb) p.P ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte},
    stableSlots slots = true → 52 ∈ slots → 56 ∈ slots → 32 ∈ slots →
    eb1.length = (layout p).width → eb2.length = (layout p).width →
    Spec.Rsa.os2ip eb1 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) →
    Spec.Rsa.os2ip eb2 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) → p.P % 2 = 1 →
    RelCT isa (fun s t => ((SamplePowerInput p (layout p) slots eb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((SamplePowerInput p (layout p) slots eb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp) code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPrepareAt.lean`, which only this module imported.
section

/-! Cached RSA prefix import within the existing FFDH local argument frame. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem cachedPrepareAt_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (environment : CachedGenerationContext p s)
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.CachedPrepare.code s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (keyPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CachedPrepare.code, WP.seq_iff]
  refine WP.mono (prepareArgs_ok s 24 h stable h24 h32 h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := contextU.pBytes
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  have input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.sub (by
    intro r hr
    refine ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], ?_⟩
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  have environmentU := environment.after fullU (restU.mono (by simp [roundClobbers]))
  refine WP.mono (cachedPrepareBody_ok u input contextU environmentU h52 stable) ?_
  rintro t ⟨contextT, readyT, modulus, r2, frameT, restT⟩
  have frame : Frame (keyPrepareWrites p s) s.mem t.mem :=
    (frameU.mono (by
      intro r hr
      simp only [keyPrepareWrites, prepareAtWrites, List.mem_append, List.mem_cons]
      exact Or.inl (Or.inr hr))).trans
    (frameT.mono (by simp [keyPrepareWrites, prepareAtWrites]))
  exact ⟨contextT, readyT, modulus, r2, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPrepareAtCT.lean`, which only this module imported.
section

/-! The public FFDH argument adapter preserves the canonical cached environment. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedPrepareArgs_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (h : Context p slots s ∧ CachedGenerationContext p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) s (CachedPrepareInitial p slots) := by
  refine WP.mono (prepareArgs_ok s 24 h.1 stable h24 h32 h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := contextU.pBytes
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  have input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.sub (by
    intro r hr
    refine ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], ?_⟩
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  exact ⟨input, contextU, h.2.after fullU (restU.mono (by simp [roundClobbers]))⟩

theorem cachedPrepareAt_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ CachedGenerationContext p s) ∧
      (Context p slots t ∧ CachedGenerationContext p t) ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.CachedPrepare.code (fun _ _ => True) := by
  have args := (prepareArgs_ct 24).mono
    (P' := fun (s t : State) => (Context p slots s ∧ CachedGenerationContext p s) ∧
      (Context p slots t ∧ CachedGenerationContext p t) ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  exact relCT_chain args (cachedPrepareArgs_next · stable h0 h24 h32 large odd)
    (cachedPrepareArgs_next · stable h0 h24 h32 large odd) (cachedPrepareBody_ct stable h52)

theorem cachedPrepareLaw : EnvironmentPrepareLaw cachedGenerationEnvironment
    VG.Impl.Ffdh.Arm.CachedPrepare.code where
  correct := by
    intro s p slots h environment _calls stable h52 h0 h24 h32 large odd _normalized
    exact cachedPrepareAt_ok s h environment stable h52 h0 h24 h32 large odd
  ct := by
    intro p slots stable h52 h0 h24 h32 large odd _normalized
    exact (cachedPrepareAt_ct stable h52 h0 h24 h32 large odd).mono
      (fun _ _ h => ⟨⟨h.1.1.1, h.1.2⟩, ⟨h.2.1.1.1, h.2.1.2⟩, h.2.2.2⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentScalar.lean`, which only this module imported.
section

/-! A public sampling bound drives the existing fixed byte-cutting instructions. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem environmentScalar_ok (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : EnvironmentBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SampleScalar.code bound) s fun t =>
      SampleContext p (layout p) slots t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = (layout p).encode rb ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SampleScalar.code, WP.seq_iff]
  refine WP.mono (law.correct s h environment normalized odd stable special h52 h24 h28 h32 h60) ?_
  rintro u ⟨contextU, widthU, maskU, frameU, restU⟩
  have entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (sampleScalarArgs_retained u contextU stable special widthU maskU h32 h40 h48) ?_
  rintro v ⟨contextV, dstV, srcV, countV, zeroV, frameV, restV⟩
  have entropyV := entropyU.after_frame frameV restV (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [size, restU.sp]
    exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (sampleCut_ok v contextV (fun d hd => (stableSlots_at stable hd).1)
    entropyV size ((output.after restU).after restV) domainSep (by rw [restV.sp, restU.sp]; exact stackSep)
    entropySep srcV dstV countV zeroV) ?_
  rintro w ⟨contextW, entropyW, bytesW, frameW, restW⟩
  refine WP.mono (localLoad_ok w .r0 contextW.locals (by decide : 0 + 4 ≤ 72)) ?_
  rintro t ⟨loaded, memT, restT⟩
  have ptr : t.gpr .r0 = p.base := loaded.trans (contextW.saved 0 h0)
  have memFrame : Frame [] w.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have args := contextW.toArgumentMemory.after_frame memFrame restT (by simp) (by simp)
  have contextT : SampleContext p (layout p) slots t := by
    refine ⟨⟨args, ptr⟩, ?_, ?_, ?_⟩
    · rw [memT, restT.sp]; exact contextW.scalarStart
    · rw [memT, restT.sp]; exact contextW.scalarWidth
    · rw [memT, restT.sp]; exact contextW.scalarMask
  have entropyT := entropyW.after_frame memFrame restT (by simp)
  have fullU : Frame (keyScalarWrites p s) s.mem u.mem := frameU.mono (by simp [keyScalarWrites])
  have fullV : Frame (keyScalarWrites p s) u.mem v.mem := by
    rw [restU.sp] at frameV
    exact frameV.mono (by simp [keyScalarWrites])
  have fullW : Frame (keyScalarWrites p s) v.mem w.mem := frameW.mono (by simp [keyScalarWrites])
  refine ⟨contextT, entropyT, by rw [memT]; exact bytesW, ?_, ?_⟩
  · rw [memT]
    exact (fullU.trans fullV).trans fullW
  · exact restU.trans ((restV.mono (by simp [roundClobbers])).trans
      ((restW.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentSample.lean`, which only this module imported.
section

/-! Scalar sampling preserves the prepared RSA modulus and exposes both the
full output encoding and its public-width significant suffix. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem environmentSample_ok (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : EnvironmentBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SampleScalar.code bound) s fun t =>
      SampleContext p (layout p) slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Octets p.base p.privateValue p.len ((layout p).encode rb) t ∧
      Octets p.base (layout p).start p.len (((layout p).encode rb).drop (layout p).lead) t ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (environmentScalar_ok env layout bound law s h environment normalized odd stable special h52 h0 h24 h28 h32 h40 h48 h60 entropy size entropyStack
    outputs.privateBuffer outputs.privateDomain outputs.privateStack entropySep) ?_
  rintro t ⟨context, _, bytes, frame, rest⟩
  have workspaceSep (r : Region) (hr : r ∈ keyScalarWrites p s) :
      (⟨State.addr p.base, 8 * p.len⟩ : Region).Disjoint r := by
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact outputs.privateWorkspace.symm
  have baseSep (r : Region) (hr : r ∈ keyScalarWrites p s) :
      (⟨State.addr s.sp, 4⟩ : Region).Disjoint r := by
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact outputs.privateStack.sub_left (Region.sub_prefix (by decide))
  have readyT := ready.after_external frame workspaceSep baseSep rest context.ptr
  have fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  have scalar : Octets p.base p.privateValue p.len ((layout p).encode rb) t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [(layout p).encode_length size]; exact outputs.privateBuffer.fits
    · rw [(layout p).encode_length size, rest.rd, rest.wr]
      obtain ⟨r, hr, hc⟩ := outputs.privateBuffer.writable
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [(layout p).encode_length size]; exact outputs.privateWorkspace
    · rw [(layout p).encode_length size]; exact bytes
  have significant := scalar.slice (d := (layout p).lead) (k := (layout p).width) (layout p).width_bounds.1
    (by rw [(layout p).encode_length size]; unfold ScalarLayout.width; have := (layout p).lead_lt; omega)
  rw [List.take_of_length_le (by rw [List.length_drop, (layout p).encode_length size]; rfl)] at significant
  exact ⟨context, readyT.1, (readyT.2.number fits (by decide : 0 < 8)).trans modulus,
    (readyT.2.number fits (by decide : 4 < 8)).trans r2, scalar, significant, frame, rest⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentScalarCT.lean`, which only this module imported.
section

/-! Public scalar layouts determine sampling addresses and loop counts. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem environmentBound_next (env : SampleEnvironment) (bound : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (law : EnvironmentBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1)
    (h52 : 52 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) (environment : env.holds p s) :
    WP isa bound s (SampleBoundReady p (layout p) slots rb) := by
  refine WP.mono (law.correct s h.context environment normalized odd stable special h52 h24 h28 h32 h60) ?_
  rintro t ⟨context, width, mask, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact h.entropyStack.sub_right (Offset.sub_base _ (by decide)))
  exact ⟨⟨context, entropy, h.outputs.after rest, by rw [rest.sp]; exact h.entropyStack⟩, width, mask⟩

theorem environmentScalar_ct (env : SampleEnvironment) (bound : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (law : EnvironmentBoundLaw env layout bound) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1)
    (h52 : 52 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    RelCT isa (fun s t => (KeyScalarInput p slots rb1 s ∧ env.holds p s) ∧ (KeyScalarInput p slots rb2 t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SampleScalar.code bound) (fun _ _ => True) := by
  have boundCT := (law.ct stable special normalized odd h52 h24 h28 h32 h60).mono
    (P' := fun (s t : State) => (KeyScalarInput p slots rb1 s ∧ env.holds p s) ∧ (KeyScalarInput p slots rb2 t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.context, h.1.2⟩, ⟨h.2.1.1.context, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h)
  have args := keyScalarArgs_ct.mono
    (P' := fun (s t : State) => SampleBoundReady p (layout p) slots rb1 s ∧ SampleBoundReady p (layout p) slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have cut := sampleCut_ct (l := layout p) (fun d hd => (stableSlots_at stable hd).1) size1 size2 entropySep
  unfold VG.Impl.Ffdh.Arm.SampleScalar.code
  have bounded := (relCT_keep_sp boundCT (fun _ _ h => h.2.2.2)).wp
    (fun s t h => ⟨environmentBound_next env bound layout law s stable special normalized odd h52 h24 h28 h32 h60 size1 h.1.1 h.1.2,
      environmentBound_next env bound layout law t stable special normalized odd h52 h24 h28 h32 h60 size2 h.2.1.1 h.2.1.2⟩)
  exact bounded.seq ((relCT_chain args
      (sampleScalarArgs_next · stable special h32 h40 h48 size1)
      (sampleScalarArgs_next · stable special h32 h40 h48 size2)
      (((relCT_keep_sp cut (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 0)).mono
        (fun _ _ h => h) (fun _ _ _ => trivial))).mono
      (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentSampleInstance.lean`, which only this module imported.
section

/-! The existing byte cutter consumes one verified public-context bound. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem environmentSample_law (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (bound : Prog isa) (law : EnvironmentBoundLaw env layout bound) :
    EnvironmentSampleLaw env layout (VG.Impl.Ffdh.Arm.SampleScalar.code bound) where
  correct := environmentSample_ok env layout bound law
  ct := by
    intro p slots rb1 rb2 stable special normalized odd h52 _h0 h24 h28 h32 h40 h48 h60 size1 size2 separate
    exact environmentScalar_ct env bound layout law stable special normalized odd h52 h24 h28 h32 h40 h48 h60 size1 size2 separate

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedSampleInstance.lean`, which only this module imported.
section

/-! Cached sampling uses only canonical public header words and the shared byte cutter. -/

section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm

theorem boundLaw : EnvironmentBoundLaw cachedGenerationEnvironment ScalarLayout.vetted
    VG.Impl.Ffdh.Arm.CachedSample.bound where
  correct := by
    intro s p slots h environment _normalized _odd _stable special h52 _h24 _h28 _h32 _h60
    exact bound_ok s h environment h52 special (bits_positive environment) (bits_bound p)
  ct := by
    intro p slots _stable _special _normalized _odd h52 _h24 _h28 _h32 _h60
    exact (bound_ct h52).mono (fun _ _ h => ⟨h.1, h.2.1, h.2.2.2⟩) (fun _ _ h => h)

theorem law : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted
    VG.Impl.Ffdh.Arm.CachedSample.code :=
  environmentSample_law cachedGenerationEnvironment ScalarLayout.vetted _ boundLaw

end VG.Proof.Ffdh.Arm.CachedSample
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPowerVetted.lean`, which only this module imported.
section

/-! The reviewed scalar layout supplies the evaluator's public schedule bounds. -/

section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPowerPersistent.lean`, which only this module imported.
section

/-! Canonical contexts and the sampled scalar form the evaluator's read-only invariant. -/

section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem persistent {p : Inputs} {l : ScalarLayout p} {s : State} {eb : List Byte} {sp : BitVec 32}
    (cached : CachedGenerationContext p s) (calls : KeyCallMemory p s)
    (exponent : Octets p.base l.start p.len eb s) (size : eb.length=l.width) (stack : s.sp=sp) :
    CombExp.Persistent p.base l.start (table p) sp p.len p.w p.P p.G (bits p) eb s := by
  refine ⟨⟨calls.stack,stack⟩,⟨exponent.fits,exponent.readable,exponent.byte⟩,cached.table,?_,?_⟩
  · intro r hr
    simp only [CombExp.writeRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact exponent.separate
    · rw [size,←stack]; exact significant_below calls
  · intro r hr
    apply cached.tableSeparate r
    simp only [CombExp.writeRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · simp [keyCallWrites,keyWrites]
    · simp [keyCallWrites,keyWrites,stack]

end VG.Proof.Ffdh.Arm.CachedPower
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombExpBackendCT.lean`, which only this module imported.
section

/-! Shared arithmetic timing does not require the secret exponent bytes to agree. -/

section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem arithmetic_ct (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) (o a b : Nat)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t=>
      TwoExp.OpInput base len w (TwoExp.CallReady base sp len) b s ∧
      TwoExp.OpInput base len w (TwoExp.CallReady base sp len) b t ∧ s.sp=t.sp)
      ((arithmetic backend base source table sp len w M g N bs).op o a b) (fun _ _=>True) := by
  have timing := TwoExp.sharedMontgomeryTiming base sp len w backend.name backend.mul
    (fun _ _ _ ho ha hb s h=>backend.correct s h ho ha hb) backend.stackOk
    (fun _ _ _ ho ha hb=>backend.rawCT ho ha hb)
  exact timing.op_ct o a b ho ha hb

end VG.Proof.Bignum.Arm.CombExp
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombExpBackendTiming.lean`, which only this module imported.
section

/-! Every RSA Montgomery backend supports independent secret comb exponents. -/

section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

theorem backendTiming (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes M g N : Nat) (bs1 bs2 : List Byte)
    (length1 : bs1.length=bytes) (length2 : bs2.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit1 : Spec.Rsa.os2ip bs1<2^N) (scalarFit2 : Spec.Rsa.os2ip bs2<2^N) :
    Timing (kernelAt backend base source table sp len w bytes M g N bs1 length1 widthBound size scheduleFit widthFit scalarFit1)
      (kernelAt backend base source table sp len w bytes M g N bs2 length2 widthBound size scheduleFit widthFit scalarFit2) := by
  refine ⟨rfl,?_,?_⟩
  · intro o a b ho ha hb
    exact (arithmetic_ct backend base source table sp len w M g N bs1 o a b ho ha hb).mono
      (fun _ _ h => ⟨⟨h.1.1,h.1.2.1.1,h.1.2.2⟩,
        ⟨h.2.1.1,h.2.1.2.1.1,h.2.1.2.2⟩,h.2.2⟩) (fun _ _ h => h)
  · intro i E1 E2 hi
    exact choose_ct backend base source table sp len w bytes N M g E1 E2 i bs1 bs2 length1 length2
      widthBound size scheduleFit widthFit scalarFit1 scalarFit2 hi

end VG.Proof.Bignum.Arm.CombExp
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPowerCT.lean`, which only this module imported.
section

/-! Cached native exponentiation hides independent sampled scalars. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPowerInstance.lean`, which only this module imported.
section

/-! One reusable RSA Montgomery helper instantiates cached private-key powers. -/

section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm

def power (backend : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.CachedPower.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)

theorem powerLaw (backend : MontBackend) :
    EnvironmentPowerLaw cachedGenerationEnvironment ScalarLayout.vetted (power backend) := by
  constructor
  · intro s p slots eb context cached calls stable h52 _h56 _h32 ready modulus odd r2 exponent size scalarFit
    exact vetted_correct backend s context cached calls stable h52 ready modulus odd r2 exponent size scalarFit
  · exact code_ct backend

end VG.Proof.Ffdh.Arm.CachedPower
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentCallTail.lean`, which only this module imported.
section

/-! # Finish a key-generation attempt using shared arithmetic calls -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem environmentCallTail_ok {env : SampleEnvironment} {layout : (p : Inputs) → ScalarLayout p}
    {power : Prog isa} (law : EnvironmentPowerLaw env layout power) (s : State) {p : Inputs} {slots : List Nat} {xb eb : List Byte}
    (h : SampleContext p (layout p) slots s) (environment : env.holds p s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (scalar : Octets p.base p.privateValue p.len xb s) (scalarSize : xb.length = p.k)
    (scalarFits : Spec.Rsa.os2ip xb < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (significant : Octets p.base (layout p).start p.len eb s) (significantSize : eb.length = (layout p).width)
    (significantValue : Spec.Rsa.os2ip eb = Spec.Rsa.os2ip xb)
    (outputs : KeyOutputs p s) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) s fun t =>
      t.gpr .r0 = (if keyAccepted p xb then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if keyAccepted p xb then xb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if keyAccepted p xb then Spec.Rsa.i2osp (keyPower p xb) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  have fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.KeyGenerate.tail, WP.seq_iff]
  refine WP.mono (law.correct s h environment calls stable h52 h56 h32 ready modulus odd r2 significant significantSize (by rw [significantValue]; exact scalarFits)) ?_
  rintro u ⟨contextU, readyU, powerU, modU, _, _, frameU, restU⟩
  rw [significantValue] at powerU
  change numAt u.mem (State.addr p.base) p.w 6 = keyPower p xb at powerU
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok u readyU (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [modU]; exact odd)) ?_
  rintro v ⟨readyV, flag, arraysV, frameV, restV⟩
  have contextV := contextU.after_workspace frameV restV readyV.ptr (fun d hd => (stableSlots_at stable hd).1)
  have powerV := (arraysV 6 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerU
  have flagV : v.gpr .r11 = if keyAccepted p xb then 1 else 0 := by
    rw [powerU, modU] at flag
    simpa only [keyAccepted, decide_eq_true_eq] using flag
  rw [WP.seq_iff]
  refine WP.mono (saveResult_ok v contextV.locals) ?_
  rintro w ⟨⟨_, resultW, frameW⟩, restW⟩
  have ptrW := (restW.gpr .r0 (by simp)).trans contextV.ptr
  have contextW := contextV.after_local (by decide : 64 + 4 ≤ 72) frameW restW ptrW
    (fun d hd => (stableSlots_at stable hd).1) saved
  have readyW := readyV.after_external frameW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    exact contextV.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))) (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [off, BitVec.add_zero] using
      Offset.disjoint (State.addr v.sp) (d := 0) (n := 4) (e := 64) (k := 4) (by left; decide) (by decide) (by decide)) restW ptrW
  have powerW := (readyW.2.number fits (by decide : 6 < 8)).trans powerV
  have powerFits : numAt w.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k) := by
    rw [powerW, keyPower, VG.Proof.Bignum.powMod_eq]
    have large := ready.modulus
    rw [modulus] at large
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound
  rw [WP.seq_iff]
  refine WP.mono (exportResult_ok w contextW h4 h32 readyW.1
    (by rw [outputY]; exact ((outputs.publicBuffer.after restU).after restV).after restW)
    (by rw [outputY]; exact outputs.publicWorkspace.symm) powerFits) ?_
  rintro z ⟨publicZ, frameZ, restZ⟩
  rw [powerW, outputY] at publicZ
  rw [outputY] at frameZ
  have outW := ((outputs.after restU).after restV).after restW
  have contextZ := contextW.toArgumentMemory.after_output frameZ restZ outW.publicDomain outW.publicStack
    (fun d hd => (stableSlots_at stable hd).1)
  have resultZ : z.mem.readW (off (State.addr z.sp) 64) 32 = if keyAccepted p xb then 1 else 0 := by
    rw [restZ.sp, frameZ.readW (r := ⟨off (State.addr w.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa using outW.publicStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide), restW.sp, resultW, flagV]
  refine WP.mono (keyFinish_ok z (keyAccepted p xb) contextZ (fun d hd => (stableSlots_at stable hd).1)
    h32 h36 h40 (outW.after restZ) resultZ) ?_
  rintro t ⟨status, privateT, publicT, frameT, _⟩
  have privateU := scalar.after_call frameU restU (by simpa only [scalarSize] using calls.privateValue)
  have privateW := (privateU.after_workspace frameV restV).after_frame frameW restW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [scalarSize, restV.sp, restU.sp] using
      outputs.privateStack.symm.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72)))
  have privateZ := privateW.after_frame frameZ restZ (by simpa only [scalarSize, List.mem_singleton, forall_eq] using outputs.separate)
  have privateBytesZ := privateZ.bytes
  rw [scalarSize] at privateBytesZ
  rw [privateBytesZ] at privateT
  rw [publicZ] at publicT
  refine ⟨status, privateT, publicT, ?_⟩
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  have fullV : Frame (keyCallWrites p s) u.mem v.mem := frameV.mono (by simp [keyCallWrites, keyWrites])
  have fullW : Frame (keyCallWrites p s) v.mem w.mem := frameW.sub (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    refine ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], ?_⟩
    rw [restV.sp, restU.sp]
    exact Offset.sub_base _ (by decide))
  exact (((fullU.trans fullV).trans fullW).trans (frameZ.mono (by simp [keyCallWrites, keyWrites]))).trans
    (frameT.mono (by simp [keyCallWrites, keyWrites]))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentCallTailCT.lean`, which only this module imported.
section

/-! # Key-generation finish timing with shared exponentiation -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

theorem environmentCallPower_next {env : SampleEnvironment} {layout : (p : Inputs) → ScalarLayout p}
    {power : Prog isa} (law : EnvironmentPowerLaw env layout power) (s : State)
    {p : Inputs} {slots : List Nat} {eb : List Byte}
    (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (size : eb.length = (layout p).width) (exponentFits : Spec.Rsa.os2ip eb < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (odd : p.P % 2 = 1)
    (h : (SamplePowerInput p (layout p) slots eb s ∧ KeyCallMemory p s) ∧ env.holds p s) :
    WP isa power s (KeyRangeInput p slots) := by
  refine WP.mono (law.correct s h.1.1.context h.2 h.1.2 stable h52 h56 h32 h.1.1.ready h.1.1.modulus odd
    h.1.1.r2 h.1.1.exponent size exponentFits) ?_
  rintro t ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.1.1.outputs.after rest, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  have large := h.1.1.ready.modulus
  rw [h.1.1.modulus] at large
  exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound

theorem environmentCallTail_ct {env : SampleEnvironment} {layout : (p : Inputs) → ScalarLayout p}
    {power : Prog isa} (law : EnvironmentPowerLaw env layout power)
    {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : eb1.length = (layout p).width) (size2 : eb2.length = (layout p).width)
    (fit1 : Spec.Rsa.os2ip eb1 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (fit2 : Spec.Rsa.os2ip eb2 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (odd : p.P % 2 = 1) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => ((SamplePowerInput p (layout p) slots eb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((SamplePowerInput p (layout p) slots eb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) (fun _ _ => True) := by
  have range := (inRange_ct (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => KeyRangeInput p slots s ∧ KeyRangeInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.tail
  exact ((relCT_keep_sp (law.ct stable h52 h56 h32 size1 size2 fit1 fit2 odd)
      (fun _ _ h => h.2.2.2)).wp (fun s t h =>
        ⟨environmentCallPower_next law s stable h52 h32 h56 size1 fit1 odd h.1,
         environmentCallPower_next law t stable h52 h32 h56 size2 fit2 odd h.2.1⟩)).seq
    ((relCT_chain range (keyRange_next · stable odd) (keyRange_next · stable odd)
      (keyExportFinish_ct stable h4 h32 h36 h40 saved outputY)).mono
        (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

theorem environmentCallTail_law {env : SampleEnvironment} {layout : (p : Inputs) → ScalarLayout p}
    {power : Prog isa} (law : EnvironmentPowerLaw env layout power) :
    EnvironmentTailLaw env layout (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) where
  correct := environmentCallTail_ok law
  ct := environmentCallTail_ct law

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyLaws.lean`, which only this module imported.
section

/-! One arithmetic backend supplies the cached attempt's preparation, sampling and power laws. -/

section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm

theorem prepareLaw : EnvironmentPrepareLaw cachedGenerationEnvironment prepare := cachedPrepareLaw

theorem sampleLaw : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample := CachedSample.law

theorem tailLaw (backend : MontBackend) :
    EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted (tail backend) :=
  environmentCallTail_law (CachedPower.powerLaw backend)

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyStack.lean`, which only this module imported.
section

/-! Cached comb attempts retain the existing 176-byte public stack reservation. -/

section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm

theorem stack_ok (backend : MontBackend) : FrameStack.armStack (code backend) ≤ 176 := by
  have prepareZero : FrameStack.armStack prepare = 0 := rfl
  have sampleZero : FrameStack.armStack sample = 0 := rfl
  have chooseZero : FrameStack.armStack CombExp.choose = 0 := rfl
  have oneZero : FrameStack.armStack (smallConst 7 1) = 0 := rfl
  have argsZero : FrameStack.armStack VG.Impl.Ffdh.Arm.CachedPower.args = 0 := rfl
  have importZero : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) = 0 := rfl
  have rangeZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange = 0 := rfl
  have publicRangeZero : FrameStack.armStack (VG.Impl.Ffdh.Arm.inRange 6) = 0 := rfl
  have exportZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult = 0 := rfl
  have finishZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish = 0 := rfl
  have failZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar = 0 := rfl
  have bound := backend.stackOk
  simp only [code, tail, VG.Impl.Ffdh.Arm.CachedKeyGenerate.code,
    VG.Impl.Ffdh.Arm.CachedKeyGenerate.body, VG.Impl.Ffdh.Arm.SampleKeyGenerate.main,
    VG.Impl.Ffdh.Arm.KeyGenerate.tail, VG.Impl.Ffdh.Arm.CachedPower.code,
    VG.Impl.Ffdh.Arm.framed, VG.Impl.Ffdh.Arm.Domain.ifFlag, VG.Impl.Ffdh.Arm.Domain.testFlag,
    CombExp.phase, CombExp.initial, CombExp.rows, CombExp.round, CombExp.step,
    MontCall.op, FrameStack.armStack, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.max_self, Nat.max_zero, Nat.zero_max,
    prepareZero, sampleZero, chooseZero, oneZero, argsZero, importZero, rangeZero,
    publicRangeZero, exportZero, finishZero, failZero]
  omega

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGeneratePost.lean`, which only this module imported.
section

/-! Cached attempts return the reviewed vetted scalar and public power. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_post (s t : State) {p : Inputs} {rb : List Byte}
    (privateValue : s.gpr .r0=p.privateValue) (publicValue : s.gpr .r2=p.publicValue)
    (domain : stackArg s 0=p.domain) (count : (stackArg s 2).toNat=p.k)
    (entropy : stackArg s 3=p.entropy)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k=rb)
    (randLength : (stackArg s 4).toNat=(stackArg s 2).toNat) (size : rb.length=p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom=true)
    (result : sampleResult p (ScalarLayout.vetted p) rb t) :
    (Spec.Ffdh.cachedGenerateKeyContract abi 176).post s t := by
  sig_post [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,
    Spec.Ffdh.generateKeySig,abi,argRegs,reduceClassify,Loc.val,State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes entropyBytes
  simp only [randLength,count,domain,entropy,domainBytes,entropyBytes,privateValue,publicValue]
  have output := sampleResult_spec size valid result
  rwa [ScalarLayout.vetted_value size] at output

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateCorrect.lean`, which only this module imported.
section

/-! The complete cached attempt implements its reviewed immutable-context contract. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_correct (prepare sample tail : Prog isa)
    (prep : EnvironmentPrepareLaw cachedGenerationEnvironment prepare)
    (sampler : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample)
    (law : EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted tail)
    (s : State) (pre : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
    ∃tr t,Exec isa (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.cachedGenerateKeyContract abi 176).post s t := by
  obtain ⟨p,rb,_,privateValue,publicValue,domain,count,_,entropy,domainBytes,entropyBytes,input,cached,valid,_cache,_words⟩ :=
    cachedKeyGenerate_data s pre
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  obtain ⟨tr,t,run,preserved,result⟩ := cachedKeyGenerateFn_ok prepare sample tail cachedGenerationEnvironment
    ScalarLayout.vetted prep sampler law CachedSample.layoutBound s input cached modValid
  refine ⟨tr,t,run,preserved,?_⟩
  have randLength : (stackArg s 4).toNat=(stackArg s 2).toNat := by
    sig_pre [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
      abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rLen,_,_,_⟩ := pre
    exact rLen
  exact cachedKeyGenerate_post s t privateValue publicValue domain count entropy domainBytes entropyBytes
    randLength input.input.size valid result

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateVerified.lean`, which only this module imported.
section

/-! Functional correctness, timing and a real canonical-context witness certify cached attempts. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_verified (prepare sample tail : Prog isa)
    (prep : EnvironmentPrepareLaw cachedGenerationEnvironment prepare)
    (sampler : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample)
    (law : EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted tail) :
    Verified target (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail)
      (Spec.Ffdh.cachedGenerateKeyContract abi 176) :=
  ⟨cachedKeyGenerate_correct prepare sample tail prep sampler law,
    cachedKeyGenerate_contract_ct prepare sample tail prep sampler law,cachedKeyGenerate_sat⟩

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm

def native (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem native_verified (b : MontBackend) : Verified target (native b)
    (Spec.Ffdh.cachedGenerateKeyContract abi 176) :=
  b.caller.verified (cachedKeyGenerate_verified prepare sample (tail b) prepareLaw sampleLaw (tailLaw b))

theorem native_stack (b : MontBackend) : FrameStack.armStack (native b)≤176 :=
  Nat.le_trans (b.caller.stack_le _) (stack_ok b)

def backend (b : MontBackend) : KeyBackend .cached where
  generateKey := native b
  generateKey_verified := native_verified b
  keyStack := native_stack b
  suffix := b.suffix
  features := b.features

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
