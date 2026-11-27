module

public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord

/-! ### `Ffdh.Arm.KeyGenerateFn`, which only this module used -/

section

/-! ### `Ffdh.Arm.KeyFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeyEntry`, which this module and modules that import it used -/

section

/-! Retain the key-generation ABI's domain, entropy, and two output pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure KeyIncoming (p : Inputs) (s : State) : Prop where
  domain : IncomingWord p.domain 128 s
  domainLength : IncomingWord (BitVec.ofNat 32 p.dom.length) 132 s
  count : IncomingWord (BitVec.ofNat 32 p.k) 136 s
  entropy : IncomingWord p.entropy 140 s
  scratch : IncomingWord p.base 148 s

theorem keyEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : KeyIncoming p s) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (outputY : p.output = p.publicValue)
    (privateLength : p.privateLength = p.k) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry) s fun t =>
      Context p [0, 48, 44, 32, 28, 24, 4, 36, 40] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  obtain rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  obtain args0 := h.of_mem moved.mem rest0
  obtain frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  obtain stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 40 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans privateValue) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  obtain rest1 := rest0.trans (stepRest1.mono (by simp))
  obtain stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  obtain frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r2 36 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r2 (by simp)).trans publicValue) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  obtain rest2 := rest1.trans (stepRest2.mono (by simp))
  obtain stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  obtain frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r2 4 args2 (by decide) (by decide) (by decide)
    (by change s2.gpr .r2 = p.output; rw [outputY]; exact (rest2.gpr .r2 (by simp)).trans publicValue) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  obtain rest3 := rest2.trans (stepRest3.mono (by simp))
  obtain stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  obtain frame3 := frame2.trans stepFrame3
  obtain allRest3 : Rest roundClobbers s s3 := rest3.mono (by simp [roundClobbers])
  refine wp_retain_incoming .r3 (by decide) args3 (by decide)
    (incoming.domain.after (by decide) frame3 allRest3) (by decide) (by decide) (by decide) stack3
    fun s4 args4 stepFrame4 stepRest4 value4 stack4 => ?_
  obtain allRest4 := allRest3.trans (stepRest4.mono (by simp [roundClobbers]))
  rw [allRest3.sp] at stepFrame4
  obtain frame4 := frame3.trans stepFrame4
  refine wp_retain_incoming .r3 (by decide) args4 (by decide)
    (incoming.domainLength.after (by decide) frame4 allRest4) (by decide) (by decide) (by decide) stack4
    fun s5 args5 stepFrame5 stepRest5 value5 stack5 => ?_
  obtain allRest5 := allRest4.trans (stepRest5.mono (by simp [roundClobbers]))
  rw [allRest4.sp] at stepFrame5
  obtain frame5 := frame4.trans stepFrame5
  refine wp_retain_incoming .r3 (by decide) args5 (by decide)
    (incoming.count.after (by decide) frame5 allRest5) (by decide) (by decide) (by decide) stack5
    fun s6 args6 stepFrame6 stepRest6 value6 stack6 => ?_
  obtain allRest6 := allRest5.trans (stepRest6.mono (by simp [roundClobbers]))
  rw [allRest5.sp] at stepFrame6
  obtain frame6 := frame5.trans stepFrame6
  refine wp_store_arg .r3 44 args6 (by decide) (by decide) (by decide)
    (by change s6.gpr .r3 = BitVec.ofNat 32 p.privateLength; rw [privateLength]; exact value6)
    stack6 fun s7 args7 stepFrame7 stepRest7 => ?_
  obtain stack7 := (stepRest7.gpr .r12 (by simp)).trans (stack6.trans stepRest7.sp.symm)
  obtain allRest7 := allRest6.trans (stepRest7.mono (by simp [roundClobbers]))
  rw [allRest6.sp] at stepFrame7
  obtain frame7 := frame6.trans stepFrame7
  refine wp_retain_incoming .r3 (by decide) args7 (by decide)
    (incoming.entropy.after (by decide) frame7 allRest7) (by decide) (by decide) (by decide) stack7
    fun s8 args8 stepFrame8 stepRest8 value8 stack8 => ?_
  obtain allRest8 := allRest7.trans (stepRest8.mono (by simp [roundClobbers]))
  rw [allRest7.sp] at stepFrame8
  obtain frame8 := frame7.trans stepFrame8
  refine wp_retain_incoming .r0 (by decide) args8 (by decide)
    (incoming.scratch.after (by decide) frame8 allRest8) (by decide) (by decide) (by decide) stack8
    fun s9 args9 stepFrame9 stepRest9 value9 stack9 => ?_
  apply WP.block_nil
  refine ⟨⟨args9, value9⟩, ?_⟩
  rw [allRest8.sp] at stepFrame9
  exact frame8.trans stepFrame9

end VG.Proof.Ffdh.Arm

end

end

/-! AAPCS key generation from caller-provided entropy with native rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure KeyFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : KeyIncoming p (entered s)
  privateValue : s.gpr .r0 = p.privateValue
  publicValue : s.gpr .r2 = p.publicValue
  outputY : p.output = p.publicValue
  privateLength : p.privateLength = p.k
  entropy : Octets p.base p.entropy p.len rb (entered s)
  size : rb.length = p.k
  entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr (entered s).sp, 72⟩
  outputs : KeyOutputs p (entered s)
  entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩
  saved : ∀ r ∈ keyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

end VG.Proof.Ffdh.Arm

end

end

/-! AAPCS key generation from caller-provided entropy with native rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure KeyGenerateFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop extends KeyFnInput p rb s where
  calls : KeyCallMemory p (entered s)
  savedCall : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint (FrameStack.belowA (entered s).sp 48)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CachedKeyGenerateInput`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CachedKeyGeneratePre`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CachedKeyGenerateFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeyMain`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeyFail`, which this module and modules that import it used -/

section

/-! Out-of-range random scalars return retry status 2 and clear both encodings. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem keyFail_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (outputs : KeyOutputs p s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar s fun t =>
      t.gpr .r0 = 2 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = List.replicate p.k 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k = List.replicate p.k 0 ∧
      Frame [⟨State.addr p.privateValue, p.k⟩, ⟨State.addr p.publicValue, p.k⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar, WP.seq_iff]
  refine WP.mono (keyClear_ok s 40 h (by decide) h40 h32 outputs.privateBuffer) ?_
  rintro u ⟨privateU, frameU, restU⟩
  change Spec.Rsa.bytesAt u.mem (State.addr p.privateValue) p.k = _ at privateU
  change Frame [⟨State.addr p.privateValue, p.k⟩] s.mem u.mem at frameU
  have contextU := h.after_output frameU restU outputs.privateDomain outputs.privateStack saved
  rw [WP.seq_iff]
  refine WP.mono (keyClear_ok u 36 contextU (by decide) h36 h32 (outputs.publicBuffer.after restU)) ?_
  rintro v ⟨publicV, frameV, _⟩
  change Spec.Rsa.bytesAt v.mem (State.addr p.publicValue) p.k = _ at publicV
  change Frame [⟨State.addr p.publicValue, p.k⟩] u.mem v.mem at frameV
  refine WP.mono (ret_ok v 2 (by decide)) ?_
  rintro t ⟨⟨status, mem⟩, _⟩
  refine ⟨status, ?_, by rw [mem]; exact publicV, ?_⟩
  · rw [mem, VG.Proof.Bignum.Arm.rsa_bytes_frame frameV (by have := p.maxLength; omega_using [this])
      (by simpa using outputs.separate)]
    exact privateU
  · rw [mem]
    exact (frameU.mono (by simp)).trans (frameV.mono (by simp))

end VG.Proof.Ffdh.Arm

end

end

/-! One key-generation attempt runs sampling, scalar validation, windowed
exponentiation, and output rejection entirely in native ARMv7 code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def keyScalarValid (p : Inputs) (rb : List Byte) : Prop :=
  0 < Spec.Rsa.os2ip (scalarOctets p rb) ∧ Spec.Rsa.os2ip (scalarOctets p rb) < scalarBound p

instance (p : Inputs) (rb : List Byte) : Decidable (keyScalarValid p rb) := inferInstanceAs (Decidable (_ ∧ _))

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CachedKeyGenerateEntry`, which this module and modules that import it used -/

section

/-! Preserve all existing arguments and retain the appended read-only context pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem cachedKeyGenerateEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : KeyIncoming p s) (cache : IncomingWord p.cachedContext 156 s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry) s fun t =>
      Context p [52, 0, 48, 44, 32, 28, 24, 4, 36, 40] t ∧
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry, WP.block_append_iff]
  refine WP.mono (withAllRest (keyEntry_ok s h incoming privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  refine wp_stackAddr (by decide) fun v moved => ?_
  have restV : Rest [.r12] u v := moved.rest (by simp)
  have contextV := contextU.of_mem moved.mem restV ((restV.gpr .r0 (by simp)).trans contextU.ptr)
  have cacheU := cache.after (by decide) frameU restU
  have cacheV : IncomingWord p.cachedContext 156 v :=
    ⟨by rw [moved.sp]; exact cacheU.fits,
      by rw [moved.rd, moved.wr, moved.sp]; exact cacheU.readable,
      by rw [moved.mem, moved.sp]; exact cacheU.word⟩
  refine wp_retain_incoming .r3 (by decide) contextV.toArgumentMemory (by decide)
    cacheV (by decide) (by decide) (by decide)
    (by rw [moved.gpr, moved.sp]; exact BitVec.add_zero _) fun t args frameT restT _ _ => ?_
  apply WP.block_nil
  refine ⟨⟨args, (restT.gpr .r0 (by simp)).trans contextV.ptr⟩, ?_⟩
  rw [moved.mem, moved.sp, restU.sp] at frameT
  exact frameU.trans frameT

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.EnvironmentTailLaw`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SamplePowerLaw`, which this module and modules that import it used -/

section

/-! # The shared key-generation exponentiator's caller contract -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure SamplePowerInput (p : Inputs) (l : ScalarLayout p) (slots : List Nat)
    (eb : List Byte) (s : State) : Prop where
  context : SampleContext p l slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  exponent : Octets p.base l.start p.len eb s
  outputs : KeyOutputs p s

end VG.Proof.Ffdh.Arm

end

end

/-! # The public-value exponentiation boundary of a key-generation attempt -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

structure EnvironmentTailLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat} {xb eb : List Byte}
    (_h : SampleContext p (layout p) slots s) (_environment : env.holds p s) (_calls : KeyCallMemory p s) (_stable : stableSlots slots = true)
    (_h52 : 52 ∈ slots) (_h4 : 4 ∈ slots) (_h32 : 32 ∈ slots)
    (_h36 : 36 ∈ slots) (_h40 : 40 ∈ slots) (_h56 : 56 ∈ slots)
    (_saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (_ready : ArithmeticReady p.base p.len p.w s)
    (_modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (_odd : p.P % 2 = 1)
    (_r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (_scalar : Octets p.base p.privateValue p.len xb s) (_scalarSize : xb.length = p.k)
    (_scalarFits : Spec.Rsa.os2ip xb < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (_significant : Octets p.base (layout p).start p.len eb s) (_significantSize : eb.length = (layout p).width)
    (_significantValue : Spec.Rsa.os2ip eb = Spec.Rsa.os2ip xb)
    (_outputs : KeyOutputs p s) (_outputY : p.output = p.publicValue),
    WP isa code s fun t =>
      t.gpr .r0 = (if keyAccepted p xb then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if keyAccepted p xb then xb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if keyAccepted p xb then Spec.Rsa.i2osp (keyPower p xb) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem
  ct : ∀ {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (_stable : stableSlots slots = true) (_h52 : 52 ∈ slots) (_h4 : 4 ∈ slots) (_h32 : 32 ∈ slots)
    (_h36 : 36 ∈ slots) (_h40 : 40 ∈ slots) (_h56 : 56 ∈ slots)
    (_saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (_size1 : eb1.length = (layout p).width) (_size2 : eb2.length = (layout p).width)
    (_fit1 : Spec.Rsa.os2ip eb1 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (_fit2 : Spec.Rsa.os2ip eb2 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (_odd : p.P % 2 = 1) (_outputY : p.output = p.publicValue),
    RelCT isa (fun s t => ((SamplePowerInput p (layout p) slots eb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((SamplePowerInput p (layout p) slots eb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      code (fun _ _ => True)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.EnvironmentSampleLaw`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SampleResult`, which this module and modules that import it used -/

section

/-! Key-attempt results parameterized by their public scalar layout. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

def sampleScalarValid (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : Prop :=
  0 < Spec.Rsa.os2ip (l.encode rb) ∧ Spec.Rsa.os2ip (l.encode rb) < scalarBound p

instance (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : Decidable (sampleScalarValid p l rb) :=
  inferInstanceAs (Decidable (_ ∧ _))

def sampleSuccess (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : Bool :=
  decide (sampleScalarValid p l rb) && keyAccepted p (l.encode rb)

def sampleMainFlag (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : BitVec 32 :=
  if sampleScalarValid p l rb then (if keyAccepted p (l.encode rb) then 1 else 3) else 2

def sampleResult (p : Inputs) (l : ScalarLayout p) (rb : List Byte) (s : State) : Prop :=
  s.gpr .r0 = sampleMainFlag p l rb ∧
  Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.k =
    (if sampleSuccess p l rb then l.encode rb else List.replicate p.k 0) ∧
  Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k =
    (if sampleSuccess p l rb then Spec.Rsa.i2osp (keyPower p (l.encode rb)) p.k else List.replicate p.k 0)

end VG.Proof.Ffdh.Arm

end

end

/-! A sampling policy supplies both scalar encoding and its public execution width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure EnvironmentSampleLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (_h : Context p slots s) (_environment : env.holds p s)
    (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (_odd : p.P % 2 = 1) (_stable : stableSlots slots = true) (_slots : sampleSlots slots)
    (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h28 : 28 ∈ slots) (_h32 : 32 ∈ slots)
    (_h40 : 40 ∈ slots) (_h48 : 48 ∈ slots) (_h60 : 60 ∈ slots)
    (_ready : ArithmeticReady p.base p.len p.w s)
    (_modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P)
    (_r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (_entropy : Octets p.base p.entropy p.len rb s) (_size : rb.length = p.k)
    (_entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (_outputs : KeyOutputs p s)
    (_entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩),
    WP isa code s fun t =>
      SampleContext p (layout p) slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Octets p.base p.privateValue p.len ((layout p).encode rb) t ∧
      Octets p.base (layout p).start p.len (((layout p).encode rb).drop (layout p).lead) t ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (_stable : stableSlots slots = true) (_slots : sampleSlots slots)
    (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (_odd : p.P % 2 = 1)
    (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h28 : 28 ∈ slots) (_h32 : 32 ∈ slots)
    (_h40 : 40 ∈ slots) (_h48 : 48 ∈ slots) (_h60 : 60 ∈ slots)
    (_size1 : rb1.length = p.k) (_size2 : rb2.length = p.k)
    (_entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩),
    RelCT isa (fun s t => (KeyScalarInput p slots rb1 s ∧ env.holds p s) ∧ (KeyScalarInput p slots rb2 t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      code (fun _ _ => True)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.EnvironmentPrepareLaw`, which this module and modules that import it used -/

section

/-! # Modulus preparation shared by key-generation arithmetic backends

The public modulus gate supplies the lower bound for its packed-word width.
Preparation may use that normalization without adding a caller obligation to
FFDH's shared contract.
-/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure EnvironmentPrepareLaw (env : SampleEnvironment) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat}
    (_h : Context p slots s) (_environment : env.holds p s) (_calls : KeyCallMemory p s)
    (_stable : stableSlots slots = true) (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h32 : 32 ∈ slots)
    (_large : 1 < p.P) (_odd : p.P % 2 = 1) (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P),
    WP isa code s fun t => Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (keyPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat}
    (_stable : stableSlots slots = true) (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h32 : 32 ∈ slots)
    (_large : 1 < p.P) (_odd : p.P % 2 = 1) (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P),
    RelCT isa (fun s t => ((Context p slots s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((Context p slots t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp) code (fun _ _ => True)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.EnvironmentKeyGenerateMain`, which only this module used -/

section

/-! Generic key-generation sampling, validation and result handling for a supplied verified exponentiator. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

theorem environmentKeyGenerateMain_ok (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : EnvironmentPrepareLaw env prepare) (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) <
        2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (special : sampleSlots slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail) s fun t =>
      t.gpr .r0 = sampleMainFlag p (layout p) rb ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if sampleSuccess p (layout p) rb then (layout p).encode rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if sampleSuccess p (layout p) rb then Spec.Rsa.i2osp (keyPower p ((layout p).encode rb)) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  obtain op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (keyCallWrites p s) m m' :=
    f.mono (by simp [keyCallWrites, keyWrites])
  rw [VG.Impl.Ffdh.Arm.SampleKeyGenerate.main, WP.seq_iff]
  refine WP.mono_syms (prep.correct s h environment calls stable h52 h0 h24 h32 large odd normalized) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩ symsU
  obtain fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [keyCallWrites, keyWrites], by intro a ha; exact ha⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨_, by simp [keyCallWrites], fun _ hx => hx⟩)
  obtain environmentU := env.stable environment fullU restU symsU
  obtain entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact entropy.separate
    · rw [size]; exact entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact calls.entropy)
  rw [WP.seq_iff]
  refine WP.mono_syms (sampler.correct u contextU environmentU normalized odd stable special h52 h0 h24 h28 h32 h40 h48 h60 readyU modU r2U entropyU size
    (by rw [restU.sp]; exact entropyStack) (outputs.after restU) entropySep) ?_
  rintro v ⟨contextV, readyV, modV, r2V, scalarV, significantV, frameV, restV⟩ symsV
  obtain scalarSize := (layout p).encode_length size
  obtain count : p.slotValue 44 = BitVec.ofNat 32 ((layout p).encode rb).length := by
    change BitVec.ofNat 32 p.privateLength = _
    rw [privateLength, scalarSize]
  rw [WP.seq_iff]
  refine WP.mono_syms (importAt_ok v 1 40 44 contextV.toContext stable (by simp [h40]) (by simp [h44]) readyV (by decide) (by decide)
    scalarV (by rw [scalarSize]; have := p.minLength; omega_using [this]) (by rw [scalarSize]; exact p.width.2.2.2.1) count) ?_
  rintro w ⟨contextW0, readyW, x, keepsW, frameW, restW⟩ symsW
  obtain contextW := contextV.after_workspace frameW restW contextW0.ptr (fun d hd => (stableSlots_at stable hd).1)
  obtain fits : arrAt p.w 8 ≤ 8 * p.len := readyW.width ▸ readyW.layout.2.2.1
  obtain modW := (keeps_array_num keepsW fits op0 (by decide)).trans modV
  obtain r2W := (keeps_array_num keepsW fits op4 (by decide)).trans r2V
  rw [WP.seq_iff]
  refine WP.mono_syms (scalarRange_ok w contextW.toContext stable (by simp [h28]) (by simp [h32]) (by simp [h60]) readyW modW odd) ?_
  rintro a ⟨contextA0, readyA, flag, arraysA, frameA, restA⟩ symsA
  obtain contextA := contextW.after_workspace frameA restA contextA0.ptr (fun d hd => (stableSlots_at stable hd).1)
  rw [x] at flag
  obtain modA := (arraysA 0 (by simp)).trans modW
  obtain r2A := (arraysA 4 (by simp)).trans r2W
  obtain scalarA := (scalarV.after_workspace frameW restW).after_workspace frameA restA
  obtain significantA := (significantV.after_workspace frameW restW).after_workspace frameA restA
  obtain outA := (((outputs.after restU).after restV).after restW).after restA
  obtain fullV : Frame (keyCallWrites p s) u.mem v.mem := frameV.sub (by
    intro r hr
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr p.privateValue, p.k⟩, by simp [keyCallWrites, keyWrites], by intro a ha; exact ha⟩)
  obtain fullA := ((fullU.trans fullV).trans (extend frameW)).trans (extend frameA)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono_syms (testFlag_ok a) ?_
  rintro z ⟨⟨zeroZ, memZ⟩, restZ⟩ symsZ
  obtain ptrZ := (restZ.gpr .r0 (by simp)).trans contextA.ptr

  obtain readyZ := readyA.of_mem memZ restZ ptrZ
  obtain frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] a.mem z.mem := by rw [memZ]; exact Frame.refl _ _
  obtain contextZ := contextA.after_workspace frameZ restZ ptrZ (fun d hd => (stableSlots_at stable hd).1)
  obtain scalarZ := scalarA.after_workspace frameZ restZ
  obtain significantZ := significantA.after_workspace frameZ restZ
  obtain outZ := outA.after restZ
  obtain environmentZ : env.holds p z := env.stable environment
    (fullA.trans (extend frameZ))
    ((((restU.trans restV).trans restW).trans restA).trans (restZ.mono (by simp [roundClobbers])))
    (symsZ.trans (symsA.trans (symsW.trans (symsV.trans symsU))))
  by_cases valid : sampleScalarValid p (layout p) rb
  · refine WP.ite true (by change some (!z.z) = some true; rw [zeroZ, flag, scalarValidFlag, ite_eq_left (show 0 < Spec.Rsa.os2ip ((layout p).encode rb) ∧ Spec.Rsa.os2ip ((layout p).encode rb) < scalarBound p from valid)]; rfl) ?_ (by intro hf; cases hf)
    intro _
    refine WP.mono (law.correct z contextZ environmentZ
      (((((calls.after restU).after restV).after restW).after restA).after restZ) stable h52 h4 h32
      h36 h40 h56 saved readyZ (by rw [memZ]; exact modA) odd
      (by rw [memZ]; exact r2A) scalarZ scalarSize (layoutBound p rb size) significantZ
      (by rw [List.length_drop, scalarSize]; rfl) ((layout p).encode_significant rb) outZ outputY) ?_
    rintro t ⟨status, privateT, publicT, frameT⟩
    refine ⟨by rw [sampleMainFlag, ite_eq_left valid]; exact status,
      by simpa only [sampleSuccess, decide_eq_true valid, Bool.true_and] using privateT,
      by simpa only [sampleSuccess, decide_eq_true valid, Bool.true_and] using publicT, ?_⟩
    obtain same : Frame (keyCallWrites p s) z.mem t.mem := by
      simpa only [keyCallWrites, keyWrites, restZ.sp, restA.sp, restW.sp, restV.sp, restU.sp] using frameT
    exact (fullA.trans (extend frameZ)).trans same
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right (show ¬(0 < Spec.Rsa.os2ip ((layout p).encode rb) ∧ Spec.Rsa.os2ip ((layout p).encode rb) < scalarBound p) from valid)]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (keyFail_ok z contextZ.toArgumentMemory (fun d hd => (stableSlots_at stable hd).1)
      (by simp [h32]) (by simp [h36]) (by simp [h40]) outZ) ?_
    rintro t ⟨status, privateT, publicT, frameT⟩
    refine ⟨by rw [sampleMainFlag, ite_eq_right valid]; exact status,
      by simpa only [sampleSuccess, decide_eq_false valid, Bool.false_and, Bool.false_eq_true, ite_false] using privateT,
      by simpa only [sampleSuccess, decide_eq_false valid, Bool.false_and, Bool.false_eq_true, ite_false] using publicT, ?_⟩
    exact (fullA.trans (extend frameZ)).trans (frameT.mono (by simp [keyCallWrites, keyWrites]))

end VG.Proof.Ffdh.Arm

end

end

/-! Cached key attempts retain the established outer frame and callee stack bound. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateBody.lean`, which only this module imported.
section

/-! Checked cached domains need only the shared native argument setup prefix. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateBody_ok (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) <
        2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s) (calls : KeyCallMemory p s)
    (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (special : sampleSlots slots)
    (valid : Spec.Rsa.modulusValid p.P p.k = true)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.CachedKeyGenerate.body prepare sample tail) s fun t =>
      sampleResult p (layout p) rb t ∧ Frame (keyCallWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.CachedKeyGenerate.body, WP.seq_iff]
  refine WP.mono_syms (headPrefix_ok s h stable h0 h24 h32) ?_
  rintro u ⟨contextU, _, _, frameU, restU⟩ symsU
  obtain fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  obtain environmentU := env.stable environment fullU restU symsU
  obtain entropyU := entropy.after_frame frameU restU (by simpa only [List.mem_singleton, forall_eq, size] using entropyStack)
  obtain facts := VG.Proof.Bignum.valid_facts valid p.minLength
  obtain stableU : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    simp only [Bool.true_and, stable]
  refine WP.mono (environmentKeyGenerateMain_ok prepare sample tail env layout prep sampler law layoutBound u
    contextU environmentU (calls.after restU) stableU
    (by simp [h52]) (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
    (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48]) (by simp) (by simp)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact saved d hd)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact special d hd)
    facts.2.1 facts.1 facts.2.2 entropyU size (by rw [restU.sp]; exact entropyStack)
    (outputs.after restU) entropySep privateLength outputY) ?_
  rintro t ⟨status, privateT, publicT, frameT⟩
  exact ⟨⟨status, privateT, publicT⟩,
    fullU.trans (by simpa only [keyCallWrites, keyWrites, restU.sp] using frameT)⟩

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateEntered_ok (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) <
        2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (s : State) {p : Inputs} {rb : List Byte} (h : ArgumentMemory p [] s)
    (environment : env.holds p s) (calls : KeyCallMemory p s) (incoming : KeyIncoming p s)
    (cache : IncomingWord p.cachedContext 156 s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (valid : Spec.Rsa.modulusValid p.P p.k = true)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry)
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.body prepare sample tail)) s fun t =>
      sampleResult p (layout p) rb t ∧ Frame (keyCallWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (cachedKeyGenerateEntry_ok s h incoming cache privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩ symsU
  obtain fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  obtain environmentU := env.stable environment fullU (restU.mono (by simp [roundClobbers])) symsU
  obtain entropyU := entropy.after_frame frameU restU (by simpa only [List.mem_singleton, forall_eq, size] using entropyStack)
  refine WP.mono (cachedKeyGenerateBody_ok prepare sample tail env layout prep sampler law layoutBound u
    contextU environmentU (calls.after restU) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd; revert d; decide) (by intro d hd; revert d; decide)
    valid entropyU size (by rw [restU.sp]; exact entropyStack)
    (outputs.after restU) entropySep privateLength outputY) ?_
  rintro t ⟨result, frameT⟩
  exact ⟨result, fullU.trans (by simpa only [keyCallWrites, keyWrites, restU.sp] using frameT)⟩

structure CachedKeyGenerateFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop where
  input : KeyGenerateFnInput p rb s
  cache : IncomingWord p.cachedContext 156 (entered s)

theorem cachedKeyGenerateFn_ok (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) <
        2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (s : State) {p : Inputs} {rb : List Byte} (h : CachedKeyGenerateFnInput p rb s)
    (environment : env.holds p (entered s)) (valid : Spec.Rsa.modulusValid p.P p.k = true) :
    WP isa (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) s fun t =>
      abiPreserved s t ∧ sampleResult p (layout p) rb t := by
  unfold VG.Impl.Ffdh.Arm.CachedKeyGenerate.code
  refine framed_of_separate _ s h.input.stackFits (keyCallWrites p (entered s))
    (fun m status =>
      status = sampleMainFlag p (layout p) rb ∧ Spec.Rsa.bytesAt m (State.addr p.privateValue) p.k =
        (if sampleSuccess p (layout p) rb then (layout p).encode rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.publicValue) p.k =
        (if sampleSuccess p (layout p) rb then Spec.Rsa.i2osp (keyPower p ((layout p).encode rb)) p.k else List.replicate p.k 0)) ?_ ?_
    (hQ := ?_)
  rotate_right
  · intro m₁ m₂ status hf ⟨st, priv, pub⟩
    have o := h.input.outputs
    have sep : ∀ a ∈ [p.privateValue, p.publicValue], ∀ r ∈ released s,
        (⟨State.addr a, p.k⟩ : Region).Disjoint r := by
      intro a ha r hr
      simp only [released, List.mem_cons, List.not_mem_nil, or_false] at hr ha
      rcases ha with rfl | rfl <;> rcases hr with rfl | rfl
      · exact (h.input.saved _ (by simp [keyWrites])).symm
      · exact o.privateStack.symm
      · exact (h.input.saved _ (by simp [keyWrites])).symm
      · exact o.publicStack.symm
    have fit : p.k < 2 ^ 64 := by have := o.privateBuffer.fits; omega_using [this]
    exact ⟨st, Eq.trans (VG.Proof.Bignum.Arm.rsa_bytes_frame hf fit (sep _ (by simp))) priv,
      Eq.trans (VG.Proof.Bignum.Arm.rsa_bytes_frame hf fit (sep _ (by simp))) pub⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.input.saved r hr
    · have eq := List.mem_singleton.mp hr; subst r; exact h.input.savedCall
  refine WP.mono (cachedKeyGenerateEntered_ok prepare sample tail env layout prep sampler law layoutBound (entered s)
    h.input.args environment h.input.calls h.input.incoming h.cache h.input.privateValue h.input.publicValue
    h.input.outputY h.input.privateLength valid h.input.entropy h.input.size h.input.entropyStack
    h.input.outputs h.input.entropySep) ?_
  rintro t ⟨result, frameT⟩
  exact ⟨frameT, result⟩

end VG.Proof.Ffdh.Arm

end

end

/-! The cached signature extends the established attempt's read-only arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def cachedPlainState (s : State) : State :=
  s.withRegions [⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
    ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,⟨stackArgAddr s 0,28⟩] s.wr

theorem cachedKeyGenerate_plain_pre (s : State)
    (pre : (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
    (Spec.Ffdh.generateKeyContract abi 176).pre (cachedPlainState s) := by
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig,
    Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit,argFit,_rd,wr,xY,xDom,xRand,xS,_xCtx,xArgs,yDom,yRand,yS,_yCtx,yArgs,
    domS,randS,_sCtx,sArgs,stackX,stackY,stackDom,stackRand,stackS,_stackCtx,stackArgs,
    xFit,yFit,domFit,randFit,sFit,_ctxFit,bounds,domainLen,xLen,yLen,rLen,space,_valid,_canonical⟩ := pre
  have inner : (⟨stackArgAddr s 0,28⟩ : Region).Sub ⟨stackArgAddr s 0,36⟩ := by
    simpa only [VG.Proof.Mont.off,BitVec.add_zero] using Offset.sub_base (stackArgAddr s 0) (by decide : 0+28≤36)
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs,
    reduceClassify, Loc.val, State.addr]
  exact ⟨stackFit,by omega_using [argFit],rfl,wr,xY,xDom,xRand,xS,
    xArgs.sub_right inner,yDom,yRand,yS,yArgs.sub_right inner,domS,randS,sArgs.sub_right inner,
    stackX,stackY,stackDom,stackRand,stackS,stackArgs.sub_right inner,
    xFit,yFit,domFit,randFit,sFit,bounds,domainLen,xLen,yLen,rLen,space⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.KeyGeneratePre`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeyPre`, which this module and modules that import it used -/

section

/-! The shared key-generation signature supplies native entropy and writable key buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem key_input (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 128).pre s)
    {p : Inputs} {rb : List Byte}
    (base : stackArg s 5 = p.base) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (domain : stackArg s 0 = p.domain)
    (count : (stackArg s 2).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (entropy : stackArg s 3 = p.entropy) (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb) :
    KeyFnInput p rb s := by
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre

  obtain ⟨stackFit, argFit, rd, wr, xY, xDom, xRand, xS, xArgs, yDom, yRand, yS, yArgs,
    domS, randS, sArgs, stackX, stackY, stackDom, stackRand, stackS, stackArgs,
    xFit, yFit, domFit, randFit, sFit, _, _, xLen, yLen, rLen, _⟩ := pre
  have domLen : (stackArg s 1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have randLength : rb.length = p.k := by
    have eq := congrArg List.length entropyBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [count] at xLen yLen rLen
  rw [xLen] at wr xY xDom xRand xS xArgs stackX xFit
  rw [yLen] at wr xY yDom yRand yS yArgs stackY yFit
  rw [rLen] at rd xRand yRand randS stackRand randFit
  rw [privateValue] at wr xY xDom xRand xS xArgs stackX xFit
  rw [publicValue] at wr xY yDom yRand yS yArgs stackY yFit
  rw [domain, domLen] at rd xDom yDom domS stackDom domFit
  rw [entropy] at rd xRand yRand randS stackRand randFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr xS yS domS randS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackX stackY stackDom stackRand stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have entropyRead : InRegions (s.rd ++ s.wr) (State.addr p.entropy) p.k :=
    ⟨⟨State.addr p.entropy, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootEntropy : Octets p.base p.entropy p.len rb s :=
    ⟨by rw [randLength]; exact randFit, by rw [randLength]; exact entropyRead,
      by rw [randLength]; exact randS, by rw [randLength]; exact entropyBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets rootDomain stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 7) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega_using [argFit, hi])
  have argSub (i : Nat) (hi : i < 7) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 28⟩ := by
    rw [argStart, argAddr i hi]
    exact Offset.sub_base _ (by omega_using [hi])
  have incoming (i : Nat) (hi : i < 7) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s stackFit (by omega_using [argFit, hi])
      ⟨⟨stackArgAddr s 0, 28⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
      (stackArgs.sub_right (argSub i hi)) rfl
  have nativeIncoming : KeyIncoming p (entered s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← domain]; exact incoming 0 (by decide)
    · have h := incoming 1 (by decide)
      rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · have h := incoming 2 (by decide)
      rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← entropy]; exact incoming 3 (by decide)
    · rw [← base]; exact incoming 5 (by decide)
  have xWrite : InRegions (entered s).wr (State.addr p.privateValue) p.k :=
    ⟨⟨State.addr p.privateValue, p.k⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
  have yWrite : InRegions (entered s).wr (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
  have outputs : KeyOutputs p (entered s) :=
    ⟨⟨xFit, xWrite⟩, ⟨yFit, yWrite⟩, xDom.symm, yDom.symm,
      stackX.sub_left (locals_sub_reserved s stackFit), stackY.sub_left (locals_sub_reserved s stackFit),
      xS, yS, xY⟩
  refine ⟨stackFit, args, nativeIncoming, privateValue, publicValue, outputY, privateLength,
    entered_octets rootEntropy stackFit (by rw [randLength]; exact stackRand), randLength,
    stackRand.symm.sub_right (locals_sub_reserved s stackFit), outputs, xRand.symm, ?_⟩
  intro r hr
  simp only [keyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact stackS.sub_left (saved_sub_reserved s stackFit)
  · exact saved_separate_locals s stackFit
  · exact stackX.sub_left (saved_sub_reserved s stackFit)
  · exact stackY.sub_left (saved_sub_reserved s stackFit)

end VG.Proof.Ffdh.Arm

end

end

/-! The enlarged stack reservation supplies the shared arithmetic calls. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem keyGenerate_pre128 (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s) :
    (Spec.Ffdh.generateKeyContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, xY, xDom, xRand, xS, xArgs, yDom, yRand, yS, yArgs,
    domS, randS, sArgs, stackX, stackY, stackDom, stackRand, stackS, stackArgs,
    xFit, yFit, domFit, randFit, sFit, bounds, domainLen, xLen, yLen, rLen, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega_arith, argFit, rd, wr, xY, xDom, xRand, xS, xArgs, yDom, yRand, yS, yArgs,
    domS, randS, sArgs, stackX.sub_left inner, stackY.sub_left inner, stackDom.sub_left inner,
    stackRand.sub_left inner, stackS.sub_left inner, stackArgs.sub_left inner,
    xFit, yFit, domFit, randFit, sFit, bounds, domainLen, xLen, yLen, rLen, space⟩

theorem keyGenerate_input (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s)
    {p : Inputs} {rb : List Byte}
    (base : stackArg s 5 = p.base) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (domain : stackArg s 0 = p.domain)
    (count : (stackArg s 2).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (entropy : stackArg s 3 = p.entropy) (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb) :
    KeyGenerateFnInput p rb s := by
  have old := key_input s (keyGenerate_pre128 s pre) base privateValue publicValue domain count capacity
    entropy outputY privateLength domainBytes entropyBytes
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stackX, stackY, stackDom, stackRand, stackS, _,
    _, _, _, _, _, _, _, xLen, yLen, rLen, _⟩ := pre
  have domLen : (stackArg s 1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [count] at xLen yLen rLen
  rw [xLen, privateValue] at stackX
  rw [yLen, publicValue] at stackY
  rw [domain, domLen] at stackDom
  rw [rLen, entropy] at stackRand
  rw [base, capacity, Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackX stackY stackDom stackRand stackS
  have calls := KeyCallMemory.of_outer stackFit (entered_sp s) stackS stackDom.symm stackX.symm stackY.symm stackRand.symm old.outputs.privateBuffer.fits
  refine ⟨old, calls, ?_⟩
  have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
  have fit : (entered s).sp.toNat + 72 < 2 ^ 32 := by
    rw [entered_nat s (by omega_arith)]; have := s.sp.isLt; omega_arith
  rw [shifted, VG.Arm.addr_add fit, belowA, addr_sub' calls.stack.fit]
  exact (Offset.disjoint_below_above _ (m := 48) (a := 72) (l := 56) (by decide)).symm

end VG.Proof.Ffdh.Arm

end

end

/-! The extended signature supplies the cached attempt's native input record. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateLift.lean`, which only this module imported.
section

/-! Appending the immutable context only enlarges the attempt's readable memory. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem plainRead {s : State} {a : Addr} {n : Nat}
    (rd : s.rd=[⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
      ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,
      ⟨State.addr (stackArg s 7),(stackArg s 8).toNat*8⟩,⟨stackArgAddr s 0,36⟩])
    (h : InRegions ((entered (cachedPlainState s)).rd++(entered (cachedPlainState s)).wr) a n) :
    InRegions ((entered s).rd++(entered s).wr) a n := by
  obtain ⟨r,member,contains⟩ := h
  rcases List.mem_append.mp member with read|write
  · change r∈[⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
      ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,⟨stackArgAddr s 0,28⟩] at read
    simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with rfl|rfl|rfl
    · exact ⟨_,List.mem_append_left _ (by change _∈s.rd; rw [rd]; simp),contains⟩
    · exact ⟨_,List.mem_append_left _ (by change _∈s.rd; rw [rd]; simp),contains⟩
    · refine ⟨⟨stackArgAddr s 0,36⟩,List.mem_append_left _ (by change _∈s.rd; rw [rd]; simp),?_⟩
      simp only [Region.Contains] at contains ⊢
      omega
  · exact ⟨r,List.mem_append_right _ write,contains⟩

theorem cachedKeyGenerate_lift {s : State} {p : Inputs} {rb : List Byte}
    (rd : s.rd=[⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
      ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,
      ⟨State.addr (stackArg s 7),(stackArg s 8).toNat*8⟩,⟨stackArgAddr s 0,36⟩])
    (h : KeyGenerateFnInput p rb (cachedPlainState s)) : KeyGenerateFnInput p rb s := by
  have octets {base src : BitVec 32} {len : Nat} {bs : List Byte}
      (v : Octets base src len bs (entered (cachedPlainState s))) : Octets base src len bs (entered s) :=
    ⟨v.fits,plainRead rd v.readable,v.separate,v.bytes⟩
  have incoming {value : BitVec 32} {d : Nat}
      (v : IncomingWord value d (entered (cachedPlainState s))) : IncomingWord value d (entered s) :=
    ⟨v.fits,plainRead rd v.readable,v.word⟩
  refine ⟨⟨h.stackFits,?_,?_,h.privateValue,h.publicValue,h.outputY,h.privateLength,
    octets h.entropy,h.size,h.entropyStack,?_,h.entropySep,h.saved⟩,?_,h.savedCall⟩
  · exact ⟨h.args.workspace.congr rfl,⟨h.args.locals.space.congr rfl,h.args.locals.separate⟩,
      octets h.args.domain,h.args.domainStack,h.args.saved⟩
  · exact ⟨incoming h.incoming.domain,incoming h.incoming.domainLength,incoming h.incoming.count,
      incoming h.incoming.entropy,incoming h.incoming.scratch⟩
  · exact ⟨⟨h.outputs.privateBuffer.fits,h.outputs.privateBuffer.writable⟩,
      ⟨h.outputs.publicBuffer.fits,h.outputs.publicBuffer.writable⟩,h.outputs.privateDomain,
      h.outputs.publicDomain,h.outputs.privateStack,h.outputs.publicStack,
      h.outputs.privateWorkspace,h.outputs.publicWorkspace,h.outputs.separate⟩
  · exact ⟨⟨h.calls.stack.fit,h.calls.stack.separate⟩,h.calls.domain,h.calls.privateValue,
      h.calls.publicValue,h.calls.entropy,h.calls.privateFits⟩

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem cachedKeyGenerate_input (s : State)
    (pre : (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre s) {p : Inputs} {rb : List Byte}
    (base : stackArg s 5=p.base) (privateValue : s.gpr .r0=p.privateValue)
    (publicValue : s.gpr .r2=p.publicValue) (domain : stackArg s 0=p.domain)
    (count : (stackArg s 2).toNat=p.k) (capacity : (stackArg s 6).toNat=p.len)
    (entropy : stackArg s 3=p.entropy) (cachePointer : stackArg s 7=p.cachedContext)
    (outputY : p.output=p.publicValue) (privateLength : p.privateLength=p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k=rb) :
    CachedKeyGenerateFnInput p rb s := by
  have plain := cachedKeyGenerate_plain_pre s pre
  have inputPlain := keyGenerate_input (cachedPlainState s) plain base privateValue publicValue domain count capacity
    entropy outputY privateLength domainBytes entropyBytes
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
  obtain ⟨stackFit,argFit,rd,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_stackArgs,_⟩ := pre
  have input := cachedKeyGenerate_lift rd inputPlain
  have cache : IncomingWord p.cachedContext 156 (entered s) := by
    have address : stackArgAddr s 7=off (State.addr s.sp) 28 := VG.Arm.addr_add (by omega_using [argFit])
    have argSub : (⟨stackArgAddr s 7,4⟩ : Region).Sub ⟨stackArgAddr s 0,36⟩ := by
      rw [show stackArgAddr s 0=State.addr s.sp from by simp [stackArgAddr],address]
      exact Offset.sub_base _ (by decide)
    apply enteredIncoming s (i:=7) (by omega_using [stackFit]) (by omega_using [argFit])
    · refine ⟨⟨stackArgAddr s 0,36⟩,List.mem_append_left _ (by rw [rd]; simp),?_⟩
      rw [show stackArgAddr s 0=State.addr s.sp from by simp [stackArgAddr],address]
      exact Offset.contains_base _ (by decide) (by decide)
    · rw [belowA,addr_sub' (by omega_using [stackFit] : 128≤s.sp.toNat)]
      exact (_stackArgs.sub_left (Offset.below_mono _ (by decide : 128≤176) (by decide))).sub_right argSub
    · exact cachePointer
  exact ⟨input,cache⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CachedKeyGenerateEnvironment`, which this module and modules that import it used -/

section

/-! The canonical immutable context survives the cached attempt's entry frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem cachedKeyGenerate_environment (s : State)
    (pre : (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre s) {p : Inputs}
    (base : stackArg s 5=p.base) (privateValue : s.gpr .r0=p.privateValue)
    (publicValue : s.gpr .r2=p.publicValue) (domain : stackArg s 0=p.domain)
    (count : (stackArg s 2).toNat=p.k) (capacity : (stackArg s 6).toNat=p.len)
    (cache : stackArg s 7=p.cachedContext) (cacheWords : (stackArg s 8).toNat=p.cachedWords)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom) :
    CachedGenerationContext p (entered s) ∧ Spec.Ffdh.domainValid p.k p.dom=true := by
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
  obtain ⟨stackFit,argFit,rd,wr,_xY,_xDom,_xRand,xS,xCtx,_xArgs,_yDom,_yRand,yS,yCtx,_yArgs,
    _domS,_randS,sCtx,_sArgs,_stackX,_stackY,_stackDom,_stackRand,stackS,stackCtx,_stackArgs,
    _xFit,_yFit,_domFit,_randFit,_sFit,ctxFit,_bounds,_domainLen,xLen,yLen,_rLen,_space,valid,canonical⟩ := pre
  have frame := entered_frame s (by omega_arith)
  have size : p.cachedContext.toNat+8*p.cachedWords ≤ 2^32 := by rw [←cache,←cacheWords]; omega_arith
  have stackSep : (cachedRegion p).Disjoint (belowA s.sp 176) := by
    unfold cachedRegion
    rw [belowA,addr_sub' stackFit]
    simpa only [←cache,←cacheWords,State.addr,Nat.mul_comm 8] using stackCtx.symm
  have savedSub : (⟨State.addr (pcPushed s).sp,56⟩ : Region).Sub (belowA s.sp 176) :=
    fun a h => belowA_sub (by decide) stackFit a (saved_sub_reserved s (by omega_arith) a h)
  have words : Spec.Rsa.wordsAt (entered s).mem (State.addr p.cachedContext) p.cachedWords =
      Spec.Rsa.wordsAt s.mem (State.addr p.cachedContext) p.cachedWords := by
    unfold Spec.Rsa.wordsAt
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    apply frame.readW (r:=cachedRegion p) _ ?_ (by decide)
    · simp only [cachedRegion,Region.Contains,Offset.add_sub_cancel_left,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_arith : 8*i<2^64)]
      omega_arith
    · intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact stackSep.sub_right savedSub
  have validP : Spec.Ffdh.domainValid p.k p.dom=true := by
    change Spec.Ffdh.domainValid (stackArg s 2).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)=true at valid
    rw [count,domain,domainBytes] at valid
    exact valid
  refine ⟨⟨?_,validP,size,?_,?_⟩,validP⟩
  · unfold Spec.Ffdh.generationContextAt
    rw [words]
    change Spec.Ffdh.generationContextAt s.mem (State.addr (stackArg s 7))
      (stackArg s 8).toNat (stackArg s 2).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat) at canonical
    simpa only [Spec.Ffdh.generationContextAt,cache,cacheWords,count,domain,domainBytes] using canonical
  · apply entered_read
    refine ⟨⟨State.addr p.cachedContext,8*p.cachedWords⟩,List.mem_append_left _ ?_,Region.contains_self _ _⟩
    rw [rd]
    simp only [cache,cacheWords,State.addr,Nat.mul_comm 8,List.mem_cons]
    simp
  · intro r hr
    simp only [keyCallWrites,keyWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (rfl|rfl|rfl|rfl)|rfl
    · simpa only [cachedRegion,←cache,←cacheWords,←base,←capacity,Nat.mul_comm 8,State.addr] using sCtx.symm
    · exact stackSep.sub_right (fun a h => belowA_sub (by decide) stackFit a (locals_sub_reserved s (by omega_arith) a h))
    · simpa only [cachedRegion,←cache,←cacheWords,←privateValue,←count,←xLen,Nat.mul_comm 8,State.addr] using xCtx.symm
    · simpa only [cachedRegion,←cache,←cacheWords,←publicValue,←count,←yLen,Nat.mul_comm 8,State.addr] using yCtx.symm
    · rw [entered_sp]
      exact stackSep.sub_right (belowA_inner (a:=48) (k:=128) (by decide) stackFit)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.KeyGenerateCorrect`, which only this module used -/

section

/-! ### `Ffdh.Arm.KeyCorrect`, which only this module used -/

section

/-! The complete callable key-generation attempt satisfies the shared contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem key_data (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 128).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyFnInput p rb s := by
  have original := pre
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  have domLength : dom.length = (stackArg s 1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 5
    domain := stackArg s 0
    publicValue := s.gpr .r2
    privateValue := s.gpr .r0
    output := s.gpr .r2
    entropy := stackArg s 3
    len := (stackArg s 6).toNat
    k := (stackArg s 2).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((stackArg s 1).toNat = 3 * (stackArg s 2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let rb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 2).toNat
  exact ⟨p, rb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    key_input s original (p := p) (rb := rb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

end VG.Proof.Ffdh.Arm

end

end


/-! The complete callable key-generation attempt satisfies the shared contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerate_data (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyGenerateFnInput p rb s := by
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, old⟩ := key_data s (keyGenerate_pre128 s pre)
  exact ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, keyGenerate_input s pre base privateValue publicValue domain count capacity
      entropy old.outputY old.privateLength domainBytes entropyBytes⟩

end VG.Proof.Ffdh.Arm

end

end


/-! Cached arguments retain the original attempt geometry and add a canonical context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem cachedKeyGenerate_data (s : State)
    (pre : (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5=p.base ∧ s.gpr .r0=p.privateValue ∧
      s.gpr .r2=p.publicValue ∧ stackArg s 0=p.domain ∧ (stackArg s 2).toNat=p.k ∧
      (stackArg s 6).toNat=p.len ∧ stackArg s 3=p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k=rb ∧
      CachedKeyGenerateFnInput p rb s ∧ CachedGenerationContext p (entered s) ∧
      Spec.Ffdh.domainValid p.k p.dom=true ∧ stackArg s 7=p.cachedContext ∧
      (stackArg s 8).toNat=p.cachedWords := by
  have plain := cachedKeyGenerate_plain_pre s pre
  obtain ⟨old,rb,base,privateValue,publicValue,domain,count,capacity,entropy,domainBytes,entropyBytes,h⟩ :=
    keyGenerate_data (cachedPlainState s) plain
  let p : Inputs := {old with cachedContext:=stackArg s 7,cachedWords:=(stackArg s 8).toNat}
  have input : CachedKeyGenerateFnInput p rb s := cachedKeyGenerate_input s pre base privateValue publicValue
    domain count capacity entropy rfl h.outputY h.privateLength domainBytes entropyBytes
  have environment := cachedKeyGenerate_environment s pre (p:=p)
    base privateValue publicValue domain count capacity rfl rfl domainBytes
  exact ⟨p,rb,base,privateValue,publicValue,domain,count,capacity,entropy,domainBytes,entropyBytes,
    input,environment.1,environment.2,rfl,rfl⟩

end VG.Proof.Ffdh.Arm
