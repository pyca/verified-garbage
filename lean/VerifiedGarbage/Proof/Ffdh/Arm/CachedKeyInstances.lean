module

public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepare
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareState
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarArgs
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.SamplePrefix
import VerifiedGarbage.Proof.Ffdh.Arm.SampleFirstRetained
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroOptional
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.OutputSlice
import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound
import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerMetadata
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationFacts
public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Ring
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
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import Init.Prelude
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateData
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateInput
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMain
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePre
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyState
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEntry
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateSat
import VerifiedGarbage.Proof.Bignum.Arm.CombExpChoose
import VerifiedGarbage.Proof.Bignum.Arm.CombExpLoop
import VerifiedGarbage.Proof.Bignum.Arm.CombExpInitial
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.FoldedPublic
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Impl.Bignum.Arm.CombExp
import VerifiedGarbage.Proof.Bignum.Arm.CombExpControl
import VerifiedGarbage.Proof.Bignum.Arm.CombExpStepCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpInitialCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! ### `Ffdh.Arm.SampleCut`, which only this module used -/

section

/-! ### `Ffdh.Arm.SampleSuffix`, which only this module used -/

section

/-! ### `Ffdh.Arm.CopyOptional`, which only this module used -/

section

/-! Copy the possibly empty suffix after a key scalar's masked leading byte. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem copyOptional_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (fits : n < 2 ^ 32) (sourceFits : src.toNat + n ≤ 2 ^ 32) (destFits : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) n) (write : InRegions s.wr (State.addr dst) n)
    (separate : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩)
    (source : s.gpr .r1 = src) (dest : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr VG.Impl.Bignum.Arm.copyBytes) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr src) n ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero, WP.seq_iff]
  refine WP.mono (zeroCount_ok s) ?_
  rintro u ⟨⟨zeroU, memU⟩, restU⟩
  by_cases empty : n = 0
  · subst n
    refine WP.ite true (by change some u.z = some true; rw [zeroU, count]; rfl) ?_ (by intro hf; cases hf)
    intro _
    exact WP.block_nil ⟨rfl, by rw [memU]; exact Frame.refl _ _, restU.mono (by simp)⟩
  · refine WP.ite false (by
      change some u.z = some false
      rw [zeroU, count]
      change some (BitVec.ofNat 32 n == (0 : BitVec 32)) = some false
      rw [ofNat_beq_zero fits, decide_eq_false empty]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (copyBytes_ok u (copyCtx_of_regions u src dst fits sourceFits destFits
      (by rw [restU.rd, restU.wr]; exact read) (by rw [restU.wr]; exact write) separate)
      (by omega_using [empty]) ((restU.gpr .r1 (by simp)).trans source) ((restU.gpr .r0 (by simp)).trans dest)
      ((restU.gpr .lr (by simp)).trans count)) ?_
    intro t inv
    refine ⟨?_, ?_, (restU.mono (by simp)).trans inv.rest⟩
    · unfold Spec.Rsa.bytesAt
      apply List.map_congr_left
      intro j hj
      obtain bound := List.mem_range.mp hj
      obtain byte := inv.copied j bound
      rw [addr_add (by omega_using [destFits, bound]), addr_add (by omega_using [sourceFits, bound]), memU] at byte
      exact byte
    · have frame := inv.frame destFits
      rw [memU] at frame
      exact frame

end VG.Proof.Ffdh.Arm

end

end


/-! Copy the scalar suffix after its first significant byte, including the
single-byte-bound case where the suffix is empty. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def sampleSuffix (p : Inputs) (l : ScalarLayout p) : Region :=
  ⟨off (State.addr p.privateValue) (l.lead + 1), p.k - (l.lead + 1)⟩

theorem sampleSuffix_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (h : SampleMemory p l slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 (l.lead + 1))
    (dest : s.gpr .r0 = p.privateValue + BitVec.ofNat 32 (l.lead + 1))
    (count : s.gpr .lr = BitVec.ofNat 32 (p.k - (l.lead + 1))) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr VG.Impl.Bignum.Arm.copyBytes) s fun t =>
      SampleMemory p l slots t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (sampleSuffix p l).base (sampleSuffix p l).len = rb.drop (l.lead + 1) ∧
      Frame [sampleSuffix p l] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have lead := l.lead_lt
  by_cases empty : p.k - (l.lead + 1) = 0
  · rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero, WP.seq_iff]
    refine WP.mono (zeroCount_ok s) ?_
    rintro t ⟨⟨zeroT, mem⟩, rest⟩
    refine WP.ite true (by change some t.z = some true; rw [zeroT, count, empty]; rfl) ?_ (by intro hf; cases hf)
    intro _
    apply WP.block_nil
    obtain frame : Frame [⟨State.addr p.privateValue, p.k⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
    obtain context := h.after_output frame rest domainSep stackSep saved
    obtain entropyT := entropy.after_frame frame rest (by simpa [size] using entropySep)
    refine ⟨context, entropyT, ?_, ?_, rest.mono (by simp)⟩
    · simp only [sampleSuffix, empty, Spec.Rsa.bytesAt, List.range_zero, List.map_nil]
      exact (List.drop_eq_nil_iff.mpr (by omega_using [size, empty])).symm
    · rw [mem]; exact Frame.refl _ _
  · have positive : 0 < p.k - (l.lead + 1) := by omega_using [empty]
    obtain out := output.slice positive (by omega_using [lead] : (l.lead + 1) + (p.k - (l.lead + 1)) ≤ p.k)
    obtain inp := entropy.slice positive (by omega_using [size, lead] : (l.lead + 1) + (p.k - (l.lead + 1)) ≤ rb.length)
    obtain inpSize : ((rb.drop (l.lead + 1)).take (p.k - (l.lead + 1))).length = p.k - (l.lead + 1) := by
      simp only [List.length_take, List.length_drop, size, Nat.min_self]
    obtain inpAddr := VG.Arm.addr_add (a := p.entropy) (k := l.lead + 1) (by have := entropy.fits; omega_using [size, empty, this])
    obtain outAddr := VG.Arm.addr_add (a := p.privateValue) (k := l.lead + 1) (by have := output.fits; omega_using [empty, this])
    obtain inpSub : (⟨State.addr (p.entropy + BitVec.ofNat 32 (l.lead + 1)), p.k - (l.lead + 1)⟩ : Region).Sub
        ⟨State.addr p.entropy, p.k⟩ := by rw [inpAddr]; exact Offset.sub_base _ (by omega_using [lead])
    obtain outSub : (⟨State.addr (p.privateValue + BitVec.ofNat 32 (l.lead + 1)), p.k - (l.lead + 1)⟩ : Region).Sub
        ⟨State.addr p.privateValue, p.k⟩ := by rw [outAddr]; exact Offset.sub_base _ (by omega_using [lead])
    refine WP.mono (copyOptional_ok s (by have := p.maxLength; omega_using [this]) (by simpa only [inpSize] using inp.fits) out.fits
      (by simpa only [inpSize] using inp.readable) out.writable ((entropySep.sub_left inpSub).sub_right outSub)
      source dest count) ?_
    rintro t ⟨bytes, frame, rest⟩
    obtain context := h.after_output frame rest (domainSep.sub_right outSub) (stackSep.sub_right outSub) saved
    obtain entropyT := entropy.after_frame frame rest (by simpa [size] using entropySep.sub_right outSub)
    refine ⟨context, entropyT, ?_, ?_, rest⟩
    · rw [outAddr, inpAddr] at bytes
      rw [← VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.entropy) (by omega_using [size, lead] : (l.lead + 1) + (p.k - (l.lead + 1)) ≤ rb.length), entropy.bytes] at bytes
      rw [List.take_of_length_le (by simp only [List.length_drop, size]; omega_using [])] at bytes
      exact bytes
    · simpa only [sampleSuffix, outAddr] using frame

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.KeyCutEncoding`, which only this module used -/

section

/-! Reconstruct the exact scalar encoding from the prefix, masked byte, and suffix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Proof.Mont

theorem keyCutEncoding {m : Mem} {dst : Addr} {rb : List Byte} {ld : Nat} {mask : Byte}
    (bound : ld < rb.length)
    (prefixBytes : Spec.Rsa.bytesAt m dst ld = List.replicate ld 0)
    (firstByte : m (off dst ld) = rb.getD ld 0 &&& mask)
    (suffixBytes : Spec.Rsa.bytesAt m (off dst (ld + 1)) (rb.length - (ld + 1)) = rb.drop (ld + 1)) :
    Spec.Rsa.bytesAt m dst rb.length = VG.Proof.Ffdh.KeyScalar.cut rb ld mask := by
  obtain splitLength : rb.length = ld + (1 + (rb.length - (ld + 1))) := by omega_using [bound]
  rw [splitLength, VG.Proof.Dsa.Generation.bytesAt_append,
    VG.Proof.Dsa.Generation.bytesAt_append, prefixBytes]
  obtain one : Spec.Rsa.bytesAt m (off dst ld) 1 = [rb.getD ld 0 &&& mask] := by
    simpa only [Spec.Rsa.bytesAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, BitVec.add_zero, List.nil_append] using congrArg (fun b : Byte => [b]) firstByte
  rw [one]
  obtain ptr : off (off dst ld) 1 = off dst (ld + 1) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  change List.replicate ld 0 ++ ([rb.getD ld 0 &&& mask] ++
    Spec.Rsa.bytesAt m (off (off dst ld) 1) (rb.length - (ld + 1))) = _
  rw [ptr, suffixBytes]
  rfl

end VG.Proof.Ffdh.Arm

end

end


/-! Native entropy cutting produces exactly the shared scalar encoding. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem sampleCut_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (h : SampleMemory p l slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy) (dest : s.gpr .r0 = p.privateValue)
    (count : s.gpr .lr = BitVec.ofNat 32 l.lead) (zero : s.gpr .r2 = 0) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy s fun t =>
      SampleMemory p l slots t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        VG.Proof.Ffdh.KeyScalar.cut rb l.lead (l.mask.setWidth 8) ∧
      Frame [⟨State.addr p.privateValue, p.k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  have lead := l.lead_lt
  have bounds := p.maxLength
  obtain prefixSub : (⟨State.addr p.privateValue, l.lead⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ :=
    Region.sub_prefix (by omega_using [lead])
  obtain suffixSub : (sampleSuffix p l).Sub ⟨State.addr p.privateValue, p.k⟩ :=
    Offset.sub_base _ (by omega_using [lead])
  obtain firstAddr : State.addr l.start = off (State.addr p.privateValue) l.lead :=
    VG.Arm.addr_add (by have := output.fits; omega_using [lead, this])
  obtain firstSub : (⟨State.addr l.start, 1⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ := by
    rw [firstAddr]
    exact Offset.sub_base _ (by omega_using [lead])
  obtain prefixFirst : (⟨State.addr p.privateValue, l.lead⟩ : Region).Disjoint ⟨State.addr l.start, 1⟩ := by
    rw [firstAddr]
    exact (Offset.disjoint_base _ (by omega_using []) (by omega_using [lead, bounds])).symm
  obtain prefixSuffix : (⟨State.addr p.privateValue, l.lead⟩ : Region).Disjoint (sampleSuffix p l) :=
    (Offset.disjoint_base _ (by omega_using []) (by omega_using [lead, bounds])).symm
  obtain firstSuffix : (⟨State.addr l.start, 1⟩ : Region).Disjoint (sampleSuffix p l) := by
    rw [firstAddr]
    exact Offset.disjoint _ (Or.inl (by omega_using [])) (by omega_using [lead, bounds]) (by omega_using [lead, bounds])
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy, WP.seq_iff]
  refine WP.mono (samplePrefix_ok s h saved output domainSep stackSep source dest count zero) ?_
  rintro u ⟨contextU, bytesU, ptrU, srcU, frameU, restU⟩
  obtain entropyU := entropy.after_frame frameU restU (by simpa [size] using entropySep.sub_right prefixSub)
  rw [WP.seq_iff]
  refine WP.mono (sampleFirst_retained u contextU saved entropyU size (output.after restU)
    domainSep (by rw [restU.sp]; exact stackSep) entropySep srcU ptrU) ?_
  rintro v ⟨contextV, entropyV, byteV, ptrV, srcV, countV, frameV, restV⟩
  obtain suffixCount : v.gpr .lr = BitVec.ofNat 32 (p.k - (l.lead + 1)) := by
    rw [countV]
    congr 1
  refine WP.mono (sampleSuffix_ok v contextV saved entropyV size ((output.after restU).after restV)
    domainSep (by rw [restV.sp, restU.sp]; exact stackSep) entropySep srcV ptrV suffixCount) ?_
  rintro t ⟨contextT, entropyT, suffix, frameT, restT⟩
  obtain prefixV : Spec.Rsa.bytesAt v.mem (State.addr p.privateValue) l.lead = List.replicate l.lead 0 := by
    rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frameV (by omega_using [lead, bounds]) (by simpa using prefixFirst)]
    exact bytesU
  obtain prefixT : Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) l.lead = List.replicate l.lead 0 := by
    rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frameT (by omega_using [lead, bounds]) (by simpa using prefixSuffix)]
    exact prefixV
  obtain byteT : t.mem (State.addr l.start) = rb.getD l.lead 0 &&& l.mask.setWidth 8 := by
    obtain same := frameT.bytes (R := ⟨State.addr l.start, 1⟩) (by simpa using firstSuffix) (by change 1 ≤ 2 ^ 64; decide) (i := 0) (by change 0 < 1; decide)
    simp only [BitVec.add_zero] at same
    exact same.trans byteV
  obtain encoded := keyCutEncoding (by omega_using [size, lead] : l.lead < rb.length) prefixT (by rw [← firstAddr]; exact byteT)
    (by simpa only [size, sampleSuffix] using suffix)
  obtain fullU : Frame [⟨State.addr p.privateValue, p.k⟩] s.mem u.mem :=
    frameU.sub (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact ⟨_, by simp, prefixSub⟩)
  obtain fullV : Frame [⟨State.addr p.privateValue, p.k⟩] u.mem v.mem :=
    frameV.sub (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact ⟨_, by simp, firstSub⟩)
  obtain fullT : Frame [⟨State.addr p.privateValue, p.k⟩] v.mem t.mem :=
    frameT.sub (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact ⟨_, by simp, suffixSub⟩)
  exact ⟨contextT, entropyT, by simpa only [size] using encoded, (fullU.trans fullV).trans fullT,
    ((restU.mono (by simp)).trans restV).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.SampleScalarCT`, which only this module used -/

section

/-! Public scalar layouts determine sampling addresses and loop counts. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleCutCT.lean`, which only this module imported.
section

/-! Entropy cutting uses the same public prefix and suffix lengths for different
secret tapes; no secret byte determines an address or loop count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure SampleCutMemory (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : SampleMemory p l slots s
  entropy : Octets p.base p.entropy p.len rb s
  outputs : KeyOutputs p s

structure SampleCutStart (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleCutMemory p l slots rb s where
  dest : s.gpr .r0 = p.privateValue
  source : s.gpr .r1 = p.entropy
  count : s.gpr .lr = BitVec.ofNat 32 l.lead
  zero : s.gpr .r2 = 0

structure SampleFirstStart (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleCutMemory p l slots rb s where
  dest : s.gpr .r0 = l.start
  source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 l.lead

structure SampleCopyStart (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleCutMemory p l slots rb s where
  dest : s.gpr .r0 = p.privateValue + BitVec.ofNat 32 (l.lead + 1)
  source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 (l.lead + 1)
  count : s.gpr .lr = BitVec.ofNat 32 (l.width - 1)

theorem samplePrefix_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : SampleCutStart p l slots rb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) s (SampleFirstStart p l slots rb) := by
  refine WP.mono (samplePrefix_ok s h.context saved h.outputs.privateBuffer h.outputs.privateDomain h.outputs.privateStack
    h.source h.dest h.count h.zero) ?_
  rintro t ⟨context, _, dest, source, frame, rest⟩
  obtain entropy := h.entropy.after_frame frame rest (by
    simpa [size] using entropySep.sub_right (Region.sub_prefix (by have := l.lead_lt; omega_using [this])))
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source⟩

theorem sampleFirst_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : SampleFirstStart p l slots rb s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) s (SampleCopyStart p l slots rb) := by
  refine WP.mono (sampleFirst_retained s h.context saved h.entropy size h.outputs.privateBuffer
    h.outputs.privateDomain h.outputs.privateStack entropySep h.source h.dest) ?_
  rintro t ⟨context, entropy, _, dest, source, count, _, rest⟩
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source, count⟩

theorem sampleCut_ct {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb1 rb2 : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    RelCT isa (fun s t => SampleCutStart p l slots rb1 s ∧ SampleCutStart p l slots rb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy (fun _ _ => True) := by
  have leading := keyPrefix_ct.mono
    (P' := fun (s t : State) => SampleCutStart p l slots rb1 s ∧ SampleCutStart p l slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.count.trans h.2.1.count.symm) (fun _ _ h => h)
  have first := keyFirst_ct.mono
    (P' := fun (s t : State) => SampleFirstStart p l slots rb1 s ∧ SampleFirstStart p l slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.source.trans h.2.1.source.symm, h.2.2⟩) (fun _ _ h => h)
  have copy := keyCopy_ct.mono
    (P' := fun (s t : State) => SampleCopyStart p l slots rb1 s ∧ SampleCopyStart p l slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.source.trans h.2.1.source.symm
      · exact h.1.count.trans h.2.1.count.symm) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy
  exact relCT_chain leading (samplePrefix_next · saved size1 entropySep) (samplePrefix_next · saved size2 entropySep)
    (relCT_chain first (sampleFirst_next · saved size1 entropySep) (sampleFirst_next · saved size2 entropySep) copy)

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure SampleBoundReady (p : Inputs) (l : ScalarLayout p) (slots : List Nat)
    (rb : List Byte) (s : State) : Prop extends KeyScalarInput p slots rb s where
  width : s.mem.readW (off (State.addr s.sp) 20) 32 = BitVec.ofNat 32 l.width
  mask : s.mem.readW (off (State.addr s.sp) 68) 32 = l.mask

theorem sampleScalarArgs_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h48 : 48 ∈ slots)
    (size : rb.length = p.k) (h : SampleBoundReady p l slots rb s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) s (SampleCutStart p l slots rb) := by
  refine WP.mono (sampleScalarArgs_retained s h.context stable special h.width h.mask h32 h40 h48) ?_
  rintro t ⟨context, dest, source, count, zero, frame, rest⟩
  obtain entropy := h.entropy.after_frame frame rest (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r
    rw [size]
    exact h.entropyStack.sub_right (Offset.sub_base _ (by decide)))
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source, count, zero⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CachedGenerationTable`, which only this module used -/

section

/-! Canonical reusable context words are exactly the read-only native comb table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.Arm

def cachedTablePtr (p : Inputs) : BitVec 32 := p.cachedContext+BitVec.ofNat 32 (24+16*p.w)

theorem CachedGenerationContext.table {p : Inputs} {s : State} (h : CachedGenerationContext p s) :
    CombTable (cachedTablePtr p) p.w p.P p.G
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)) s := by
  obtain wPos : 0<p.w := by have := p.width.1; omega_using [this]
  obtain wordsCount : p.cachedWords=3+34*p.w := by
    rw [h.canonical.1]
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
    omega_using []
  obtain size : 8*p.cachedWords=24+272*p.w := by rw [wordsCount]; omega_using []
  obtain ptrAddr : State.addr (cachedTablePtr p)=VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w) := by
    unfold cachedTablePtr
    exact addr_add (by have := h.fit; omega_using [wPos, size, this])
  obtain ptrNat : (cachedTablePtr p).toNat=p.cachedContext.toNat+(24+16*p.w) := by
    simp only [cachedTablePtr,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := h.fit; omega_using [wordsCount, this] : 24+16*p.w<2^32)]
    exact Nat.mod_eq_of_lt (by have := h.fit; omega_using [wPos, size, this])
  refine ⟨wPos,?_,?_,?_⟩
  · rw [ptrNat]
    have := h.fit
    omega_using [size, this]
  · rw [ptrAddr]
    exact CallLay.inRegions_sub h.readable (by omega_using [wordsCount]) (by omega_using [wordsCount, ptrNat])
  · intro a ha
    let E := Spec.Rsa.powMod p.G
      (Spec.Rsa.FixedBaseComb.exponent (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)) a) p.P *
      2^(64*p.w)%p.P
    obtain modValid := VG.Proof.Ffdh.domainValid_mod h.valid
    obtain pPos : 0<p.P := by have := (valid_facts modValid p.minLength).2.1; exact Nat.lt_trans (by decide) this
    obtain pBound : p.P<2^(64*p.w) := by
      obtain v := os2ip_lt (p.dom.take p.k)
      rw [p.pLength,pow256_eq] at v
      exact Nat.lt_of_lt_of_le v (Nat.pow_le_pow_right (by decide) (by have := p.width.2.2.2.1; omega_using [this]))
    obtain eBound : E<2^(64*p.w) := Nat.lt_trans (Nat.mod_lt _ pPos) pBound
    have limb (i : Nat) (hi : i<p.w) :
        s.mem.readW (VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w+8*p.w*a+8*i)) 64 =
          BitVec.ofNat 64 (E/2^(64*i)) := by
      let index := 3+(2+a)*p.w+i
      obtain mulA : (2+a)*p.w≤33*p.w := Nat.mul_le_mul_right _ (by omega_using [ha])
      obtain indexFit : index<p.cachedWords := by dsimp [index]; omega_using [wordsCount, hi, mulA]
      obtain entries := VG.Proof.Ffdh.generationValues_entry p.k p.dom a ha
      obtain entry := congrArg (fun xs : List (BitVec 64) => xs[i]?) entries
      have hik : i<Spec.Rsa.modulusWords p.k := hi
      simp only [List.getElem?_take,ite_eq_left hik,List.getElem?_drop,Spec.Rsa.toWords,
        List.getElem?_map,List.getElem?_range hik,Option.map_some] at entry
      obtain read := congrArg (fun xs : List (BitVec 64) => xs[index]?) h.words
      simp only [Spec.Rsa.wordsAt,List.getElem?_map,List.getElem?_range indexFit,Option.map_some] at read
      change some (s.mem.readW (VG.Proof.Mont.off (State.addr p.cachedContext) (8*index)) 64)=_ at read
      dsimp only [index,Inputs.w] at read
      rw [entry] at read
      obtain offset : 24+16*p.w+8*p.w*a+8*i=8*index := by dsimp [index]; ring
      rw [offset]
      exact Option.some.inj read
    obtain value : wv s.mem (State.addr p.cachedContext) (24+16*p.w+8*p.w*a) p.w=E := by
      rw [← Nat.mod_eq_of_lt eBound]
      apply wv_of_words
      intro i hi
      change (s.mem.readW (VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w+8*p.w*a+8*i)) 64).toNat=_
      rw [limb i hi,BitVec.toNat_ofNat]
    rw [← read_eq_val32,show 4*(2*p.w)=8*p.w by omega_using [],ptrAddr]
    simp only [VG.Proof.Mont.off,Offset.add_add]
    change (s.mem.read (VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w+8*p.w*a)) (8*p.w)).toNat=E
    rw [read_eq_wv]
    exact value

theorem CachedGenerationContext.tableSeparate {p : Inputs} {s : State}
    (h : CachedGenerationContext p s) : ∀ r∈keyCallWrites p s,
      (⟨State.addr (cachedTablePtr p),32*(8*p.w)⟩ : Region).Disjoint r := by
  obtain wPos : 0<p.w := by have := p.width.1; omega_using [this]
  obtain wordsCount : p.cachedWords=3+34*p.w := by
    rw [h.canonical.1]
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
    omega_using []
  obtain size : 8*p.cachedWords=24+272*p.w := by rw [wordsCount]; omega_using []
  obtain address : State.addr (cachedTablePtr p)=VG.Proof.Mont.off (State.addr p.cachedContext) (24+16*p.w) := by
    unfold cachedTablePtr
    exact addr_add (by have := h.fit; omega_using [wPos, size, this])
  obtain sub : (⟨State.addr (cachedTablePtr p),32*(8*p.w)⟩ : Region).Sub (cachedRegion p) := by
    rw [address]
    exact Offset.sub_base _ (by omega_using [wordsCount])
  intro r hr
  exact (h.separate r hr).sub_left sub

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.SampleSpec`, which only this module used -/

section

/-! The native attempt statuses and output encodings agree with the shared
FFDH specification, using subgroup closure for generated powers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem sampleMainFlag_spec (p : Inputs) (l : ScalarLayout p) (rb : List Byte) (_size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    (sampleMainFlag p l rb).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip (l.encode rb)) := by
  obtain parameters : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom) = true := by
    have h := valid
    rw [Spec.Ffdh.domainValid, Bool.and_eq_true] at h
    exact h.1
  obtain modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  obtain facts := VG.Proof.Bignum.valid_facts modulus p.minLength
  rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq parameters]
  obtain publicPower := VG.Proof.Ffdh.publicValid_power parameters (Spec.Rsa.os2ip (l.encode rb))
  obtain publicBool : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom,
      (Spec.Ffdh.domainOf p.k p.dom).g ^ Spec.Rsa.os2ip (l.encode rb) % (Spec.Ffdh.domainOf p.k p.dom).p⟩ =
      keyAccepted p (l.encode rb) := by
    obtain equiv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom,
      (Spec.Ffdh.domainOf p.k p.dom).g ^ Spec.Rsa.os2ip (l.encode rb) % (Spec.Ffdh.domainOf p.k p.dom).p⟩ = true ↔
        keyAccepted p (l.encode rb) = true := by
      rw [publicPower, p.domainP, p.domainG]
      simp only [keyAccepted, keyPower, VG.Proof.Bignum.powMod_eq, decide_eq_true_eq]
    exact Bool.eq_iff_iff.mpr equiv
  rw [publicBool]
  obtain scalarClass := p.privateValid_native (Spec.Rsa.os2ip (l.encode rb))
  by_cases scalarGood : sampleScalarValid p l rb
  · have priv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (l.encode rb)) = true :=
      scalarClass.mpr scalarGood
    rw [sampleMainFlag, ite_eq_left scalarGood, priv, ite_eq_right (by decide : ¬(true = false))]
    cases keyAccepted p (l.encode rb) <;> rfl
  · have priv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (l.encode rb)) = false := by
      cases eq : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (l.encode rb))
      · rfl
      · exact False.elim (scalarGood (scalarClass.mp eq))
    rw [sampleMainFlag, ite_eq_right scalarGood, priv, ite_eq_left rfl]
    rfl

theorem sampleMainFlag_one (p : Inputs) (l : ScalarLayout p) (rb : List Byte) :
    (sampleMainFlag p l rb).toNat = 1 ↔ sampleSuccess p l rb = true := by
  unfold sampleMainFlag sampleSuccess
  by_cases valid : sampleScalarValid p l rb <;> cases accepted : keyAccepted p (l.encode rb) <;> simp [valid]

theorem sampleOctets_encoded (p : Inputs) (l : ScalarLayout p) (rb : List Byte) (size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    l.encode rb = Spec.Rsa.i2osp (Spec.Rsa.os2ip (l.encode rb)) p.k := by
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
  rw [← l.encode_length size]
  exact (VG.Proof.Rsa.i2osp_os2ip _).symm

theorem sampleResult_spec {p : Inputs} {l : ScalarLayout p} {rb : List Byte} {t : State} (size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) (result : sampleResult p l rb t) :
    (t.gpr .r0).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip (l.encode rb)) ∧
    if Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
        (Spec.Rsa.os2ip (l.encode rb)) = 1 then
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        Spec.Rsa.i2osp (Spec.Rsa.os2ip (l.encode rb)) p.k ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Ffdh.domainOf p.k p.dom).g
          (Spec.Rsa.os2ip (l.encode rb)) (Spec.Ffdh.domainOf p.k p.dom).p) p.k
    else Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = List.replicate p.k 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k = List.replicate p.k 0 := by
  obtain ⟨status, privateT, publicT⟩ := result
  obtain statusSpec := sampleMainFlag_spec p l rb size valid
  refine ⟨by rw [status]; exact statusSpec, ?_⟩
  by_cases success : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip (l.encode rb)) = 1
  · have native := (sampleMainFlag_one p l rb).mp (statusSpec.trans success)
    rw [native, ite_eq_left rfl] at privateT publicT
    rw [ite_eq_left success]
    refine ⟨privateT.trans (sampleOctets_encoded p l rb size valid), ?_⟩
    obtain modulus := VG.Proof.Ffdh.domainValid_mod valid
    rw [p.domainP] at modulus
    obtain facts := VG.Proof.Bignum.valid_facts modulus p.minLength
    rw [publicT, keyPower, p.domainP, p.domainG]
  · have native : sampleSuccess p l rb = false := by
      apply Bool.eq_false_iff.mpr
      intro good
      exact success (statusSpec.symm.trans ((sampleMainFlag_one p l rb).mpr good))
    rw [native, ite_eq_right (by decide : ¬(false = true))] at privateT publicT
    rw [ite_eq_right success]
    exact ⟨privateT, publicT⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CachedKeyGenerateContractCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.KeyClassification`, which only this module used -/

section

/-! Status 2 discloses exactly scalar rejection, including for unchecked
parameter encodings; no other secret classification is needed for timing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem keyStatus_two_iff (a : Spec.Ffdh.Parameters) (x : Nat) :
    Spec.Ffdh.keyStatus a x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.keyStatus
  cases valid : Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.true_eq_false]
    split <;> decide

theorem keyStatus_validity_same (a : Spec.Ffdh.Parameters) (x1 x2 : Nat)
    (status : Spec.Ffdh.keyStatus a x1 = Spec.Ffdh.keyStatus a x2) :
    Spec.Ffdh.privateValid a x1 = true ↔ Spec.Ffdh.privateValid a x2 = true := by
  constructor
  · intro good
    cases other : Spec.Ffdh.privateValid a x2
    · have rejected := (keyStatus_two_iff a x1).mp (status.trans ((keyStatus_two_iff a x2).mpr other))
      rw [good] at rejected
      cases rejected
    · rfl
  · intro good
    cases other : Spec.Ffdh.privateValid a x1
    · have rejected := (keyStatus_two_iff a x2).mp (status.symm.trans ((keyStatus_two_iff a x1).mpr other))
      rw [good] at rejected
      cases rejected
    · rfl

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.KeyEntryCT`, which only this module used -/

section

/-! Key-generation entry accesses only fixed offsets of the public stack frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem keyEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry) (fun _ _ => True) := by
  obtain accesses := RelCT.block_append ((storeLocal_ct .r0 40).seq (RelCT.block_append ((storeLocal_ct .r2 36).seq (RelCT.block_append ((storeLocal_ct .r2 4).seq (RelCT.block_append ((loadLocal_ct .r3 128 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 24).seq (RelCT.block_append ((loadLocal_ct .r3 132 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 28).seq (RelCT.block_append ((loadLocal_ct .r3 136 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 32).seq (RelCT.block_append ((storeLocal_ct .r3 44).seq (RelCT.block_append ((loadLocal_ct .r3 140 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 48).seq (RelCT.block_append ((loadLocal_ct .r0 148 (by decide)).seq ((storeLocal_ct .r0 0)))))))))))))))))))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq accesses)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.SampleState`, which only this module used -/

section

/-! Native key-generation states used to compose functional and timing proofs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

structure SampleReady (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : SampleContext p l slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  scalar : Octets p.base p.privateValue p.len (l.encode rb) s
  significant : Octets p.base l.start p.len ((l.encode rb).drop l.lead) s
  outputs : KeyOutputs p s

structure SampleImported (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleReady p l slots rb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip (l.encode rb)

structure SampleRanged (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleReady p l slots rb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip (l.encode rb))

theorem SampleReady.after_mem {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte} {s t : State}
    (h : SampleReady p l slots rb s) (mem : t.mem = s.mem) (rest : Rest [] s t) : SampleReady p l slots rb t := by
  obtain ptr := (rest.gpr .r0 (by simp)).trans h.context.ptr
  obtain frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨⟨h.context.toContext.of_mem mem rest ptr, by rw [rest.sp, mem]; exact h.context.scalarStart, by rw [rest.sp, mem]; exact h.context.scalarWidth, by rw [rest.sp, mem]; exact h.context.scalarMask⟩, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩

theorem SampleRanged.after_mem {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte} {s t : State}
    (h : SampleRanged p l slots rb s) (mem : t.mem = s.mem) (rest : Rest [] s t) : SampleRanged p l slots rb t :=
  ⟨h.toSampleReady.after_mem mem rest, (rest.gpr .r11 (by simp)).trans h.flag⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Cached attempts compare independent entropy tapes under the reviewed public leakage. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateEntryCT.lean`, which only this module imported.
section

/-! Retaining the appended context reads and writes only fixed stack offsets. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry) (fun _ _ => True) := by
  obtain extra := RelCT.block_append (stackAddr_ct.seq (RelCT.block_append
    ((loadLocal_ct .r3 156 (by decide)).seq (storeLocal_ct .r3 52))))
  exact RelCT.block_append ((relCT_keep_sp keyEntry_ct (fun _ _ h => h)).seq
    (extra.mono (fun _ _ h => h) (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentSampleState.lean`, which only this module imported.
section

/-! Native key-generation states used to compose functional and timing proofs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem environmentSample_next (env : SampleEnvironment) (sample : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (sampler : EnvironmentSampleLaw env layout sample) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : KeyPrepared p slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) :
    WP isa sample s (fun t => (SampleReady p (layout p) slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  refine WP.mono_syms (sampler.correct s h.context environment normalized odd stable special h52 h0 h24 h28 h32 h40 h48 h60 h.ready h.modulus h.r2
    h.entropy size h.entropyStack h.outputs entropySep) ?_
  rintro t ⟨context, ready, modulus, r2, scalar, significant, frame, rest⟩ syms
  refine ⟨⟨⟨context, ready, modulus, r2, scalar, significant, h.outputs.after rest⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.sub (by
    intro r hr
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr p.privateValue, p.k⟩, by simp [keyCallWrites, keyWrites], fun _ hx => hx⟩)

theorem environmentImport_next (env : SampleEnvironment) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (size : rb.length = p.k) (privateLength : p.privateLength = p.k) (h : SampleReady p l slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (fun t => (SampleImported p l slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  obtain length := l.encode_length size
  refine WP.mono_syms (importAt_ok s 1 40 44 h.context.toContext stable h40 h44 h.ready (by decide) (by decide) h.scalar
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength, length])) ?_
  rintro t ⟨context, ready, imported, keeps, frame, rest⟩ syms
  obtain fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  refine ⟨⟨⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide)).trans h.modulus,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 4) (by decide)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, imported⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.mono (by simp [keyCallWrites, keyWrites])

theorem environmentRange_next (env : SampleEnvironment) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (odd : p.P % 2 = 1) (h : SampleImported p l slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (fun t => (SampleRanged p l slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  refine WP.mono_syms (scalarRange_ok s h.context.toContext stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro t ⟨context, ready, flag, arrays, frame, rest⟩ syms
  rw [h.imported] at flag
  refine ⟨⟨⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, flag⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.mono (by simp [keyCallWrites, keyWrites])

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentPrepareState.lean`, which only this module imported.
section

/-! # Modulus preparation preserves key-generation input and call geometry -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem environmentPrepare_next (env : SampleEnvironment) (prepare : Prog isa) (prep : EnvironmentPrepareLaw env prepare) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa prepare s (fun t => KeyPrepared p slots rb t ∧ KeyCallMemory p t) := by
  refine WP.mono (prep.correct s h.context environment calls stable h52 h0 h24 h32 large odd normalized) ?_
  rintro t ⟨context, ready, modulus, r2, frame, rest⟩
  obtain entropy := h.entropy.after_frame frame rest (by
    intro r hr
    simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact h.entropy.separate
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact calls.entropy)
  exact ⟨⟨⟨context, entropy, h.outputs.after rest, by rw [rest.sp]; exact h.entropyStack⟩, ready, modulus, r2⟩, calls.after rest⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentKeyGenerateMainCT.lean`, which only this module imported.
section

/-! The only secret-dependent key-generation branch is scalar acceptance,
whose classification is disclosed by the attempt's returned status. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem environmentKeyGenerateMain_ct (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare) (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k → Spec.Rsa.os2ip ((layout p).encode rb) < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (publicRelAll : ∀ s t, env.publicRel s t)
    (afterMem : ∀ {p : Inputs} {s t : State}, env.holds p s → t.mem = s.mem → VG.Proof.X25519.Arm.Rest [] s t → env.holds p t)
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (special : sampleSlots slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail) (fun _ _ => True) := by
  have preparePost (s : State) {rb : List Byte} (size : rb.length = p.k)
      (h : (KeyScalarInput p slots rb s ∧ KeyCallMemory p s) ∧ env.holds p s) :
      WP isa prepare s (fun t => (KeyPrepared p slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
    refine (environmentPrepare_next env prepare prep s stable h52 h0 h24 h32 large odd normalized size h.1.1 h.1.2 h.2).and ?_
    refine WP.mono_syms (prep.correct s h.1.1.context h.2 h.1.2 stable h52 h0 h24 h32 large odd normalized) ?_
    rintro t ⟨_, _, _, _, frame, rest⟩ syms
    apply env.stable h.2 _ rest syms
    exact frame.sub (by
      intro r hr
      simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [keyCallWrites, keyWrites], by intro a ha; exact ha⟩
      · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp [keyCallWrites], fun _ hx => hx⟩)
  obtain prepareCT : RelCT isa (fun s t =>
      ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      prepare (fun s t => ((KeyPrepared p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyPrepared p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨trace, _⟩ := prep.ct stable h52 h0 h24 h32 large odd normalized s t tr1 tr2 u v
      ⟨⟨⟨h.1.1.1.context, h.1.1.2⟩, h.1.2⟩, ⟨⟨h.2.1.1.1.context, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩ e1 e2
    obtain ⟨_, u', runU, postU⟩ := preparePost s size1 h.1
    obtain ⟨_, v', runV, postV⟩ := preparePost t size2 h.2.1
    obtain ⟨-, rfl⟩ := Exec.det e1 runU
    obtain ⟨-, rfl⟩ := Exec.det e2 runV
    exact ⟨trace, postU, postV, env.public_stable h.2.2.1 (Exec.syms e1) (Exec.syms e2),
      (Exec.sp e1).trans (h.2.2.2.trans (Exec.sp e2).symm)⟩
  obtain sampleCT := (sampler.ct stable special normalized odd h52 h0 h24 h28 h32 h40 h48 h60 size1 size2 entropySep).mono
    (P' := fun (s t : State) => ((KeyPrepared p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyPrepared p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.1.toKeyScalarInput, h.1.2⟩, ⟨h.2.1.1.1.toKeyScalarInput, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h)
  obtain sampled := (relCT_keep_sp sampleCT (fun _ _ h => h.2.2.2)).wp (fun s t h =>
    ⟨environmentSample_next env sample layout sampler s stable special h52 h0 h24 h28 h32 h40 h48 h60 size1 entropySep h.1.1.1 h.1.1.2 h.1.2 normalized odd,
     environmentSample_next env sample layout sampler t stable special h52 h0 h24 h28 h32 h40 h48 h60 size2 entropySep h.2.1.1.1 h.2.1.1.2 h.2.1.2 normalized odd⟩)
  obtain imports := (importAt_ct (p := p) (a := 1) (slot := 40) (countSlot := 44) (k := p.k) stable (by simp [h40]) (by simp [h44])
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength]) (by decide)).mono
    (P' := fun (s t : State) => ((SampleReady p (layout p) slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((SampleReady p (layout p) slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.1.context.toContext, h.1.1.1.ready⟩, ⟨h.2.1.1.1.context.toContext, h.2.1.1.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  obtain ranges := (scalarRange_ct stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd).mono
    (P' := fun (s t : State) => ((SampleImported p (layout p) slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((SampleImported p (layout p) slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.1.context.toContext, h.1.1.1.ready, h.1.1.1.modulus⟩, ⟨h.2.1.1.1.context.toContext, h.2.1.1.1.ready, h.2.1.1.1.modulus⟩, h.2.2⟩) (fun _ _ h => h)
  have sigSize {rb : List Byte} (size : rb.length = p.k) : (((layout p).encode rb).drop (layout p).lead).length = (layout p).width := by
    rw [List.length_drop, (layout p).encode_length size]
    rfl
  obtain branches : RelCT isa (fun s t => ((SampleRanged p (layout p) slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((SampleRanged p (layout p) slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag tail VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar)
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (sampleScalarValid p (layout p) rb1))
      (fun s h => by
        have f := h.1.1.flag
        change s.gpr .r11 = (if sampleScalarValid p (layout p) rb1 then 1 else 0) at f
        simpa only [decide_eq_true_eq] using f)
      (fun s h => by
        have f := h.1.1.flag
        change s.gpr .r11 = (if sampleScalarValid p (layout p) rb2 then 1 else 0) at f
        simp only [← classification] at f
        simpa only [decide_eq_true_eq] using f)
      (fun _ _ h mem rest => ⟨⟨h.1.1.after_mem mem rest, h.1.2.after rest⟩, afterMem h.2 mem rest⟩) (fun _ _ h mem rest => ⟨⟨h.1.1.after_mem mem rest, h.1.2.after rest⟩, afterMem h.2 mem rest⟩)
    · intro _
      exact (law.ct stable h52 h4 h32 h36
        h40 h56 saved (sigSize size1) (sigSize size2)
        (by rw [(layout p).encode_significant rb1]; exact layoutBound p rb1 size1)
        (by rw [(layout p).encode_significant rb2]; exact layoutBound p rb2 size2) odd outputY).mono
        (fun s t h => ⟨⟨⟨⟨h.1.1.1.context, h.1.1.1.ready, h.1.1.1.modulus, h.1.1.1.r2, h.1.1.1.significant, h.1.1.1.outputs⟩, h.1.1.2⟩, h.1.2⟩,
          ⟨⟨⟨h.2.1.1.1.context, h.2.1.1.1.ready, h.2.1.1.1.modulus, h.2.1.1.1.r2, h.2.1.1.1.significant, h.2.1.1.1.outputs⟩, h.2.1.1.2⟩, h.2.1.2⟩, publicRelAll s t, h.2.2⟩)
        (fun _ _ h => h)
    · intro _
      exact (keyFail_ct (fun d hd => (stableSlots_at stable hd).1) (by simp [h32]) (by simp [h36]) (by simp [h40])).mono
        (fun _ _ h => ⟨⟨h.1.1.1.context.toContext.toArgumentMemory, h.1.1.1.outputs⟩, ⟨h.2.1.1.1.context.toContext.toArgumentMemory, h.2.1.1.1.outputs⟩, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SampleKeyGenerate.main
  exact prepareCT.seq (sampled.seq ((relCT_chain imports
        (fun s h => environmentImport_next env s stable (by simp [h40]) (by simp [h44]) size1 privateLength h.1.1 h.1.2 h.2)
        (fun s h => environmentImport_next env s stable (by simp [h40]) (by simp [h44]) size2 privateLength h.1.1 h.1.2 h.2)
        (relCT_chain ranges
          (fun s h => environmentRange_next env s stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1.1 h.1.2 h.2)
          (fun s h => environmentRange_next env s stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1.1 h.1.2 h.2)
          branches)).mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateBodyCT.lean`, which only this module imported.
section

/-! The cached attempt uses only the native public setup prefix before sampling. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateBody_ct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (publicRelAll : ∀ s t, env.publicRel s t)
    (afterMem : ∀ {p : Inputs} {s t : State}, env.holds p s → t.mem = s.mem → VG.Proof.X25519.Arm.Rest [] s t → env.holds p t)
    {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (special : sampleSlots slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue)
    (valid : Spec.Rsa.modulusValid p.P p.k = true) :
    RelCT isa (fun s t => ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.body prepare sample tail) (fun _ _ => True) := by
  let P := fun rb s => (KeyScalarInput p slots rb s ∧ KeyCallMemory p s) ∧ env.holds p s
  let Q := fun rb s => (KeyScalarInput p (60 :: 56 :: slots) rb s ∧ KeyCallMemory p s) ∧ env.holds p s
  obtain head := (headPrefix_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => P rb1 s ∧ P rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1.1.context, h.2.1.1.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {rb : List Byte} (size : rb.length = p.k) (h : P rb s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers)) s (Q rb) := by
    refine WP.mono_syms (headPrefix_ok s h.1.1.context stable h0 h24 h32) ?_
    rintro u ⟨context, _, _, frame, rest⟩ syms
    refine ⟨⟨⟨context, h.1.1.entropy.after_frame frame rest (by simpa [size] using h.1.1.entropyStack),
      h.1.1.outputs.after rest, by rw [rest.sp]; exact h.1.1.entropyStack⟩, h.1.2.after rest⟩, ?_⟩
    exact env.stable h.2 (frame.mono (by simp [keyCallWrites, keyWrites])) rest syms
  obtain stableU : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    simp only [Bool.true_and, stable]
  obtain facts := VG.Proof.Bignum.valid_facts valid p.minLength
  obtain main := (environmentKeyGenerateMain_ct prepare sample tail env layout prep sampler law layoutBound
    publicRelAll afterMem stableU
    (by simp [h52]) (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
    (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48]) (by simp) (by simp)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact saved d hd)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact special d hd)
    size1 size2 classification entropySep privateLength outputY facts.2.1 facts.1 facts.2.2).mono
      (P' := fun (s t : State) => Q rb1 s ∧ Q rb2 t ∧ s.sp = t.sp)
      (fun s t h => ⟨h.1, h.2.1, publicRelAll s t, h.2.2⟩) (fun _ _ h => h)
  exact relCT_chain head (fun s h => wp s size1 h) (fun s h => wp s size2 h) main

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateFnCT.lean`, which only this module imported.
section

/-! Cached key-generation timing reveals only the reviewed attempt classification. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateFn_ct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (publicRelAll : ∀ s t, env.publicRel s t)
    (afterMem : ∀ {p : Inputs} {s t : State}, env.holds p s → t.mem = s.mem → VG.Proof.X25519.Arm.Rest [] s t → env.holds p t)
    {p : Inputs} {rb1 rb2 : List Byte}
    (valid : Spec.Rsa.modulusValid p.P p.k = true)
    (classification : sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2) :
    RelCT isa (fun s t => (CachedKeyGenerateFnInput p rb1 s ∧ env.holds p (entered s)) ∧
      (CachedKeyGenerateFnInput p rb2 t ∧ env.holds p (entered t)) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) (fun _ _ => True) := by
  let P := fun (rb : List Byte) (a : State) =>
    ∃ s, CachedKeyGenerateFnInput p rb s ∧ a = entered s ∧ env.holds p a
  let Q := fun (rb : List Byte) (u : State) =>
    (KeyScalarInput p [52, 0, 48, 44, 32, 28, 24, 4, 36, 40] rb u ∧ KeyCallMemory p u) ∧ env.holds p u
  have entry := cachedKeyGenerateEntry_ct.mono
    (P' := fun (s t : State) => P rb1 s ∧ P rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {rb : List Byte} (h : P rb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry) a (Q rb) := by
    obtain ⟨s, allInput, rfl, environment⟩ := h
    have input := allInput.input
    refine WP.mono_syms (withAllRest (cachedKeyGenerateEntry_ok (entered s) input.args input.incoming allInput.cache
      input.privateValue input.publicValue input.outputY input.privateLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩ syms
    refine ⟨⟨⟨context, input.entropy.after_frame frame rest (by simpa [input.size] using input.entropyStack),
      input.outputs.after rest, by rw [rest.sp]; exact input.entropyStack⟩, input.calls.after rest⟩, ?_⟩
    exact env.stable environment (frame.mono (by simp [keyCallWrites, keyWrites]))
      (rest.mono (by simp [roundClobbers])) syms
  unfold VG.Impl.Ffdh.Arm.CachedKeyGenerate.code
  apply framed_ct (fun _ _ h => ⟨h.1.1.input.stackFits, h.2.1.1.input.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  obtain body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (cachedKeyGenerateBody_ct prepare sample tail env layout prep sampler law layoutBound publicRelAll afterMem
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) (by intro d hd; revert d; decide)
      related.1.1.input.size related.2.1.1.input.size classification related.1.1.input.entropySep
      related.1.1.input.privateLength related.1.1.input.outputY valid)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1.1, rfl, related.1.2⟩,
    ⟨t, related.2.1.1, rfl, related.2.1.2⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedGenerationMemory.lean`, which only this module imported.
section

/-! The immutable canonical context survives silent argument and flag operations. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem cachedGeneration_publicRel (s t : State) : cachedGenerationEnvironment.publicRel s t := trivial

theorem cachedGeneration_afterMem {p : Inputs} {s t : State}
    (h : cachedGenerationEnvironment.holds p s) (mem : t.mem = s.mem) (rest : Rest [] s t) :
    cachedGenerationEnvironment.holds p t := by
  obtain frame : Frame (keyCallWrites p s) s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact h.after frame (rest.mono (by simp [roundClobbers]))

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_contract_ct (prepare sample tail : Prog isa)
    (prep : EnvironmentPrepareLaw cachedGenerationEnvironment prepare)
    (sampler : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample)
    (law : EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted tail) :
    ConstantTime isa (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre
      (Proof.Ffdh.cachedGenerateKeyContract abi 176).pub
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy, domainBytes, entropyBytes, allInputS,cachedS,validS,cachePointer,cacheWords⟩ := cachedKeyGenerate_data s hs
  have inputS := allInputS.input
  have randLength (a : State) (h : (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 2).toNat := by
    have h := cachedKeyGenerate_plain_pre a h
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := h
    exact length
  sig_pub [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, p4, p5, p6, p7, _, p9, p10, p11, p12⟩ := hp
  rw [randLength s hs, randLength t ht, ← p4, ← p5, ← p6, ← p7] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let rb2 := Spec.Rsa.bytesAt t.mem (State.addr p.entropy) p.k
  have allInputT := cachedKeyGenerate_input t ht (p := p) (rb := rb2)
    (p9.symm.trans base) (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
    (by rw [← p6]; exact count) (by rw [← p10]; exact capacity) (p7.symm.trans entropy) (p11.symm.trans cachePointer) inputS.outputY inputS.privateLength ?_ rfl
  · have inputT := allInputT.input
    have cachedT := (cachedKeyGenerate_environment t ht (p9.symm.trans base)
      (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
      (by rw [←p6]; exact count) (by rw [←p10]; exact capacity)
      (p11.symm.trans cachePointer) (by rw [←p12]; exact cacheWords)
      (by rw [←p5,←domain]; change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat=p.dom; rw [←domEq,domain]; exact domainBytes)).1
    have status := (List.cons.inj statusEq).1
    rw [← domEq] at status
    simp only [State.addr] at domainBytes entropyBytes
    simp only [count, domain, entropy, domainBytes, entropyBytes] at status
    change Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) =
      Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb2) at status
    rw [← ScalarLayout.vetted_value inputS.size, ← ScalarLayout.vetted_value inputT.size] at status
    have classification := keyStatus_validity_same (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip ((ScalarLayout.vetted p).encode rb))
      (Spec.Rsa.os2ip ((ScalarLayout.vetted p).encode rb2)) status
    rw [p.privateValid_native, p.privateValid_native] at classification
    have modValid := VG.Proof.Ffdh.domainValid_mod validS
    rw [p.domainP] at modValid
    exact (cachedKeyGenerateFn_ct prepare sample tail cachedGenerationEnvironment ScalarLayout.vetted
      prep sampler law CachedSample.layoutBound cachedGeneration_publicRel cachedGeneration_afterMem
      modValid classification s t tr1 tr2 u v
      ⟨⟨allInputS,cachedS⟩,⟨allInputT,cachedT⟩,sp⟩ e1 e2).1
  · rw [← p5, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes


end VG.Proof.Ffdh.Arm

end

end

/-! ### `Bignum.Arm.CombExpPhase`, which only this module used -/

section

/-! ### `Bignum.Arm.CombExpFinish`, which only this module used -/

section

/-! Decode the completed comb power with one shared Montgomery product. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem finish_ok {base : BitVec 32} {len w M g E : Nat} {P : State → Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State) (h : Power base len w M g E s) (hp : P s) :
    WP isa (A.op 6 6 7) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod g E M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧ P t ∧ TwoExp.HeaderKept base s t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (A.op_ok s 6 6 7 h.ready hp
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.one]; exact h.ready.modulus)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, pt, frame, rest⟩
  rw [h.modulus] at modulus bound value
  rw [h.one] at value
  obtain final := mont_final_factor h.coprime h.value value
  rw [Nat.mod_eq_of_lt bound, Nat.mul_one, ← powMod_eq] at final
  obtain fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  obtain r2 := (keeps_array_num keeps fits
    (q := 4) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans h.r2
  obtain one := (keeps_array_num keeps fits
    (q := 7) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans h.one
  exact ⟨ready, final, modulus, r2, one, pt, TwoExp.header_of_keeps h.ready keeps, frame, rest⟩

end VG.Proof.Bignum.Arm.CombExp

end

end


/-! The public comb schedule computes the same full scalar power as direct exponentiation. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem phase_ok {base source table : BitVec 32} {len w bytes N M g x : Nat}
    {P : State→Prop} {regions : List Region}
    (K : Kernel base source table len w bytes N M g x P regions) (s : State)
    (ready : ArithmeticReady base len w s) (hp : P s) (controls : Controls base source table bytes N s)
    (modulus : numAt s.mem (State.addr base) w 0=M) (odd : M%2=1)
    (r2 : numAt s.mem (State.addr base) w 4=2^(128*w)%M)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows N) (fits : Spec.Rsa.FixedBaseComb.rows N<2^32)
    (bound : x<2^N) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.phase K.arithmetic.op) s fun t =>
      ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 6=Spec.Rsa.powMod g x M ∧
      numAt t.mem (State.addr base) w 0=M ∧ numAt t.mem (State.addr base) w 4=2^(128*w)%M ∧
      numAt t.mem (State.addr base) w 7=1 ∧ P t ∧ Controls base source table bytes N t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.CombExp.phase,WP.seq_iff]
  refine WP.mono (initial_ok (g:=g) K.arithmetic s ready hp controls modulus odd r2) ?_
  rintro u ⟨powerU,pu,controlsU,counterU,frameU,restU⟩
  obtain start : Power base len w M g (VG.Proof.Rsa.FixedBaseComb.high N x (Spec.Rsa.FixedBaseComb.rows N)) u := by
    simpa only [VG.Proof.Rsa.FixedBaseComb.high_top] using powerU
  rw [WP.seq_iff]
  refine WP.mono (rows_ok K u positive (Nat.le_refl _) fits start pu controlsU counterU) ?_
  rintro v ⟨powerV,pv,controlsV,_,frameV,restV⟩
  rw [VG.Proof.Rsa.FixedBaseComb.high_zero N x bound] at powerV
  refine WP.mono (finish_ok K.arithmetic v powerV pv) ?_
  rintro t ⟨readyT,resultT,modT,r2T,oneT,pt,headerT,frameT,restT⟩
  exact ⟨readyT,resultT,modT,r2T,oneT,pt,controlsV.after_header headerT,
    frameU.trans (frameV.trans frameT),restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm.CombExp

end

end

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
  rw [ScalarLayout.start,VG.Arm.addr_add (by omega_using [fit, lead])]
  exact h.privateValue.sub_left (Offset.sub_base _ (by unfold ScalarLayout.width; omega_using [lead]))

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
    widthBound (by have := l.width_bounds.2; have := p.maxLength; omega_arith) scheduleFit widthFit scalarFit
  obtain source : CombDigit.Source l.start eb s := ⟨exponent.fits,exponent.readable,exponent.byte⟩
  obtain hp : CombExp.Persistent p.base l.start (table p) s.sp p.len p.w p.P p.G (bits p) eb s := by
    refine ⟨⟨calls.stack,rfl⟩,source,cached.table,?_,tableSeparate⟩
    intro r hr
    simp only [CombExp.writeRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact exponent.separate
    · rw [size]; exact significant_below calls
  rw [VG.Impl.Ffdh.Arm.CachedPower.code,WP.seq_iff]
  refine WP.mono (args_ok s context cached ready h52) ?_
  rintro u ⟨readyU,controlsU,arraysU,frameU,restU⟩
  obtain writes : Frame (CombExp.writeRegions p.base s.sp p.len) s.mem u.mem := frameU.mono (by simp [CombExp.writeRegions])
  obtain hpU := K.arithmetic.stable frameU restU hp
  obtain controls : CombExp.Controls p.base l.start (table p) eb.length (bits p) u := by
    rw [size]; exact controlsU
  refine WP.mono (CombExp.phase_ok K u readyU hpU controls
    ((arraysU 0 (by decide)).trans modulus) odd ((arraysU 4 (by decide)).trans r2)
    positive (by omega_using [scheduleFit]) scalarFit) ?_
  rintro t ⟨rd,value,m,rr,one,_,_,frameT,restT⟩
  obtain frame := writes.trans frameT
  obtain rest := restU.trans restT
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
  obtain step : ∀ k, RelCT isa (I k) (VG.Impl.Bignum.Arm.CombExp.round K1.arithmetic.op) fun u v =>
      isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
      (isa.eval .ne u=some true → ∃ m<k, I m u v) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨positiveK,boundK,fitsK,left,right,sp⟩ := h
    obtain successor : k-1+1=k := by omega_using [positiveK]
    obtain timing := relCT_keep_sp (round_ct K1 K2 ct (i:=k-1) (by omega_using [positiveK, boundK])) (fun _ _ h => h.2.2)
    obtain leftInput : RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x1 (k-1+1)) (k-1) P1 s := by
      simpa only [successor] using (show RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x1 k) (k-1) P1 s from
        ⟨left.power,left.persistent,left.controls,by simpa only [successor] using left.counter⟩)
    obtain rightInput : RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x2 (k-1+1)) (k-1) P2 t := by
      simpa only [successor] using (show RowInput base source table len w bytes N M g
        (VG.Proof.Rsa.FixedBaseComb.high N x2 k) (k-1) P2 t from
        ⟨right.power,right.persistent,right.controls,by simpa only [successor] using right.counter⟩)
    obtain ⟨trace,sp'⟩ := timing s t tr1 tr2 u v ⟨leftInput,rightInput,sp⟩ e1 e2
    obtain correct1 := round_ok K1 s (i:=k-1) (by omega_using [positiveK, boundK]) (by omega_using [fitsK]) leftInput.power leftInput.persistent
      leftInput.controls leftInput.counter
    obtain correct2 := round_ok K2 t (i:=k-1) (by omega_using [positiveK, boundK]) (by omega_using [fitsK]) rightInput.power rightInput.persistent
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
      obtain nonzero : k-1≠0 := by
        intro zero
        change some (!u.z)=some true at again
        simp only [zero1,zero,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega_using [positiveK],by omega_using [nonzero],by omega_using [boundK],by omega_using [fitsK],
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
  obtain bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  obtain input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  obtain fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.sub (by
    intro r hr
    refine ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], ?_⟩
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  obtain environmentU := environment.after fullU (restU.mono (by simp [roundClobbers]))
  refine WP.mono (cachedPrepareBody_ok u input contextU environmentU h52 stable) ?_
  rintro t ⟨contextT, readyT, modulus, r2, frameT, restT⟩
  obtain frame : Frame (keyPrepareWrites p s) s.mem t.mem :=
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
  obtain bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  obtain input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  obtain fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.sub (by
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
  obtain args := (prepareArgs_ct 24).mono
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
  obtain entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (sampleScalarArgs_retained u contextU stable special widthU maskU h32 h40 h48) ?_
  rintro v ⟨contextV, dstV, srcV, countV, zeroV, frameV, restV⟩
  obtain entropyV := entropyU.after_frame frameV restV (by
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
  obtain ptr : t.gpr .r0 = p.base := loaded.trans (contextW.saved 0 h0)
  obtain memFrame : Frame [] w.mem t.mem := by rw [memT]; exact Frame.refl _ _
  obtain args := contextW.toArgumentMemory.after_frame memFrame restT (by simp) (by simp)
  obtain contextT : SampleContext p (layout p) slots t := by
    refine ⟨⟨args, ptr⟩, ?_, ?_, ?_⟩
    · rw [memT, restT.sp]; exact contextW.scalarStart
    · rw [memT, restT.sp]; exact contextW.scalarWidth
    · rw [memT, restT.sp]; exact contextW.scalarMask
  obtain entropyT := entropyW.after_frame memFrame restT (by simp)
  obtain fullU : Frame (keyScalarWrites p s) s.mem u.mem := frameU.mono (by simp [keyScalarWrites])
  obtain fullV : Frame (keyScalarWrites p s) u.mem v.mem := by
    rw [restU.sp] at frameV
    exact frameV.mono (by simp [keyScalarWrites])
  obtain fullW : Frame (keyScalarWrites p s) v.mem w.mem := frameW.mono (by simp [keyScalarWrites])
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
  obtain readyT := ready.after_external frame workspaceSep baseSep rest context.ptr
  obtain fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  obtain scalar : Octets p.base p.privateValue p.len ((layout p).encode rb) t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [(layout p).encode_length size]; exact outputs.privateBuffer.fits
    · rw [(layout p).encode_length size, rest.rd, rest.wr]
      obtain ⟨r, hr, hc⟩ := outputs.privateBuffer.writable
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [(layout p).encode_length size]; exact outputs.privateWorkspace
    · rw [(layout p).encode_length size]; exact bytes
  obtain significant := scalar.slice (d := (layout p).lead) (k := (layout p).width) (layout p).width_bounds.1
    (by rw [(layout p).encode_length size]; unfold ScalarLayout.width; have := (layout p).lead_lt; omega_using [this])
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
  obtain entropy := h.entropy.after_frame frame rest (by
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
  obtain boundCT := (law.ct stable special normalized odd h52 h24 h28 h32 h60).mono
    (P' := fun (s t : State) => (KeyScalarInput p slots rb1 s ∧ env.holds p s) ∧ (KeyScalarInput p slots rb2 t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.context, h.1.2⟩, ⟨h.2.1.1.context, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h)
  have args := keyScalarArgs_ct.mono
    (P' := fun (s t : State) => SampleBoundReady p (layout p) slots rb1 s ∧ SampleBoundReady p (layout p) slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  obtain cut := sampleCut_ct (l := layout p) (fun d hd => (stableSlots_at stable hd).1) size1 size2 entropySep
  unfold VG.Impl.Ffdh.Arm.SampleScalar.code
  obtain bounded := (relCT_keep_sp boundCT (fun _ _ h => h.2.2.2)).wp
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
  obtain positive : 0<bits p := CachedSample.bits_positive cached
  obtain bound : bits p≤8192 := CachedSample.bits_bound p
  obtain width : eb.length=(bits p+7)/8 := size.trans (CachedSample.layout_width p positive)
  obtain small := VG.Proof.Rsa.FixedBaseComb.rows_small bound
  exact correct backend s context cached calls stable h52 ready modulus odd r2 exponent size
    (by omega_using [width]) small.2 (by omega_using [bound]) (VG.Proof.Rsa.FixedBaseComb.rows_pos positive) scalarFit
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
  obtain timing := TwoExp.sharedMontgomeryTiming base sp len w backend.name backend.mul
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
    obtain positiveBits : 0<bits p := CachedSample.bits_positive h.1.cached
    obtain boundBits : bits p≤8192 := CachedSample.bits_bound p
    obtain publicWidth : l.width=(bits p+7)/8 := CachedSample.layout_width p positiveBits
    obtain widthBound : bits p≤8*l.width := by omega_using [publicWidth]
    obtain widthFit : bits p<2^31 := by omega_using [boundBits]
    obtain bytesFit : l.width<2^32 := by
      have := l.width_bounds.2
      have := p.maxLength
      omega_using [boundBits, publicWidth]
    obtain scheduleFit := (VG.Proof.Rsa.FixedBaseComb.rows_small boundBits).2
    let K1 := CombExp.kernelAt backend p.base l.start (table p) sp0 p.len p.w l.width p.P p.G (bits p)
      eb1 size1 widthBound bytesFit scheduleFit widthFit fit1
    let K2 := CombExp.kernelAt backend p.base l.start (table p) sp0 p.len p.w l.width p.P p.G (bits p)
      eb2 size2 widthBound bytesFit scheduleFit widthFit fit2
    obtain timing : CombExp.Timing K1 K2 := CombExp.backendTiming backend p.base l.start (table p) sp0
      p.len p.w l.width p.P p.G (bits p) eb1 eb2 size1 size2 widthBound bytesFit scheduleFit widthFit fit1 fit2
    have argsReady (eb : List Byte) (size : eb.length=l.width) (a : State) (input : NativeInput p slots eb sp0 a) :
        WP isa VG.Impl.Ffdh.Arm.CachedPower.args a
          (CombExp.PhaseInput p.base l.start (table p) p.len p.w l.width (bits p) p.P
            (CombExp.Persistent p.base l.start (table p) sp0 p.len p.w p.P p.G (bits p) eb)) := by
      let A := CombExp.arithmetic backend p.base l.start (table p) sp0 p.len p.w p.P p.G (bits p) eb
      obtain hp := persistent input.cached input.calls input.input.exponent size input.sameSp
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
      (CombExp.phase_ct K1 K2 timing odd (VG.Proof.Rsa.FixedBaseComb.rows_pos positiveBits) (by omega_using [scheduleFit]))
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
  obtain fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.KeyGenerate.tail, WP.seq_iff]
  refine WP.mono (law.correct s h environment calls stable h52 h56 h32 ready modulus odd r2 significant significantSize (by rw [significantValue]; exact scalarFits)) ?_
  rintro u ⟨contextU, readyU, powerU, modU, _, _, frameU, restU⟩
  rw [significantValue] at powerU
  change numAt u.mem (State.addr p.base) p.w 6 = keyPower p xb at powerU
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok u readyU (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [modU]; exact odd)) ?_
  rintro v ⟨readyV, flag, arraysV, frameV, restV⟩
  obtain contextV := contextU.after_workspace frameV restV readyV.ptr (fun d hd => (stableSlots_at stable hd).1)
  obtain powerV := (arraysV 6 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerU
  obtain flagV : v.gpr .r11 = if keyAccepted p xb then 1 else 0 := by
    rw [powerU, modU] at flag
    simpa only [keyAccepted, decide_eq_true_eq] using flag
  rw [WP.seq_iff]
  refine WP.mono (saveResult_ok v contextV.locals) ?_
  rintro w ⟨⟨_, resultW, frameW⟩, restW⟩
  obtain ptrW := (restW.gpr .r0 (by simp)).trans contextV.ptr
  obtain contextW := contextV.after_local (by decide : 64 + 4 ≤ 72) frameW restW ptrW
    (fun d hd => (stableSlots_at stable hd).1) saved
  obtain readyW := readyV.after_external frameW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    exact contextV.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))) (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [off, BitVec.add_zero] using
      Offset.disjoint (State.addr v.sp) (d := 0) (n := 4) (e := 64) (k := 4) (by left; decide) (by decide) (by decide)) restW ptrW
  obtain powerW := (readyW.2.number fits (by decide : 6 < 8)).trans powerV
  obtain powerFits : numAt w.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k) := by
    rw [powerW, keyPower, VG.Proof.Bignum.powMod_eq]
    have large := ready.modulus
    rw [modulus] at large
    exact Nat.lt_trans (Nat.mod_lt _ (by omega_using [odd])) p.modulusBound
  rw [WP.seq_iff]
  refine WP.mono (exportResult_ok w contextW h4 h32 readyW.1
    (by rw [outputY]; exact ((outputs.publicBuffer.after restU).after restV).after restW)
    (by rw [outputY]; exact outputs.publicWorkspace.symm) powerFits) ?_
  rintro z ⟨publicZ, frameZ, restZ⟩
  rw [powerW, outputY] at publicZ
  rw [outputY] at frameZ
  obtain outW := ((outputs.after restU).after restV).after restW
  obtain contextZ := contextW.toArgumentMemory.after_output frameZ restZ outW.publicDomain outW.publicStack
    (fun d hd => (stableSlots_at stable hd).1)
  obtain resultZ : z.mem.readW (off (State.addr z.sp) 64) 32 = if keyAccepted p xb then 1 else 0 := by
    rw [restZ.sp, frameZ.readW (r := ⟨off (State.addr w.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa using outW.publicStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide), restW.sp, resultW, flagV]
  refine WP.mono (keyFinish_ok z (keyAccepted p xb) contextZ (fun d hd => (stableSlots_at stable hd).1)
    h32 h36 h40 (outW.after restZ) resultZ) ?_
  rintro t ⟨status, privateT, publicT, frameT, _⟩
  obtain privateU := scalar.after_call frameU restU (by simpa only [scalarSize] using calls.privateValue)
  obtain privateW := (privateU.after_workspace frameV restV).after_frame frameW restW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [scalarSize, restV.sp, restU.sp] using
      outputs.privateStack.symm.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72)))
  obtain privateZ := privateW.after_frame frameZ restZ (by simpa only [scalarSize, List.mem_singleton, forall_eq] using outputs.separate)
  have privateBytesZ := privateZ.bytes
  rw [scalarSize] at privateBytesZ
  rw [privateBytesZ] at privateT
  rw [publicZ] at publicT
  refine ⟨status, privateT, publicT, ?_⟩
  obtain fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  obtain fullV : Frame (keyCallWrites p s) u.mem v.mem := frameV.mono (by simp [keyCallWrites, keyWrites])
  obtain fullW : Frame (keyCallWrites p s) v.mem w.mem := frameW.sub (by
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
  exact Nat.lt_trans (Nat.mod_lt _ (by omega_using [odd])) p.modulusBound

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
  obtain range := (inRange_ct (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
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
  omega_using [bound]

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
    (Proof.Ffdh.cachedGenerateKeyContract abi 176).post s t := by
  sig_post [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,
    Spec.Ffdh.generateKeySig,abi,argRegs,reduceClassify,Loc.val,State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes entropyBytes
  simp only [randLength,count,domain,entropy,domainBytes,entropyBytes,privateValue,publicValue]
  obtain output := sampleResult_spec size valid result
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
    (s : State) (pre : (Proof.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
    ∃tr t,Exec isa (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) s tr t ∧
      abiPreserved s t ∧ (Proof.Ffdh.cachedGenerateKeyContract abi 176).post s t := by
  obtain ⟨p,rb,_,privateValue,publicValue,domain,count,_,entropy,domainBytes,entropyBytes,input,cached,valid,_cache,_words⟩ :=
    cachedKeyGenerate_data s pre
  obtain modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  obtain ⟨tr,t,run,preserved,result⟩ := cachedKeyGenerateFn_ok prepare sample tail cachedGenerationEnvironment
    ScalarLayout.vetted prep sampler law CachedSample.layoutBound s input cached modValid
  refine ⟨tr,t,run,preserved,?_⟩
  obtain randLength : (stackArg s 4).toNat=(stackArg s 2).toNat := by
    sig_pre [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
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
      (Proof.Ffdh.cachedGenerateKeyContract abi 176) :=
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
    (Proof.Ffdh.cachedGenerateKeyContract abi 176) :=
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
