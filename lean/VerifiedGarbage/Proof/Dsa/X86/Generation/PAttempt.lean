module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTestState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributions
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStatus
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidatePreserve
import VerifiedGarbage.Proof.Dsa.X86.Generation.ControlPreserve
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttemptControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateTest
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchConstruct

/-! # One complete p-search attempt with exact candidate and witness outcomes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem pAttempt_ok {H : Hash} (K : HashOK H) {P : SearchContextPlan} {T : GenerationTape P.geometry}
    {W : Nat → BitVec 32} {s : State} {counter qvalue used : Nat}
    (R : SearchContext P W s) (seed : TapeMemory T s) (len : T.bytes.length = P.geometry.qLen)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (counterBound : counter < 32 * P.geometry.pLen)
    (C : SearchControl (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) counter (P.geometry.contributionCount + 1) s)
    (source : W 1 = T.pointer) (usedValue : W 16 = BitVec.ofNat 32 used) (usedBound : used ≤ P.witnesses.bytes.length)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen) = qvalue)
    (qpos : 0 < qvalue) (qbound : 2 * qvalue < 2 ^ (32 * (2 * (P.geometry.pLen / 8))))
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * T.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * T.bytes.length) bs).length = 8 * T.bytes.length)
    (valueBound : Spec.Dsa.pCandidate (8 * P.geometry.pLen) (8 * P.geometry.qLen) qvalue T.bytes
      (1 + counter * (P.geometry.contributionCount + 1)) < 256 ^ P.geometry.pLen)
    (valueOdd : Spec.Dsa.pCandidate (8 * P.geometry.pLen) (8 * P.geometry.qLen) qvalue T.bytes
      (1 + counter * (P.geometry.contributionCount + 1)) % 2 = 1) :
    WP isa (pAttempt H P.geometry.pLen P.geometry.qLen) s fun t =>
      let value := Spec.Dsa.pCandidate (8 * P.geometry.pLen) (8 * P.geometry.qLen) qvalue T.bytes
        (1 + counter * (P.geometry.contributionCount + 1))
      ∃ W', ∃ result : PrimeStepResult, SearchContext P W' t ∧ W' 1 = T.pointer ∧ W' 10 = W 10 ∧
        W' 16 = BitVec.ofNat 32 result.used ∧ W' 19 = BitVec.ofNat 32 result.status ∧
        TapeMemory T t ∧ Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off P.geometry.base q) P.geometry.qLen) = qvalue ∧
        Spec.Rsa.bytesAt t.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen value ∧
        Spec.Rsa.bytesAt t.mem (off P.geometry.base exponent) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen ((value - 1) / qvalue) ∧
        CandidateTestResult P value used result t ∧
        SearchControl (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) counter (P.geometry.contributionCount + 1) t ∧
        t.mem.readW (off (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) 8) 32 = BitVec.ofNat 32 result.status ∧
        Frame (parameterWrites P.geometry) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have pw := P.geometry.width
  have qw := P.geometry.qWidth
  have qr : q + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold q usedBytes domainCheck; omega
  have pr : p + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold p usedBytes domainCheck; omega
  have er : exponent + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold exponent usedBytes domainCheck; omega
  unfold pAttempt
  refine WP.seq (WP.mono (pAttemptOffset_ok R C) fun a ⟨Ra, Ca, Oa, Ka⟩ => ?_)
  have Fa : Frame (parameterWrites P.geometry) s.mem a.mem := Oa.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [parameterWrites])
  have seeda := seed.keep Fa T.parameterApart Ka
  have qa : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt a.mem (off P.geometry.base q) P.geometry.qLen) = qvalue := by
    rw [drawFrame_bytes Oa (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (P.geometry.frame_part qr).symm) (by omega), qval]
  refine WP.seq (WP.mono (searchConstruct_ok K Ra seeda len digest final (P.geometry.contribution_offset counterBound)
    (show frameUpdate W 2 _ 1 = T.pointer from source) rfl qa qpos qbound hash hashSize)
    fun b ⟨pb, eb, qb, Rb, seedb, Ob, Kb⟩ => ?_)
  have Cb := Ca.frame Ob (construction_controlApart K P.geometry T _ len final)
  have Fb := Ob.sub (construction_mutable K P.geometry T _ len final)
  refine WP.seq (WP.mono (pCandidateTest_ok Rb valueBound valueOdd pb
    (show frameUpdate W 2 _ 16 = BitVec.ofNat 32 used from usedValue) usedBound)
    fun c ⟨result, Rc, outcome, Oc, Kc⟩ => ?_)
  have Cc := Cb.frame Oc (candidateTest_controlApart P.geometry)
  have Fc := Oc.sub (candidateTest_mutable P.geometry)
  have seedc := seedb.keep Fc T.parameterApart Kc
  refine WP.mono (pAttemptReturn_ok Rc Cc) fun t ⟨Rt, Ct, status, Ot, Kt⟩ => ?_
  have Ft := (controlOutside_frame Ot).sub (control_mutable P.geometry)
  refine ⟨_, result, Rt, source, rfl, rfl, rfl, seedc.keep Ft T.parameterApart Kt, ?_, ?_, ?_,
    outcome.keep (controlOutside_frame Ot) (control_arithmeticApart P.geometry) Kt (by decide), Ct, status,
    ((Fa.trans Fb).trans Fc).trans Ft,
    (Ka.mono (by decide)).trans (Kb.trans (Kc.trans (Kt.mono (by decide))))⟩
  · rw [control_bytes Ot qr (by unfold q VG.Impl.Dsa.Generation.Layout.control; omega),
      candidateTest_bytes Oc qr (by unfold q witness; omega), qb]
  · rw [control_bytes Ot pr (by unfold p VG.Impl.Dsa.Generation.Layout.control; omega),
      candidateTest_bytes Oc pr (by unfold p witness; omega), pb]
  · rw [control_bytes Ot er (by unfold exponent VG.Impl.Dsa.Generation.Layout.control; omega),
      candidateTest_bytes Oc er (by unfold exponent witness; omega), eb]
end VG.Proof.Dsa.X86.Generation
