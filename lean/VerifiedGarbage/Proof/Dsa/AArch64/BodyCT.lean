module

public import VerifiedGarbage.Proof.Dsa.AArch64.SignBody
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
public import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SignReleaseCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
public import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
public import VerifiedGarbage.Proof.Dsa.AArch64.Add
public import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Call2
public import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
public import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
public import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
public import VerifiedGarbage.Proof.Dsa.AArch64.Failure
public import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
public import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
public import VerifiedGarbage.Proof.Dsa.AArch64.Power
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
public import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
public import VerifiedGarbage.Proof.Dsa.AArch64.Result
public import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
public import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Store
public import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
public import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
public import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
public import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.Call2
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.Minus
import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Sha256.Stream

/-! # Constant time through validation, computation and the ABI return -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def SigningBodyPre (p : SchedulePublic) (s : State) : Prop :=
  Ready p.layout s ∧
  (∃ data yb qb, SigningOperands p.layout data yb qb s ∧ data.digest.length = p.digestLen) ∧
  (∃ valid : Bool, word s.mem p.layout.base Field.mask.offset = mask valid) ∧
  (∀ i < 2 * p.layout.qLen, InRegions s.wr (p.layout.fields .out + BitVec.ofNat 64 i) 1) ∧
  (∀ i < 2 * p.layout.qLen, usedBytes ≤ ofs p.layout.base (p.layout.fields .out + BitVec.ofNat 64 i))

theorem SigningBodyPre.schedule {p : SchedulePublic} {s : State} (h : SigningBodyPre p s) :
    PublicKeyPre signComputeInputs p s := by
  obtain ⟨hr, ⟨data, yb, qb, ho, hd⟩, hm, _, _⟩ := h
  refine ⟨⟨hr, ?_, hm⟩, qb, ho.subgroup, ho.subgroupLength, ho.subgroupValue⟩
  intro a ha
  simp only [signComputeInputs, signInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨yb, ho.publicValue, ho.publicLength⟩
  · exact ⟨qb, ho.subgroup, ho.subgroupLength⟩
  · exact ⟨data.generator, ho.generator, ho.generatorLength⟩
  · exact ⟨data.nonce, ho.nonce, ho.nonceLength⟩
  · exact ⟨data.privateScalar, ho.privateScalar, ho.privateLength⟩
  · exact ⟨data.digest, ho.digest, hd⟩

def SchedulePublic.release (p : SchedulePublic) : ReleasePublic where
  base := p.layout.base
  output := p.layout.fields .out
  width := p.layout.qLen
  positive := p.layout.widths.1
  bound := p.layout.widths.2.1

theorem signingComputeRelease_ok (M : Mont) {p : SchedulePublic} {s : State} (h : SigningBodyPre p s) :
    WP isa (signCompute M.mm) s (ReleasePre p.release) := by
  obtain ⟨hr, ⟨data, yb, qb, ho, _⟩, ⟨valid, hm⟩, hw, hsep⟩ := h
  refine WP.mono (signCompute_ok M hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.subgroup ho.privateScalar ho.nonce ho.digest
    ho.generatorLength ho.publicLength ho.subgroupLength ho.privateLength ho.nonceLength
    ho.digestBound ho.subgroupValue hm) fun t ⟨ht, hm, _, _, _, hk⟩ => ?_
  exact ⟨ht.scratch, ht.parent.x0, ht.fields .out (by decide),
    (ht.fields .qLen (by decide)).trans p.layout.qLength, ⟨_, hm⟩,
    fun i hi => by rw [hk.wr]; exact hw i hi, hsep⟩

theorem signBody_ct (M : Mont) : RelCT isa (Two SigningBodyPre) (signBody M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => ReleasePre p.release)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule) (signCompute_ct M)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => signingComputeRelease_ok M h
  · exact two_map SchedulePublic.release (fun _ _ h => h) signRelease_ct

def VerifyingBodyPre (p : SchedulePublic) (s : State) : Prop :=
  Ready p.layout s ∧
  (∃ data qb, VerificationOperands p.layout data qb s ∧ data.digest.length = p.digestLen) ∧
  ∃ valid : Bool, word s.mem p.layout.base Field.mask.offset = mask valid

theorem VerifyingBodyPre.schedule {p : SchedulePublic} {s : State} (h : VerifyingBodyPre p s) :
    PublicKeyPre verifyComputeInputs p s := by
  obtain ⟨hr, ⟨data, qb, ho, hd⟩, hm⟩ := h
  refine ⟨⟨hr, ?_, hm⟩, qb, ho.subgroup, ho.subgroupLength, ho.subgroupValue⟩
  intro a ha
  simp only [verifyComputeInputs, verifyInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨qb, ho.subgroup, ho.subgroupLength⟩
  · exact ⟨data.generator, ho.generator, ho.generatorLength⟩
  · exact ⟨data.publicValue, ho.publicValue, ho.publicLength⟩
  · exact ⟨data.signatureR, ho.signatureR, ho.rLength⟩
  · exact ⟨data.signatureS, ho.signatureS, ho.sLength⟩
  · exact ⟨data.digest, ho.digest, hd⟩

theorem verifyingComputeReturn_ok (M : Mont) {p : SchedulePublic} {s : State} (h : VerifyingBodyPre p s) :
    WP isa (verifyCompute M.mm) s (fun t => t.gpr .x0 = p.layout.base) := by
  obtain ⟨hr, ⟨data, qb, ho, _⟩, ⟨valid, hm⟩⟩ := h
  refine WP.mono (verifyCompute_ok M hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.subgroup ho.signatureR ho.signatureS ho.digest
    ho.generatorLength ho.publicLength ho.subgroupLength ho.rLength ho.sLength
    ho.digestBound ho.subgroupValue hm) fun _ h => h.1.parent.x0

theorem verifyBody_ct (M : Mont) : RelCT isa (Two VerifyingBodyPre) (verifyBody M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => fun t => t.gpr .x0 = p.layout.base)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule) (verifyCompute_ct M)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => verifyingComputeReturn_ok M h
  · exact two_map (fun p => p.layout.base) (fun _ _ h => h) result_ct

end VG.Proof.Dsa.AArch64
