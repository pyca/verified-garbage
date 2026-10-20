module

public import VerifiedGarbage.Proof.Dsa.X86_64.SignBody
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyBody
public import VerifiedGarbage.Proof.Dsa.X86_64.ComputeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SignReleaseCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands

/-! # Constant time through validation, computation and the ABI return -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

theorem signingComputeRelease_ok (M : Mont) (Sq : MontS) {p : SchedulePublic} {s : State} (h : SigningBodyPre p s) :
    WP isa (signCompute Sq.mm M.mm) s (ReleasePre p.release) := by
  obtain ⟨hr, ⟨data, yb, qb, ho, _⟩, ⟨valid, hm⟩, hw, hsep⟩ := h
  refine WP.mono (signCompute_ok M Sq hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.subgroup ho.privateScalar ho.nonce ho.digest
    ho.generatorLength ho.publicLength ho.subgroupLength ho.privateLength ho.nonceLength
    ho.digestBound ho.subgroupValue hm) fun t ⟨ht, hm, _, _, _, hk⟩ => ?_
  exact ⟨ht.scratch, ht.parent.rdi, ht.fields .out (by decide),
    (ht.fields .qLen (by decide)).trans p.layout.qLength, ⟨_, hm⟩,
    fun i hi => by rw [hk.2.2]; exact hw i hi, hsep⟩

theorem signBody_ct (M : Mont) (Sq : MontS) : RelCT isa (Two SigningBodyPre) (signBody Sq.mm M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => ReleasePre p.release)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule) (signCompute_ct M Sq)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => signingComputeRelease_ok M Sq h
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

theorem verifyingComputeReturn_ok (M : Mont) (Sq : MontS) {p : SchedulePublic} {s : State} (h : VerifyingBodyPre p s) :
    WP isa (verifyCompute Sq.mm M.mm) s (fun t => t.gpr .rdi = p.layout.base) := by
  obtain ⟨hr, ⟨data, qb, ho, _⟩, ⟨valid, hm⟩⟩ := h
  refine WP.mono (verifyCompute_ok M Sq hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.subgroup ho.signatureR ho.signatureS ho.digest
    ho.generatorLength ho.publicLength ho.subgroupLength ho.rLength ho.sLength
    ho.digestBound ho.subgroupValue hm) fun _ h => h.1.parent.rdi

theorem verifyBody_ct (M : Mont) (Sq : MontS) : RelCT isa (Two VerifyingBodyPre) (verifyBody Sq.mm M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => fun t => t.gpr .rdi = p.layout.base)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule) (verifyCompute_ct M Sq)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => verifyingComputeReturn_ok M Sq h
  · exact two_map (fun p => p.layout.base) (fun _ _ h => h) result_ct

end VG.Proof.Dsa.X86_64
