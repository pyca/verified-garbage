module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Prefix
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Timing
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Prefix
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Public traces for both contiguous POWER seal payload layouts -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.Contiguous
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq)

def sealRegs : List Reg := [.r19,.r22,.r23,.r27,.r28,.r29,.r30,.r31]
def suffixRegs : List Reg := [.r18,.r22,.r23,.r24,.r25,.r27,.r28,.r29,.r30,.r31]

private theorem prefixCert : ∃ h, (vectorTaint.check (Taint.ofRegs sealRegs) prefixCode h).isSome=true :=
  ⟨_,by taint_decide⟩
private theorem suffixCert : ∃ h, (vectorTaint.check (Taint.ofRegs suffixRegs) suffix h).isSome=true :=
  ⟨_,by taint_decide⟩

/-- The fused prefix and the rest of the same program see only public lengths
and addresses. The fused helper's preservation theorem carries them across its call. -/
theorem payload_rel [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s t : State} (sp : s.sp=t.sp) (agree : ∀ r ∈ sealRegs, s.gpr r=t.gpr r)
    (sa : FusedAccess s) (sr : Covers (fusedRead s++fusedWrite s) (s.rd++s.wr)) (sw : Covers (fusedWrite s) s.wr)
    (ta : FusedAccess t) (tr : Covers (fusedRead t++fusedWrite t) (t.rd++t.wr)) (tw : Covers (fusedWrite t) t.wr) :
    RelCT isa (Eq2 s t) payload TT := by
  obtain ⟨_,hc⟩ := prefixCert
  obtain ⟨_,hs⟩ := suffixCert
  apply RelCT.assoc
  refine rel_seq (RelCT.taint (A := vectorTaint) (Taint.ofRegs sealRegs)
    (fun _ _ ⟨rfl,rfl⟩ => ⟨sp,fun r hr => agree r (Taint.mem_ofRegs.mp hr)⟩) hc)
    (prefix_wp sa sr sw) (prefix_wp ta tr tw) (fun a b p q => ?_)
  refine RelCT.taint (A := vectorTaint) (Taint.ofRegs suffixRegs) (fun _ _ ⟨rfl,rfl⟩ =>
    ⟨p.sp.trans (sp.trans q.sp.symm),fun r hr => ?_⟩) hs
  have mem := Taint.mem_ofRegs.mp hr
  have len := agree .r23 (by decide)
  by_cases d : r=.r18
  · subst r; rw [p.dst,q.dst,len,agree .r27 (by decide)]
  by_cases x : r=.r24
  · subst r; rw [p.src,q.src,len,agree .r19 (by decide)]
  by_cases n : r=.r25
  · subst r; rw [p.len,q.len,len]
  have h : r ∈ prefixKeep ∧ r ∈ sealRegs := by clear hr; revert mem d x n; revert r; decide
  rw [p.saved r h.1,q.saved r h.1,agree r h.2]

/-- AAD branches and accesses depend on its length, address and the public
stream/context addresses. The trace permits arbitrary AAD bytes in each run. -/
theorem aad_rel {s t : State} (sp : s.sp=t.sp)
    (agree : ∀ r ∈ ([.r21,.r22,.r29,.r30,.r31] : List Reg), s.gpr r=t.gpr r) : RelCT isa (Eq2 s t) aadC TT := by
  refine RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r21,.r22,.r29,.r30,.r31])
    (fun _ _ ⟨rfl,rfl⟩ => ⟨sp,fun r hr => agree r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

end VG.Proof.AesGcm.PPC64LE.Contiguous
