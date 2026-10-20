module

public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
public import VerifiedGarbage.Proof.Dsa.AArch64.Workspaces
import VerifiedGarbage.Proof.Dsa.Layout

/-! # Establishing the persistent DSA context from caller scratch -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem workspace_field {B : Addr} {wp wq : Nat} {mem mem' : Mem}
    (hf : Frm B (workspaceRanges wp wq) mem mem') (f : Field) :
    word mem' B f.offset = word mem B f.offset := by
  have hb := VG.Proof.Dsa.field_bounds f
  have hpq : pWorkspace ≤ qWorkspace := by decide
  apply hf.word_eq _ (Nat.le_trans hb.2 (by decide))
  intro range hr
  simp only [workspaceRanges, initRanges, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · right; omega
  · right; omega
  · exact Or.inl hb.2
  · right; omega
  · left; omega

theorem workspace_outside {L : ExecutionLayout} {mem mem' : Mem}
    (hf : Frm L.base (workspaceRanges L.pWords L.qWords) mem mem') :
    Outside L.base 48 (activeBytes - 48) mem mem' := by
  obtain ⟨_, _, _, _, _, hphi, hqhi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hphi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqhi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hlo : 48 ≤ pWorkspace ∧ 48 ≤ qWorkspace ∧ 144 ≤ activeBytes := by decide
  intro x hx
  apply hf x
  intro range hr
  simp only [workspaceRanges, initRanges, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only at * <;> omega

theorem workspacesReady_ok {L : ExecutionLayout} {s : State} {pb qb : List Byte}
    (hs : Scr s L.base usedBytes) (hdi : s.gpr .x0 = L.base)
    (hfields : ∀ f, word s.mem L.base f.offset = L.fields f)
    (hps : Src s L.base usedBytes (L.fields .p) pb) (hqs : Src s L.base usedBytes (L.fields .q) qb)
    (hpl : pb.length = L.pLen) (hql : qb.length = L.qLen)
    (hpv : Spec.Dsa.decodeBE pb = L.modulus) (hqv : Spec.Dsa.decodeBE qb = L.subgroup)
    (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1) :
    WP isa SignVerify.workspaces s fun t => ∃ pmi qmi : BitVec 64,
      Ready { L with pInverse := pmi, qInverse := qmi } t ∧
      Outside L.base 48 (activeBytes - 48) s.mem t.mem ∧
      word t.mem L.base Field.mask.offset = word s.mem L.base Field.mask.offset ∧ Keep coreRegs s t := by
  have hpfield : word s.mem L.base Field.pLen.offset = BitVec.ofNat 64 pb.length := by
    rw [hpl]
    exact (hfields .pLen).trans L.pLength
  have hqfield : word s.mem L.base Field.qLen.offset = BitVec.ofNat 64 qb.length := by
    rw [hql]
    exact (hfields .qLen).trans L.qLength
  have hlens : Spec.Dsa.lengthsValid pb.length qb.length := by rw [hpl, hql]; exact L.lengths
  refine WP.mono (workspaces_ok hs hdi (by decide) (hfields .p) (hfields .q) hpfield hqfield
    hps hqs hlens (by rw [hpv]; exact hpo) (by rw [hqv]; exact hqo)) ?_
  intro t ⟨pmi, qmi, hg, hp, hq, hf, hk⟩
  simp only [hpl, hql, hpv, hqv] at hp hq hf
  have hsa : Scr t L.base activeBytes := by
    simpa only [off, BitVec.add_zero] using hg.scr.sub (o := 0) (n := activeBytes) (by decide) (by decide)
  refine ⟨pmi, qmi, ⟨⟨hsa, hg.x0, hg.hdr⟩, hs.congr hk.wr, ?_, hp, hq⟩,
    workspace_outside (L := L) hf, workspace_field hf .mask, hk⟩
  intro f _
  exact (workspace_field hf f).trans (hfields f)

end VG.Proof.Dsa.AArch64
