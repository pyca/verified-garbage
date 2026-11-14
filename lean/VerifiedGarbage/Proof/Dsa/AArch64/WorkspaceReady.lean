module

public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
import VerifiedGarbage.Proof.Dsa.AArch64.Child
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
public import VerifiedGarbage.Proof.Dsa.AArch64.InitFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Parent

/-! ### `Dsa.AArch64.Workspaces`, which only this module used -/

section

/-! # Initializing both DSA moduli in the shared scratch allocation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def workspaceRanges (wp wq : Nat) : List (Nat × Nat) :=
  [(48, 80)] ++ initRanges pWorkspace wp ++ initRanges qWorkspace wq

theorem workspaces_ok {s : State} {B pp qp : Addr} {Z : Nat} {p q : List Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : activeBytes ≤ Z)
    (hp : word s.mem B Field.p.offset = pp) (hq : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hlens : Spec.Dsa.lengthsValid p.length q.length)
    (hpodd : Spec.Dsa.decodeBE p % 2 = 1) (hqodd : Spec.Dsa.decodeBE q % 2 = 1) :
    WP isa SignVerify.workspaces s fun t => ∃ pmi qmi : BitVec 64,
      Good t B Z outerWords 0 ∧
      ChildReady t.mem B pWorkspace ((p.length + 7) / 8) (Spec.Dsa.decodeBE p) pmi ∧
      ChildReady t.mem B qWorkspace ((q.length + 7) / 8) (Spec.Dsa.decodeBE q) qmi ∧
      Frm B (workspaceRanges ((p.length + 7) / 8) ((q.length + 7) / 8)) s.mem t.mem ∧
      Keep coreRegs s t := by
  obtain ⟨hp2, hp48, hq2, hq48, hpLo, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds hlens
  have hlengths : 1 ≤ p.length ∧ p.length < 2 ^ 31 ∧ 1 ≤ q.length ∧ q.length < 2 ^ 31 := by
    unfold Spec.Dsa.lengthsValid at hlens
    omega_using [hlens]
  have hparent : pWorkspace ≤ Z := Nat.le_trans (by decide) hZ
  unfold SignVerify.workspaces seqs
  refine WP.seq (WP.mono (parent_ok hs hdi hparent) fun u ⟨hgu, hfu, hku⟩ => ?_)
  have uf : Frm B [(48, 80)] s.mem u.mem := Frm.of_outside hfu (by simp)
  have ufield (f : Field) : word u.mem B f.offset = word s.mem B f.offset :=
    hfu.word (Or.inr (Nat.le_trans (by decide) (VG.Proof.Dsa.field_bounds f).1))
      (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  have usrc {ptr : Addr} {bs : List Byte} (hsrc : Src s B Z ptr bs) : Src u B Z ptr bs := by
    apply hsrc.congrK _ hku
    apply InScr.of_frm uf
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact Nat.le_trans (by decide) hparent
  refine WP.seq (WP.mono (child_ok hgu hparent (by decide) hpLo (Nat.le_trans hpHi (Nat.le_trans (by decide) hZ))
    hp2 hp48 (by decide) ⟨.input .p, .pLen⟩ (by trivial)
    ((ufield .p).trans hp) ((ufield .pLen).trans hpl) (usrc hps)
    hlengths.1 hlengths.2.1 rfl hpodd) fun v ⟨pmi, hgv, hpr, hfv, hkv⟩ => ?_)
  have vfield (f : Field) : word v.mem B f.offset = word u.mem B f.offset :=
    init_word hfv (VG.Proof.Dsa.field_bounds f).2
      (Or.inr (Nat.le_trans (by decide) (VG.Proof.Dsa.field_bounds f).1)) (by decide)
  have vqs := init_source hfv hkv (Nat.le_trans (by decide) hparent) (by omega_using [hZ, hpHi, hqHi]) (usrc hqs)
  have hqLo : slot outerWords 8 ≤ qWorkspace := by decide
  refine WP.mono (child_ok hgv hparent (by decide) hqLo (Nat.le_trans hqHi hZ)
    hq2 hq48 (by decide) ⟨.input .q, .qLen⟩ (by trivial)
    ((vfield .q).trans ((ufield .q).trans hq)) ((vfield .qLen).trans ((ufield .qLen).trans hql)) vqs
    hlengths.2.2.1 hlengths.2.2.2 rfl hqodd) fun t ⟨qmi, hgt, hqr, hft, hkt⟩ => ?_
  have hprt := init_ready hft hpr (by decide) (by have := hs.nowrap; omega_using [hZ, hpHi, hqHi, this]) (Or.inl (by omega_using [hpHi]))
  exact ⟨pmi, qmi, hgt, hprt, hqr, (uf.append hfv).append hft,
    ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end


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
  · right; omega_using [hb]
  · right; omega_using [hb]
  · exact Or.inl hb.2
  · right; omega_using [hb]
  · left; omega_using [hb, hpq]

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
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only at * <;> omega_arith

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
