module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSA with the CRT on x86-64, with the key's precomputed values: constant time

`Crt.mainP` leaks what `Crt.main` leaks, and `r2Pre` only the stack
pointer, `w`, the working space and `pre`'s address (`crtMainP_ct`), from
states that carry, besides `main`'s stage, the stack pointer, `pre`'s
address and `R² mod n` in `pre` (`StageP`); so `Crt.codeP` is constant
time but for `n` and `pre`'s address (`crtCodeP_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## `main` -/

/-- A state of `main`'s stage `R`, with the stack pointer `q.2.1`, `pre`'s
address `q.2.2` and `R² mod n` in `pre`. -/
def StageP (R : StageRel) (q : CrtPub × Addr × Addr) (t : State) : Prop :=
  Stage R q.1 t ∧ t.gpr .rsp = q.2.1 ∧ stackArg t 12 = q.2.2 ∧ PreR2 t q.1.B q.1.Z q.1.w q.1.N

/-- The setup of `n` and the input, from `main`'s start with `pre`. -/
theorem setupAP_ct : RelCT isa (Two (StageP R0)) (seqs (loadSteps ++ restSteps)) (Two (StageP RA)) := by
  refine two_post (setupA_ct.mono (fun _ _ h => two_bind (fun q _ _ h₁ h₂ => ⟨q.1, h₁.1, h₂.1⟩) h)
    fun _ _ _ => trivial) ?_
  rintro q σ ⟨⟨σ', xb, pb, qb, dpb, dqb, qib, h, hv, he⟩, hsp, harg, hp⟩
  subst he
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  have hZq := h.z
  have hZ : slot ((q.1.k + 7) / 8) 8 ≤ q.1.Z := by unfold offQ at hZq; omega_arith
  refine WP.mono (setup_ok h.scr h.rdi hZ (by omega_arith) (by omega_arith) h.hK h.hN h.hIn
    h.n h.x h.nl h.xl hodd) fun t ⟨minv, so, f, k⟩ => ?_
  have hi : InScr q.1.B q.1.Z σ.mem t.mem := InScr.of_frm f fun r hr => Nat.le_trans (setupRanges_le _ r hr) hZ
  exact ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, so⟩, (k.gpr (by decide)).trans hsp,
    (hp.arg_eq hi (k.gpr (by decide))).trans harg, hp.congr hi (k.gpr (by decide)) k.2.1 k.2.2⟩

/-- `R² mod n` from `pre`. -/
theorem r2P_ct : RelCT isa (Two (StageP RA)) r2Pre (Two (Stage RB)) := by
  refine (two_post (Ψ := fun (q : CrtPub × Addr × Addr) t => Stage RB q.1 t)
    (two_map (fun q : CrtPub × Addr × Addr => (⟨q.2.1, q.1.B, q.1.w, q.2.2⟩ : R2PPub)) ?_ r2Pre_ct) ?_).mono
    (fun _ _ h => h) (fun _ _ h => two_bind (fun q _ _ h₁ h₂ => ⟨q.1, h₁, h₂⟩) h)
  · rintro q t ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, so⟩, hsp, harg, hp⟩
    have hZq := h.z
    have hZ : slot q.1.w 8 ≤ q.1.Z := by unfold CrtPub.w; unfold offQ at hZq; omega_arith
    have := r2PreCT_of so.good hZ so.r12 hp
    rw [hsp, harg] at this
    exact this
  · rintro q t ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, so⟩, -, -, hp⟩
    obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
    have := h.k1
    have := h.k2
    have hZq := h.z
    exact WP.mono (r2Pre_ok so.good (by unfold CrtPub.w; unfold offQ at hZq; omega_arith) (by unfold CrtPub.w; omega_arith)
      (by unfold CrtPub.w; omega_arith) so.r12 (by omega_arith) hp)
      fun t' ⟨hg, _⟩ => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, hg⟩

/-- `n`'s setup with `R² mod n` from `pre` leaks the same in runs that agree
on `n`, the stack pointer and `pre`'s address. -/
theorem nSetupP_ct (M : Mont) : RelCT isa (Two (StageP R0)) (seqs (nSetupP M.mm)) fun _ _ => True := by
  rw [nSetupP_eq]
  refine RelCT.seqs_append (by simp [loadSteps]) (by simp) (RelCT.seq setupAP_ct ?_)
  exact RelCT.seqs_append (by simp) (by simp) (RelCT.seq r2P_ct (nTail_ct M))

/-- `mainP` leaks the same in runs that agree on the public data, the stack
pointer and `pre`'s address, given that its parts do. -/
theorem crtMainP_ct (M : Mont) (E : CrtExpL M) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M E) (hP : PPhaseCT M E)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    RelCT isa (Two (StageP R0)) (Crt.mainP M.mm E.code) fun _ _ => True := by
  rw [crtMainP_eq]
  refine RelCT.seqs_append (by simp [nSetupP]) (by simp [qPhase]) (RelCT.seq (R := Two (Stage R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetupP]) (by simp [checks])
      (RelCT.seq (R := Two (Stage R2)) ?_ (checksS_ct hC))
    refine RelCT.seqs_append (by simp [nSetupP]) (by simp [primesSetup])
      (RelCT.seq (R := Two (Stage R1)) ?_ (setupS_ct hS))
    refine (two_post (Ψ := fun (q : CrtPub × Addr × Addr) t => Stage R1 q.1 t) (nSetupP_ct M) ?_).mono
      (fun _ _ h => h) (fun _ _ h => two_bind (fun q _ _ h₁ h₂ => ⟨q.1, h₁, h₂⟩) h)
    rintro q σ ⟨⟨σ', xb, pb, qb, dpb, dqb, qib, h, hv, he⟩, -, -, hp⟩
    subst he
    exact WP.mono (nPartP_ok M h hv hp) fun _ ⟨minv, hr⟩ => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, hr⟩
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (qS_ct M E hQ) ?_)
  exact RelCT.seqs_append (by simp [pPhase]) (by simp [finish]) (RelCT.seq (pS_ct M E hP) hF)

/-! ## The code -/

/-- A state `crtContractP` allows, with the public data `q.1` and `pre`'s
address `q.2`. -/
def CCRelP (q : CCPub × Addr) (s : State) : Prop := crtContractP.pre s ∧ CCEq q.1 s ∧ stackArg s 12 = q.2

theorem ccRelP_ok : CCOk Prod.fst CCRelP := fun _ _ h => ⟨(crtCtxP_of h.1).1, h.2.1⟩

/-- `main`'s stage with `pre`, after the head and the modulus' check. -/
theorem cc3P_stage {q : CCPub × Addr} {t : State} (h : CC3W Prod.fst CCRelP q t) (he : isa.eval .ne t = some false) :
    StageP R0 (q.1.m, q.1.rsp, q.2) t := by
  obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre⟩ := cc3W_pre ccRelP_ok h
  obtain ⟨s, t₁, ⟨hs, heq, harg⟩, hh, hm, k, hz⟩ := h
  have hv : Spec.Rsa.modulusValid q.1.m.N q.1.m.k = true := by
    simp only [eval, hz] at he; simpa using he
  obtain ⟨-, -, hp⟩ := crtCtxP_of hs
  obtain ⟨hsp, hB, hZ, hk, -, hnp, -, -, -, -, -, -, -, -, hnb⟩ := heq
  rw [hB, hZ, hnb, hk] at hp
  have kk := hh.keep.trans k
  have hi : InScr q.1.m.B q.1.m.Z s.mem t.mem := by rw [hm, ← hB, ← hZ]; exact hh.inScr
  exact ⟨⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, rfl⟩, (kk.gpr (by decide)).trans hsp,
    (hp.arg_eq hi (kk.gpr (by decide))).trans harg, hp.congr hi (kk.gpr (by decide)) kk.2.1 kk.2.2⟩

variable (M : Mont) (E : CrtExpL M)

/-- `vg_rsa_private_crt_precomputed` leaks the same in runs that agree on the
public data and `pre`'s address, given that `main`'s parts do. -/
theorem crtCodeP_ct (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M E) (hP : PPhaseCT M E)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    RelCT isa (Two CCRelP) (Crt.codeP M.mm E.code) fun _ _ => True := by
  unfold Crt.codeP
  refine crtEntryWith_ct ccRelP_ok _ ?_
  exact (crtMainP_ct M E hS hC hQ hP hF).mono (fun _ _ h => two_bind (fun q t₁ t₂ h₁ h₂ =>
    ⟨(q.1.m, q.1.rsp, q.2), cc3P_stage h₁.1 h₁.2, cc3P_stage h₂.1 h₂.2⟩) h) fun _ _ h => h

/-- `vg_rsa_private_crt_precomputed` is constant time but for `n` and `pre`'s
address, given that `main`'s parts are. -/
theorem crtCodeP_constantTime_of (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M E) (hP : PPhaseCT M E)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    ConstantTime isa crtContractP.pre crtContractP.pub (Crt.codeP M.mm E.code) := by
  refine RelCT.constantTime ((crtCodeP_ct M E hS hC hQ hP hF).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp, h12, _, _⟩ => ⟨(ccPubOf s₁, stackArg s₁ 12), ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, ⟨r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩, h12.symm⟩

/-- `vg_rsa_private_crt_precomputed` is constant time but for `n` and `pre`'s
address. -/
theorem crtCodeP_constantTime (hE : E.CT) :
    ConstantTime isa crtContractP.pre crtContractP.pub (Crt.codeP M.mm E.code) :=
  crtCodeP_constantTime_of M E setup_ct checks_ct
    (qPhase_ct M E (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M E (redc_ct_Y M) hE.2 (by taint_decide)))
    (pPhase_ct M E (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M E (redc_ct_Y M) hE.1 (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct

end VG.Proof.Bignum.X86_64
