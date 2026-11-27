module

public import VerifiedGarbage.Proof.MlKem.X86_64.Mul
public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeMul
public import VerifiedGarbage.Proof.MlKem.X86_64.Ntt
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.Ntt
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MlKem.X86_64.NttInv`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: `vg_mlkem_inv_ntt`

As `vg_mlkem_ntt` (`Ntt.lean`): each layer is `nttInvLayer`, the seven layers
are those of `NTT⁻¹` (`nttInv_eq_layers`), and the last pass multiplies each
coefficient by 3303 (`vscale_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem nttInvLayer_eq (F : Poly) (len : Nat) :
    nttInvLayer F len = layF nttInvBlockN F len (fun c => 256 / len - 1 - c) (128 / len) := rfl

/-- A layer of `NTT⁻¹` with `len ≥ 8`, whose first zeta is `zeta k`. -/
theorem invLay_ok {sP : Addr} (len k : Nat) (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 256 / len - 1 = k)
    {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vibfly len k (-2)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F len) ∧ BInv sP s s' := by
  have hl : 128 / len ≥ 1 ∧ 256 / len = 2 * (128 / len) ∧ 256 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [nttInvLayer_eq]
  exact vlay_ok vibfly_spec nttInvBlk_ok hlen (-2) (fun c => 256 / len - 1 - c) (by rw [hk]; rfl)
    (fun c _ => by omega_using [hl])
    (fun c hc' => step_bwd (zi := fun c => 256 / len - 1 - c) (dz := -2) _ 1 (by decide) (by omega_using [hl, hc']))
    hc hsi hS hT hw

theorem invLay4_ok {sP : Addr} {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay4 vibfly 62 0x05 (-4)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 4) ∧ BInv sP s s' := by
  rw [nttInvLayer_eq, show 256 / 4 - 1 = 63 from rfl, show 128 / 4 = 32 from rfl]
  exact vlay4_ok vibfly_spec nttInvBlk_ok 62 0x05 (-4) (fun c => 63 - c) (fun i => 62 - 2 * i) rfl (by decide)
    (by decide)
    (fun i hi => step_bwd (zi := fun i => 62 - 2 * i) (dz := -4) _ 2 (by decide) (by omega_using [hi]))
    hc hsi hS hT hw

theorem invLay2_ok {sP : Addr} {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vibfly 124 0x1B (-8)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 2) ∧ BInv sP s s' := by
  rw [nttInvLayer_eq, show 256 / 2 - 1 = 127 from rfl, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vibfly_spec nttInvBlk_ok 124 0x1B (-8) (fun c => 127 - c) (fun i => 124 - 4 * i) rfl
    (by decide) (by decide)
    (fun i hi => step_bwd (zi := fun i => 124 - 4 * i) (dz := -8) _ 4 (by decide) (by omega_using [hi]))
    hc hsi hS hT hw

theorem nttInv_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.nttInv s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa Impl.MlKem.X86_64.nttInv s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold Impl.MlKem.X86_64.nttInv
    refine noMx_ok (sP := s.gpr .rsi) fun s1 k1 f1 => ?_
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (vpro_ok hdi1 hsi1 hF1 (by rw [k1.2.1, k1.2.2]; exact List.mem_append_right _ hwf) (by rw [k1.2.2]; exact hw) hd)
      fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LI.seq hsi2 hw2 invLay2_ok ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LI.seq hsi2 hw2 invLay4_ok ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 8 31 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 16 15 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 32 7 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 64 3 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 128 1 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fun _ hc hsi hS _ hw => vscale_ok hc hsi hS hw) ?_ hI
    intro s3 hI
    refine WP.mono (vepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4, _⟩ => ⟨?_, ?_⟩
    · rw [nttInv_eq_layers]
      simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_))) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr (mx_sub _), .inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem nttInv_ct : ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub Impl.MlKem.X86_64.nttInv :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.KpkeBodies`, which only this module used -/

section

/-!
# ML-KEM on x86-64: the SSE2 arithmetic without its MXCSR region

The code `vg_mlkem*_decrypt_mul` inlines (`Bodies.sse`): `vg_mlkem_ntt`'s,
storing its result through `r10` (`nttOB`, against `nttOK`),
`vg_mlkem_inv_ntt`'s (`nttInvB`) and `vg_mlkem_multiply_ntts`'s (`mulB`),
meet the contracts of the functions: the proofs are those of the functions
(`Ntt.lean`, `NttInv.lean`, `Mul.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `NTT` of `f = rdi` to `t = r10`, with the working space at `rsi`. -/
def nttOK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .r10), pR (s.gpr .rsi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .r10)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .r10)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .r10) (ntt (polyAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- `mov rdi, r10`. -/
theorem movDiR10_ok (s : State) :
    WP isa (.block [.mov .rdi (.reg .r10)]) s fun s' => s'.gpr .rdi = s.gpr .r10 ∧ s'.mem = s.mem ∧
      s'.xmm = s.xmm ∧ Keep [.rdi] s s' := by
  vrunm
  refine ⟨fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem nttOB_correct (s : State) (hs : nttOK.pre s) :
    ∃ t s', Exec isa nttOB s t s' ∧ abiPreserved s s' ∧ nttOK.post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwt : pR (s.gpr .r10) ∈ s.wr := by rw [hs.2.1]; simp
  have hrf : pR (s.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hs.1]; simp
  have hW : WP isa nttOB s fun s' => PolyIs s'.mem (s.gpr .r10) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .r10), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold nttOB
    refine WP.seq (WP.mono (vpro_ok rfl rfl ⟨hs.2.2.2.2.2.2, rfl⟩ hrf hw hs.2.2.1) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := k2.gpr (by decide)
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2]; exact hw
    refine LI.seq hsi2 hw2 (fwdLay_ok 128 1 (by decide) (by decide)) ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 64 2 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 32 4 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 16 8 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 8 16 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 fwdLay4_ok ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 fwdLay2_ok ?_ hI
    intro s3 hI
    refine WP.seq (WP.mono (movDiR10_ok s3) fun s4 ⟨hdi4, hm4, hx4, k4⟩ => ?_)
    have k34 := hI.keep.trans k4
    have hS4 := hI.S
    rw [← hm4] at hS4
    refine WP.mono (vepi_ok (s := s4) ⟨by rw [hx4]; exact hI.c.q, by rw [hx4]; exact hI.c.qinv⟩
      hS4 (by rw [hdi4, hI.keep.gpr (by decide), k2.gpr (by decide)])
      (by rw [k34.gpr (by decide), hsi2]) (by rw [k34.2.2, k2.2.2]; exact hwt)
      (by rw [k34.2.2]; exact hw2) hs.2.2.2.1) fun s5 ⟨hP, hf5, _⟩ => ⟨?_, ?_⟩
    · rw [ntt_eq_layers]
      simp only [nttLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · rw [hm4] at hf5
      refine (frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf5 ?_)) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rdi, .r8, .r9] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩)), hP⟩

theorem nttInvB_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa nttInvB s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvB s fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold nttInvB
    refine WP.seq (WP.mono (vpro_ok rfl rfl ⟨hs.2.2.2.2.2, rfl⟩ (List.mem_append_right _ hwf) hw hd)
      fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := k2.gpr (by decide)
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2]; exact hw
    refine LI.seq hsi2 hw2 invLay2_ok ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LI.seq hsi2 hw2 invLay4_ok ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 8 31 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 16 15 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 32 7 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 64 3 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 128 1 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fun _ hc hsi hS _ hw => vscale_ok hc hsi hS hw) ?_ hI
    intro s3 hI
    refine WP.mono (vepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide)])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4, _⟩ => ⟨?_, ?_⟩
    · rw [nttInv_eq_layers]
      simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_)) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), hP⟩

namespace Mul

theorem bodyCorrect {s₀ : State} (hp : mulK.pre s₀) :
    ∃ t s', Exec isa mulB s₀ t s' ∧ abiPreserved s₀ s' ∧ mulK.post s₀ s' := by
  have hw : pR (sP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hW : WP isa mulB s₀ fun s' =>
      PolyIs s'.mem (hP s₀) (multiplyNTTs (F s₀) (G s₀)) ∧ Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s'.mem := by
    unfold mulB
    refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r10 = sP s₀ ∧ s1.mem = s₀.mem ∧
      s1.xmm = s₀.xmm ∧ Keep [.r10] s₀ s1) (by
        vrunm
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h10, hm1, _, k1⟩ => ?_)
    refine WP.seq ?_
    simp only [mulPro, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (wordTab_gen gTab gTab_lt (by decide) h10 (by rw [k1.2.2]; exact hw))
      fun s3 ⟨ht, f3, k3, _, _⟩ => ?_
    have h10'' : s3.gpr .r10 = sP s₀ := by rw [k3.gpr (by decide), h10]
    refine WP.mono (Q := fun (s4 : State) => VConsts s4 ∧ s4.xmm .xmm12 = r2V ∧ s4.gpr .r8 = sP s₀ ∧
      s4.mem = s3.mem ∧ Keep [.rax, .r8] s3 s4) (by
        simp only [vconsts]
        vrunm [h10'']
        refine ⟨⟨?_, ?_⟩, fun r hr => ?_, rfl, rfl⟩
        · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
          decide
        · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
          decide
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false])
      fun s4 ⟨hc4, hr4, h84, hm4, k4⟩ => ?_
    have k14 := (k1.trans k3).trans k4
    refine WP.mono (wp_rcxLoop (N := 16) (by decide) (by decide) (Inv s₀) (fun s g _ => ?_)
      fun i hi s hI => step hp hi hI) fun s5 hI => ⟨?_, hI.frame⟩
    · have k := k14.trans g.keep
      refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, ?_, fun _ h => absurd h (by omega_using [])⟩
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [g.keep.gpr (by decide), h84]; exact (add_ofNat_zero _).symm
      · exact ⟨by rw [g.xmm]; exact hc4.q, by rw [g.xmm]; exact hc4.qinv⟩
      · rw [g.xmm]; exact hr4
      · rw [g.mem, hm4, ← hm1]
        refine frame_fs (fP := hP s₀) f3 ?_
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact .inr (pR_sub_tab _)
      · intro k hk; rw [g.mem, hm4]; exact ht k hk
    · exact polyIs_of_toNat fun k hk => hI.done k (by rw [n_eq] at hk; omega_using [hk])
  obtain ⟨t, s', he, ⟨hP', hf⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1⟩)), hP'⟩

end Mul

theorem mulB_correct (s : State) (hs : mulK.pre s) :
    ∃ t s', Exec isa mulB s t s' ∧ abiPreserved s s' ∧ mulK.post s s' :=
  Mul.bodyCorrect hs

end VG.Proof.MlKem.X86_64

end

end


/-!
# ML-KEM on x86-64: the pieces of `vg_mlkem*_{en,de}crypt_mul`

What `decryptMul` and `encryptMul` (`Impl/MlKem/X86_64/KpkeMul.lean`) need
of the code of a backend (`BodiesOk`): each piece meets a contract, around
an accumulator of a sum of products in a form of the backend's own
(`AccRep`), with whatever the products read from `scratch + 3328`
(`TabRep`). For SSE2 (`Bodies.sse`), the accumulator is the polynomial
itself (`PolyIs`), there is no table, and a product is computed to
`scratch + 2048` with `vg_mlkem_multiply_ntts`'s code and added with
`vg_mlkem_add`'s (`mulAccB`), whose contracts `WP.inline` runs them with.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The second working space of the products, at `scratch + 2048`. -/
abbrev tmpR (p : Addr) : Region := pR (p + BitVec.ofNat 64 2048)

/-- What the products read, at `scratch + 3328`. -/
abbrev tabR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 3328, 256⟩

/-- A form of a polynomial in the 1024 bytes at an address, which writes
elsewhere keep. -/
structure AccRep where
  is : Mem → Addr → Poly → Prop
  frame : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → ∀ {p : Addr} {f : Poly},
    (∀ r ∈ rs, (pR p).Disjoint r) → is m p f → is m' p f

/-- What the products need at `scratch + 3328`, which writes elsewhere keep. -/
structure TabRep where
  is : Mem → Addr → Prop
  frame : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → ∀ {p : Addr},
    (∀ r ∈ rs, (tabR p).Disjoint r) → is m p → is m' p

/-- The accumulator at `rdi` of the zero polynomial. -/
def zeroK (R : AccRep) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [pR (s.gpr .rdi)] ∧ (retR s).Disjoint (pR (s.gpr .rdi))
  post s s' := R.is s'.mem (s.gpr .rdi) zero
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `NTT⁻¹` of the accumulator at `rdi`, to the polynomial at `rdi`, with the
working space at `rsi`. -/
def invAccK (R : AccRep) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ ∃ F, R.is s.mem (s.gpr .rdi) F
  post s s' := ∀ F, R.is s.mem (s.gpr .rdi) F → PolyIs s'.mem (s.gpr .rdi) (nttInv F)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The accumulator `o` at `rdi = rbp + 1024 o` plus `f = rsi ×_T g = rdx`, with
the working space at `scratch = rcx` (which `rbx` holds too) and at
`scratch + 2048`, and the table at `scratch + 3328`. -/
def mulAccK (R : AccRep) (T : TabRep) (o : Nat) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx), tabR (s.gpr .rcx)] ∧
    s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx), tmpR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdi)).Disjoint (tabR (s.gpr .rcx)) ∧
    (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdx)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdx)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rcx)).Disjoint (tmpR (s.gpr .rcx)) ∧ (pR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (tmpR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (tmpR (s.gpr .rcx)) ∧ (retR s).Disjoint (tabR (s.gpr .rcx)) ∧
    s.gpr .rbx = s.gpr .rcx ∧ s.gpr .rdi = s.gpr .rbp + BitVec.ofNat 64 (1024 * o) ∧ Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx) ∧
    T.is s.mem (s.gpr .rcx) ∧ ∃ A, R.is s.mem (s.gpr .rdi) A
  post s s' := ∀ A, R.is s.mem (s.gpr .rdi) A →
    R.is s'.mem (s.gpr .rdi) (add A (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx))))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The accumulator at `rdi` of `f = rsi ×_T g = rdx`, with what `mulAccK`
gives. -/
def mulSetK (R : AccRep) (T : TabRep) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx), tabR (s.gpr .rcx)] ∧
    s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx), tmpR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdi)).Disjoint (tabR (s.gpr .rcx)) ∧
    (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdx)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdx)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rcx)).Disjoint (tmpR (s.gpr .rcx)) ∧ (pR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (tmpR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (tmpR (s.gpr .rcx)) ∧ (retR s).Disjoint (tabR (s.gpr .rcx)) ∧
    s.gpr .rbx = s.gpr .rcx ∧ Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx) ∧ T.is s.mem (s.gpr .rcx)
  post s s' := R.is s'.mem (s.gpr .rdi) (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The polynomial at `rdi` plus the accumulator at `rsi`, to `rdi`. -/
def finK (R : AccRep) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rdi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧
    ∃ F, R.is s.mem (s.gpr .rsi) F
  post s s' := ∀ F, R.is s.mem (s.gpr .rsi) F → PolyIs s'.mem (s.gpr .rdi) (add (polyAt s.mem (s.gpr .rdi)) F)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- What `decryptMul`, `encryptMul` and `keygenMul` need of the code of a
backend: each piece meets its contract, and calls nothing. -/
structure BodiesOk (B : Bodies) (R : AccRep) (T : TabRep) : Prop where
  nttO : ∀ s, nttOK.pre s → ∃ t s', Exec isa B.nttO s t s' ∧ abiPreserved s s' ∧ nttOK.post s s'
  inv : ∀ s, (invAccK R).pre s → ∃ t s', Exec isa B.inv s t s' ∧ abiPreserved s s' ∧ (invAccK R).post s s'
  zero : ∀ s, (zeroK R).pre s → ∃ t s', Exec isa B.zero s t s' ∧ abiPreserved s s' ∧ (zeroK R).post s s'
  mulAcc : ∀ o, 1024 * o < 2 ^ 31 → ∀ s, (mulAccK R T o).pre s →
    ∃ t s', Exec isa (B.mulAcc o) s t s' ∧ abiPreserved s s' ∧ (mulAccK R T o).post s s'
  tab : ∀ s, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 3328) 256 →
    WP isa (.block B.tab) s fun s' => T.is s'.mem (s.gpr .rcx) ∧ Frame [tabR (s.gpr .rcx)] s.mem s'.mem ∧
      Keep [.r9, .r10] s s'
  nc : B.nttO.noCalls = true ∧ B.inv.noCalls = true ∧ B.zero.noCalls = true ∧ ∀ o, (B.mulAcc o).noCalls = true
  fin : ∀ s, (finK R).pre s → ∃ t s', Exec isa B.fin s t s' ∧ abiPreserved s s' ∧ (finK R).post s s'
  ncFin : B.fin.noCalls = true
  mulSet : ∀ s, (mulSetK R T).pre s → ∃ t s', Exec isa B.mulSet s t s' ∧ abiPreserved s s' ∧ (mulSetK R T).post s s'
  ncSet : B.mulSet.noCalls = true

/-! ## SSE2 -/

/-- The accumulator of `Bodies.sse`: the polynomial. -/
def accSse : AccRep := ⟨PolyIs, fun hf _ _ hd h => polyIs_frame hf hd h⟩

/-- `Bodies.sse` reads no table. -/
def tabSse : TabRep := ⟨fun _ _ => True, fun _ _ _ _ => trivial⟩

namespace ZeroB

/-- After `i` stores of sixteen bytes. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x0 : s.xmm .xmm0 = 0
  keep : Keep [.rdi, .rcx] s₀ s
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  zero : ∀ k < 4 * i, coeffAt s.mem (s₀.gpr .rdi) k = 0

end ZeroB

theorem zeroB_wp {s : State} (hw : pR (s.gpr .rdi) ∈ s.wr) :
    WP isa zeroB s fun s' => PolyIs s'.mem (s.gpr .rdi) zero ∧ Frame [pR (s.gpr .rdi)] s.mem s'.mem ∧
      Keep [.rdi, .rcx] s s' := by
  unfold zeroB
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.xmm .xmm0 = 0 ∧ s1.mem = s.mem ∧ Keep [] s s1) (by
        vrunm
        exact ⟨by simp [XBinOp.eval], fun r _ => by simp only [RegUpd.gpr_setXmm], rfl, rfl⟩)
      fun s1 ⟨hx, hm, k1⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 64) (by decide) (by decide) (ZeroB.Inv s) (fun u g _ => ?_)
    fun i hi u hI => ?_) fun u hI => ⟨polyIs_of_toNat fun k hk => ?_, hI.frame, hI.keep⟩
  · refine ⟨by rw [g.keep.gpr (by decide), k1.gpr (by decide)]; exact (BitVec.add_zero _).symm,
      by rw [g.keep.2.1, k1.2.1], by rw [g.keep.2.2, k1.2.2], by rw [g.xmm, hx], (k1.trans g.keep).mono (by decide),
      by rw [g.mem, hm]; exact Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  · have hc : InRegions u.wr (u.gpr .rdi) 16 := by
      rw [hI.wr, hI.rdi]; exact ⟨_, hw, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
    have hc' : InRegions (u.rd ++ u.wr) (u.gpr .rdi) 16 := let ⟨r, hr, h⟩ := hc; ⟨r, List.mem_append_right _ hr, h⟩
    vrunm [hc, hc']
    refine ⟨?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hI.rd,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hI.wr,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hI.x0, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, fun k hk => ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
      rw [hI.rdi, show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_off, Nat.mul_succ]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      exact hI.keep.gpr (by simp [hr])
    · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hI.keep.2.1
    · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hI.keep.2.2
    · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
      rw [hI.rdi]
      exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
    · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
      rw [hI.rdi, coeffAt_write128 _ _ (by omega_using [hi]) _ (by omega_using [hi, hk]), hI.x0]
      split
      · simp [dword]
      · exact hI.zero k (by omega_arith)
  · rw [n_eq] at hk
    rw [hI.zero k (by omega_using [hk]), zero, getElem!_pos _ k (by rw [n_eq]; exact hk)]
    simp

theorem zeroB_correct (s : State) (hs : (zeroK accSse).pre s) :
    ∃ t s', Exec isa zeroB s t s' ∧ abiPreserved s s' ∧ (zeroK accSse).post s s' := by
  obtain ⟨t, s', he, ⟨hP, hf, _⟩, hk⟩ := WP.keep [.rcx, .rdi] (zeroB_wp (s := s) (by rw [hs.2.1]; simp))
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2)), hP⟩

theorem nttInvB_acc (s : State) (hs : (invAccK accSse).pre s) :
    ∃ t s', Exec isa nttInvB s t s' ∧ abiPreserved s s' ∧ (invAccK accSse).post s s' := by
  obtain ⟨F, hF⟩ := hs.2.2.2.2.2
  obtain ⟨t, s', he, ha, hp⟩ := nttInvB_correct s ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hF.1⟩
  exact ⟨t, s', he, ha, fun F' hF' => by
    have e : polyAt s.mem (s.gpr .rdi) = F' := hF'.2
    simp only [inPlaceK, e] at hp
    exact hp⟩

theorem cov_mem {rs : List Region} {R : Region} (hR : R ∈ rs) : Covers [R] rs :=
  Covers.one ⟨R, hR, Region.contains_self _ _⟩

set_option linter.unusedSimpArgs false in
theorem mulAccB_correct (o : Nat) (ho : 1024 * o < 2 ^ 31) (s : State) (hs : (mulAccK accSse tabSse o).pre s) :
    ∃ t s', Exec isa (mulAccB o) s t s' ∧ abiPreserved s s' ∧ (mulAccK accSse tabSse o).post s s' := by
  obtain ⟨hrd, hwr, dAF, dAG, dAC, dAT, dAB, dFC, dFT, dGC, dGT, dCT, dCB, dTB,
    rA, rF, rG, rC, rT, rB, hbx, hbp, hRF, hRG, _, hAcc⟩ := hs
  generalize hA : s.gpr .rdi = A at *
  generalize hF : s.gpr .rsi = F at *
  generalize hG : s.gpr .rdx = G at *
  generalize hC : s.gpr .rcx = C at *
  have hW : WP isa (mulAccB o) s fun s' =>
      (∀ X, PolyIs s.mem A X → PolyIs s'.mem A (add X (multiplyNTTs (polyAt s.mem F) (polyAt s.mem G)))) ∧
      Frame [pR A, pR C, tmpR C] s.mem s'.mem := by
    unfold mulAccB
    -- `rdi = scratch + 2048`
    refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = C + BitVec.ofNat 64 2048 ∧
        s1.mem = s.mem ∧ Keep [.rdi] s s1) (by
          simp only [leaR]
          vrunm [hC]
          refine ⟨congrArg (C + ·) (by decide), fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, hm1, k1⟩ => ?_)
    have g1 : ∀ r, r ∉ [Reg.rdi] → s1.gpr r = s.gpr r := fun r hr => k1.gpr hr
    -- the product to `scratch + 2048`
    refine WP.seq (WP.inline (k := mulK) mulB_correct (rd := [pR F, pR G]) (wr := [tmpR C, pR C]) ?_ ?_ ?_
      (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_))
    · simp only [mulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        h1di, g1 .rsi (by decide), g1 .rdx (by decide), g1 .rcx (by decide), g1 .rsp (by decide), hF, hG, hC, hm1,
        retR]
      exact ⟨trivial, trivial, dFT.symm, dGT.symm, dCT.symm, dFC, dGC, rT, rF, rG, rC, hRF, hRG⟩
    · rw [k1.2.1, k1.2.2, hrd, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons ((cov_mem (by simp)).cons
        ((cov_mem (by simp)).cons Covers.nil)))
    · rw [k1.2.2, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons Covers.nil)
    simp only [mulK, State.withRegions_gpr, State.withRegions_mem, h1di, g1 .rsi (by decide),
      g1 .rdx (by decide), hF, hG, hm1] at hpost2
    have rbx_2 : s2.gpr .rbx = C := by rw [habi2.1 .rbx (by decide), g1 .rbx (by decide), hbx]
    have rbp_2 : s2.gpr .rbp = s.gpr .rbp := by rw [habi2.1 .rbp (by decide), g1 .rbp (by decide)]
    have rsp_2 : s2.gpr .rsp = s.gpr .rsp := by rw [habi2.1 .rsp (by decide), g1 .rsp (by decide)]
    -- the accumulator's address again, `rsi = scratch + 2048`
    refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = A ∧ s3.gpr .rsi = C + BitVec.ofNat 64 2048 ∧
        s3.mem = s2.mem ∧ Keep [.rdi, .rsi] s2 s3) (by
          simp only [leaR, List.cons_append, List.nil_append]
          vrunm [rbx_2, rbp_2, sx_ofNat ho]
          refine ⟨hbp.symm, congrArg (C + ·) (by decide), fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s3 ⟨h3di, h3si, hm3, k3⟩ => ?_)
    have rsp_3 : s3.gpr .rsp = s.gpr .rsp := by rw [k3.gpr (by decide), rsp_2]
    have hfA : ∀ r ∈ [tmpR C, pR C], (pR A).Disjoint r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dAT, dAC]
    rw [hm1] at hf2
    have hT3 : PolyIs s3.mem (C + BitVec.ofNat 64 2048) (multiplyNTTs (polyAt s.mem F) (polyAt s.mem G)) := by
      rw [hm3]; exact hpost2
    obtain ⟨X0, hX0⟩ := hAcc
    have hA3 : PolyIs s3.mem A (polyAt s.mem A) := by
      rw [hm3]; exact polyIs_frame hf2 hfA ⟨hX0.1, rfl⟩
    refine WP.inline (k := accK Spec.MlKem.add) add_correct (rd := [tmpR C]) (wr := [pR A]) ?_ ?_ ?_
      (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_)
    · simp only [accK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        h3di, h3si, rsp_3, retR]
      exact ⟨trivial, trivial, dAT, rA, rT, hA3.1, hT3.1⟩
    · rw [k3.2.1, k3.2.2, hrd2, hwr2, k1.2.1, k1.2.2, hrd, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons Covers.nil)
    · rw [k3.2.2, hwr2, k1.2.2, hwr]
      exact (cov_mem (by simp)).cons Covers.nil
    simp only [accK, State.withRegions_gpr, State.withRegions_mem, h3di, h3si] at hpost4
    rw [hA3.2, hT3.2] at hpost4
    rw [hm3] at hf4
    refine ⟨fun X hX => ?_, ?_⟩
    · rw [← hX.2]; exact hpost4
    · refine (hf2.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans
        (hf4.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10] hW (by rfl)
  refine ⟨t, s', he, abiPreserved_of_exec (by rfl) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨rA, rC, rT⟩)), fun X hX => ?_⟩
  rw [hA, hF, hG]
  rw [hA] at hX
  exact hP X hX

/-- `vg_mlkem_add`'s code adds the polynomial at `rsi`. -/
theorem finB_correct (s : State) (hs : (finK accSse).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.add s t s' ∧ abiPreserved s s' ∧ (finK accSse).post s s' := by
  obtain ⟨hrd, hwr, hd, rA, rF, hRA, F, hF⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := add_correct s ⟨hrd, hwr, hd, rA, rF, hRA, hF.1⟩
  exact ⟨t, s', he, ha, fun G hG => by rw [← hG.2]; exact hp⟩

/-- `vg_mlkem_multiply_ntts`'s code stores the product. -/
theorem mulB_set (s : State) (hs : (mulSetK accSse tabSse).pre s) :
    ∃ t s', Exec isa mulB s t s' ∧ abiPreserved s s' ∧ (mulSetK accSse tabSse).post s s' := by
  obtain ⟨hrd, hwr, dAF, dAG, dAC, _, _, dFC, _, dGC, _, _, _, _, rA, rF, rG, rC, _, _, _, hRF, hRG, _⟩ := hs
  have hW : WP isa mulB s fun s' =>
      PolyIs s'.mem (s.gpr .rdi) (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx))) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s'.mem := by
    refine WP.inline (k := mulK) mulB_correct (rd := [pR (s.gpr .rsi), pR (s.gpr .rdx)])
      (wr := [pR (s.gpr .rdi), pR (s.gpr .rcx)]) ?_ ?_ ?_ (fun s2 _ _ _ hf2 _ hpost2 => ?_)
    · simp only [mulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        retR]
      exact ⟨trivial, trivial, dAF, dAG, dAC, dFC, dGC, rA, rF, rG, rC, hRF, hRG⟩
    · rw [hrd, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons ((cov_mem (by simp)).cons
        ((cov_mem (by simp)).cons Covers.nil)))
    · rw [hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons Covers.nil)
    simp only [mulK, State.withRegions_gpr, State.withRegions_mem] at hpost2
    exact ⟨hpost2, hf2⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10] hW (by rfl)
  exact ⟨t, s', he, abiPreserved_of_exec (by rfl) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨rA, rC⟩)), hP⟩

theorem BodiesOk.sse : BodiesOk .sse accSse tabSse :=
  ⟨nttOB_correct, nttInvB_acc, zeroB_correct, mulAccB_correct,
    fun _ _ => WP.block_nil_iff.mpr ⟨trivial, Frame.refl _ _, Keep.refl _ _⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun _ => rfl⟩, finB_correct, by decide +kernel,
    mulB_set, by decide +kernel⟩

end VG.Proof.MlKem.X86_64
