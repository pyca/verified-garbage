import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Impl.MlKem.X86_64.KpkeMul

/-!
# ML-KEM on x86-64: the SSE2 arithmetic without its MXCSR region

The code `vg_mlkem*_decrypt_mul` inlines (`Bodies.sse`): `vg_mlkem_ntt`'s,
storing its result through `r10` (`nttOB`, against `nttOK`),
`vg_mlkem_inv_ntt`'s (`nttInvB`) and `vg_mlkem_multiply_ntts`'s (`mulB`),
each without the MXCSR prologue and epilogue of its function, meet the
contracts of the functions: the proofs are those of the functions
(`Ntt.lean`, `NttInv.lean`, `Mul.lean`) without `withMxcsr_ok`.
-/

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
      refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, ?_, fun _ h => absurd h (by omega)⟩
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
    · exact polyIs_of_toNat fun k hk => hI.done k (by rw [n_eq] at hk; omega)
  obtain ⟨t, s', he, ⟨hP', hf⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1⟩)), hP'⟩

end Mul

theorem mulB_correct (s : State) (hs : mulK.pre s) :
    ∃ t s', Exec isa mulB s t s' ∧ abiPreserved s s' ∧ mulK.post s s' :=
  Mul.bodyCorrect hs

end VG.Proof.MlKem.X86_64
