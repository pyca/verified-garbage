import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodies

/-!
# ML-KEM on x86-64: the AVX2 arithmetic without its MXCSR region

As `KpkeBodies.lean`, for `Bodies.avx2`: `vg_mlkem_ntt_avx2`'s code storing
through `r10` (`nttOBY`), `vg_mlkem_inv_ntt_avx2`'s (`nttInvBY`) and
`vg_mlkem_multiply_ntts_avx2`'s (`mulBY`), without `withMxcsr`, meet the
contracts of the functions; the proofs are those of `NttAvx2.lean` and
`MulAvx2.lean` without `withMxcsr_ok`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `mov rdi, r10`, keeping both lanes of the vector registers. -/
theorem movDiR10Y_ok (s : State) :
    WP isa (.block [.mov .rdi (.reg .r10)]) s fun s' => s'.gpr .rdi = s.gpr .r10 ∧ s'.mem = s.mem ∧
      (∀ r l, s'.lane r l = s.lane r l) ∧ Keep [.rdi] s s' := by
  vrunm [lane_setReg]
  refine ⟨fun _ _ => trivial, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem nttOBY_correct (s : State) (hs : nttOK.pre s) :
    ∃ t s', Exec isa nttOBY s t s' ∧ abiPreserved s s' ∧ nttOK.post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwt : pR (s.gpr .r10) ∈ s.wr := by rw [hs.2.1]; simp
  have hrf : pR (s.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hs.1]; simp
  have hW : WP isa nttOBY s fun s' => PolyIs s'.mem (s.gpr .r10) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .r10), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold nttOBY
    refine WP.seq (WP.mono (ypro_ok zmTab zmTab_eq rfl rfl ⟨hs.2.2.2.2.2.2, rfl⟩ hrf hw hs.2.2.1)
      fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := k2.gpr (by decide)
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2]; exact hw
    refine LIY.seq hsi2 hw2 (fwdLayY_ok 128 1 (by decide) (by decide)) ?_
      ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LIY.seq hsi2 hw2 (fwdLayY_ok 64 2 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (fwdLayY_ok 32 4 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (fwdLayY_ok 16 8 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 fwdLay8Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 fwdLay4Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 fwdLay2Y_ok ?_ hI
    intro s3 hI
    refine WP.seq (WP.mono (movDiR10Y_ok s3) fun s4 ⟨hdi4, hm4, hl4, k4⟩ => ?_)
    have k34 := hI.keep.trans k4
    have hS4 := hI.S
    rw [← hm4] at hS4
    refine WP.mono (yepi_ok (s := s4) (fun l hl => ⟨by rw [State.proj_xmm, hl4]; exact (hI.c l hl).q,
        by rw [State.proj_xmm, hl4]; exact (hI.c l hl).qinv⟩)
      hS4 (by rw [hdi4, hI.keep.gpr (by decide), k2.gpr (by decide)])
      (by rw [k34.gpr (by decide), hsi2]) (by rw [k34.2.2, k2.2.2]; exact hwt)
      (by rw [k34.2.2]; exact hw2) hs.2.2.2.1) fun s5 ⟨hP, hf5⟩ => ⟨?_, ?_⟩
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

theorem nttInvBY_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa nttInvBY s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvBY s fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold nttInvBY
    refine WP.seq (WP.mono (ypro_ok zmTabInv zmTabInv_eq rfl rfl ⟨hs.2.2.2.2.2, rfl⟩ (List.mem_append_right _ hwf)
      hw hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := k2.gpr (by decide)
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2]; exact hw
    refine LIY.seq hsi2 hw2 invLay2Y_ok ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LIY.seq hsi2 hw2 invLay4Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 invLay8Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 16 112 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 32 120 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 64 124 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 128 126 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (fun _ hc hsi hS _ hw => yscale_ok hc hsi hS hw) ?_ hI
    intro s3 hI
    refine WP.mono (yepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide)])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨?_, ?_⟩
    · rw [nttInv_eq_layers]
      simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_)) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), hP⟩

namespace MulY

open VG.Proof.MlKem.X86_64.Mul (hP fP gP sP F G)

theorem bodyCorrect {s₀ : State} (hp : mulK.pre s₀) :
    ∃ t s', Exec isa mulBY s₀ t s' ∧ abiPreserved s₀ s' ∧ mulK.post s₀ s' := by
  have hw : pR (sP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hW : WP isa mulBY s₀ fun s' =>
      PolyIs s'.mem (hP s₀) (multiplyNTTs (F s₀) (G s₀)) ∧ Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s'.mem := by
    unfold mulBY
    refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r10 = sP s₀ ∧ s1.mem = s₀.mem ∧
      Keep [.r10] s₀ s1) (by
        vrunm
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h10, hm1, k1⟩ => ?_)
    refine WP.seq ?_
    simp only [mulProY, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (wordTab_gen gTabY gTabY_lt (by decide) h10 (by rw [k1.2.2]; exact hw))
      fun s3 ⟨ht, f3, k3, _, _⟩ => ?_
    rw [← List.append_assoc]
    refine WP.mono (consts_ok s3) fun s4 ⟨hc4, hr4, h84, hm4, _, k4⟩ => ?_
    have h84' : s4.gpr .r8 = sP s₀ := by rw [h84, k3.gpr (by decide), h10]
    have k14 := (k1.trans k3).trans k4
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (Inv s₀) (fun s g hy _ => ?_)
      fun i hi s hI => step hp hi hI) fun s5 hI => ?_)
    · have k := k14.trans g.keep
      have hl : ∀ r l, s.lane r l = s4.lane r l := fun r l => by
        simp only [State.lane]; rw [g.xmm, hy]
      refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, ?_, fun _ h => absurd h (by bdd_omega)⟩
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [g.keep.gpr (by decide), h84']; exact (add_ofNat_zero _).symm
      · exact fun l hl' => ⟨by rw [State.proj_xmm, hl]; exact (hc4 l hl').q,
          by rw [State.proj_xmm, hl]; exact (hc4 l hl').qinv⟩
      · exact fun l hl' => by rw [hl]; exact hr4 l hl'
      · rw [g.mem, hm4, ← hm1]
        refine frame_fs (fP := hP s₀) f3 ?_
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact .inr (pR_sub_tab _)
      · intro k hk; rw [g.mem, hm4]; exact ht k hk
    · vrunm
      exact ⟨polyIs_of_toNat fun k hk => hI.done k (by rw [n_eq] at hk; omega), hI.frame⟩
  obtain ⟨t, s', he, ⟨hP', hf⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1⟩)), hP'⟩

end MulY

theorem mulBY_correct (s : State) (hs : mulK.pre s) :
    ∃ t s', Exec isa mulBY s t s' ∧ abiPreserved s s' ∧ mulK.post s s' :=
  MulY.bodyCorrect hs

end VG.Proof.MlKem.X86_64
