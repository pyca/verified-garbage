module

import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the AVX2 arithmetic without its MXCSR region

As `KpkeBodies.lean` and `KpkeAcc.lean`, for `Bodies.avx2`:
`vg_mlkem_ntt_avx2`'s code storing through `r10` (`nttOBY`), without
`withMxcsr`, meets the contract of the function (the proof is that of
`NttAvx2.lean` without `withMxcsr_ok`), and the pieces around the
accumulator in words (`AccY.lean`, `AccInvY.lean`) meet theirs.
-/

@[expose] public section

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

theorem BodiesOk.avx2 : BodiesOk .avx2 accY tabY :=
  ⟨nttOBY_correct, nttInvAccY_correct, zeroAccY_correct, fun _ _ _ hs => MulAccY.correct hs,
    fun s hin => tabAccY_wp s hin, ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun _ => (by decide +kernel : mulAccY.noCalls = true)⟩⟩

end VG.Proof.MlKem.X86_64
