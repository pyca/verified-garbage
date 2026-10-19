module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
public import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
public import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunRdi1
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvTop
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt_avx2` and `vg_mlkem_inv_ntt_avx2`

Both run on registers in two passes (`NttRegs.lean`), inside the MXCSR
prologue and epilogue: `NttR.nttR_ok` and `NttR.nttIR_ok` give their
results.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## `vg_mlkem_ntt_avx2` -/

theorem nttY_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa nttAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttAvx2 s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold nttAvx2
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.mono (NttR.nttR_ok NttR.check_rdi (.inl rfl) (by rw [hsi1, k1.2.2]; exact hw)
      (by rw [hdi1, k1.2.1, k1.2.2]; exact List.mem_append_right _ hwf) (by rw [hdi1, k1.2.2]; exact hwf)
      (by rw [hdi1, hsi1]; exact hd) (by rw [hdi1, hsi1]; exact hd) (by rw [hdi1]; exact hF1.1))
      fun s2 ⟨hP, hf2, _⟩ => ⟨?_, ?_⟩
    · rw [hdi1, hF1.2] at hP; exact hP
    · rw [hdi1, hsi1] at hf2
      refine (frame_fs f1 ?_).trans hf2
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact .inr (mx_sub _)
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem nttY_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub nttAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttY_verified : Verified X86_64.target nttAvx2 (Spec.MlKem.nttContract X86_64.abi) :=
  Verified.of_correct nttY_correct nttY_ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlKem.X86_64
