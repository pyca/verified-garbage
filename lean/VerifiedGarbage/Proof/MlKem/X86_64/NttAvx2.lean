module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt_avx2` and `vg_mlkem_inv_ntt_avx2`

The prologue leaves the table of zetas (in the order the layers read it) and
`f` as words in `scratch` (`ypro_ok`), the lazy layers take them to the
words of `NTT(f)` or `NTT⁻¹(f)` (`nttLazy_ok`, `nttInvLazy_ok`), and the
epilogue unpacks `S` into `f` (`yepi_ok`).
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
    refine WP.seq (WP.mono (ypro_ok zmTab zmTab_eq hdi1 hsi1 hF1 (by rw [k1.2.1, k1.2.2]; exact List.mem_append_right _ hwf)
      (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine WP.seq (WP.mono (nttLazy_ok hc hsi2 hS hT hw2) fun s3 ⟨hS3, hb3⟩ => ?_)
    refine WP.mono (yepi_ok hb3.consts hS3 (by rw [hb3.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hb3.keep.gpr (by decide), hsi2]) (by rw [hb3.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hb3.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨hP, ?_⟩
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hb3.frame ?_).trans (frame_fs hf4 ?_))) <;>
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

/-! ## `vg_mlkem_inv_ntt_avx2` -/

theorem nttInvY_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa nttInvAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvAvx2 s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold nttInvAvx2
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (ypro_ok zmTabInv zmTabInv_eq hdi1 hsi1 hF1 (by rw [k1.2.1, k1.2.2]; exact List.mem_append_right _ hwf)
      (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine WP.seq (WP.mono (nttInvLazy_ok hc hsi2 hS hT hw2) fun s3 ⟨hS3, hb3⟩ => ?_)
    refine WP.mono (yepi_ok hb3.consts hS3 (by rw [hb3.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hb3.keep.gpr (by decide), hsi2]) (by rw [hb3.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hb3.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨hP, ?_⟩
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hb3.frame ?_).trans (frame_fs hf4 ?_))) <;>
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

theorem nttInvY_ct : ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub nttInvAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttInvY_verified : Verified X86_64.target nttInvAvx2 (Spec.MlKem.nttInvContract X86_64.abi) :=
  Verified.of_correct nttInvY_correct nttInvY_ct (by
    mlkem_implies [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlKem.X86_64
