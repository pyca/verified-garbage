module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEnc

import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEnc
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
meta import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_kpke_encrypt`, verified

The proof of `Proof/MlKem/X86_64/KpkeEnc.lean` for ML-KEM-1024 with AVX2,
its constant time, and its contract implying the shared one of
`Proof/MlKem/Kpke16Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Proof.MlKem

theorem keWf1024 : KpkeEnc.KeWf kem1024 := ⟨.inr rfl, by decide, by decide, by decide⟩

theorem kpkeEnc1024Y_ct :
    ConstantTime isa (kpkeEncK kem1024).pre (kpkeEncK kem1024).pub (kpkeEnc kem1024 .avx2 encryptMul16Y) := by
  unfold kpkeEnc
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    (R := fun (s₁ s₂ : State) => ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r) ?_ ?_)
  · refine ((RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (fun x y h => kpkeEnc_agree kem1024 x y h.1 h.2.1 h.2.2) [] (by taint_decide)).wpDep
      (F := fun σ s => KpkeEnc.EU kem1024 σ 0 s) fun s₁ s₂ h =>
        ⟨KpkeEnc.pre_wp PrimsOk.avx2 keWf1024 encMul16Y4_correct (by lit_decide) (by lit_decide) h.1,
          KpkeEnc.pre_wp PrimsOk.avx2 keWf1024 encMul16Y4_correct (by lit_decide) (by lit_decide) h.2.1⟩).mono
      (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, e₁, e₂⟩ => kpkeEnc_mid hp e₁ e₂
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (fun x y h => X86_64.Taint.agree_ofRegs h) [] (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial

theorem kpkeEnc1024Y_correct : ∀ s, (kpkeEncK kem1024).pre s →
    ∃ t s', Exec isa (kpkeEnc kem1024 .avx2 encryptMul16Y) s t s' ∧ abiPreserved s s' ∧
      (kpkeEncK kem1024).post s s' :=
  KpkeEnc.kpkeEnc_correct PrimsOk.avx2 calls1024 keWf1024 encMul16Y4_correct (by lit_decide) (by lit_decide)
    (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)

theorem kpkeEnc1024_of {c : Prog isa}
    (hc : ∀ s, (kpkeEncK kem1024).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
      (kpkeEncK kem1024).post s s')
    (hct : ConstantTime isa (kpkeEncK kem1024).pre (kpkeEncK kem1024).pub c) :
    Verified X86_64.target c (Proof.MlKem.Params.kpkeEncryptContract mlKem1024 X86_64.abi) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, Kem.ctLen, kem1024, retR, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, encCt, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, Kem.du, Kem.dv, Kem.ctLen, kem1024, retR, Params.ctLen, mlKem1024]
      pub := by sig_implies_pub [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, Kem.ctLen, kem1024, retR, Params.ctLen, mlKem1024]
      sat := by
        refine ⟨kpkeEncSat kem1024, ?_⟩
        sig_pre [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReducedW16_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

theorem kpkeEnc1024Y_verified :
    Verified X86_64.target (kpkeEnc kem1024 .avx2 encryptMul16Y) (Proof.MlKem.Params.kpkeEncryptContract mlKem1024 X86_64.abi) :=
  kpkeEnc1024_of kpkeEnc1024Y_correct kpkeEnc1024Y_ct

end VG.Proof.MlKem1024.X86_64
