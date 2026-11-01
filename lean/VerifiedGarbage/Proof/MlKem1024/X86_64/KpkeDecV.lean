module
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem

import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_kpke_decrypt`, verified

The proof of `Proof/MlKem/X86_64/KpkeDec.lean` for ML-KEM-1024 and each
backend, its constant time, and its contract implying the shared one of
`Proof/MlKem/Kpke16Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Proof.MlKem

theorem kdWf1024 : KpkeDec.KdWf kem1024 := ⟨.inr rfl, by decide, by decide, by decide⟩

theorem kpkeDec1024Y_ct :
    ConstantTime isa (kpkeDecK kem1024).pre (kpkeDecK kem1024).pub (kpkeDec kem1024 .avx2 dmInnerY) :=
  VG.Taint.constantTime (A := taint) _ (kpkeDec_agree kem1024) (by taint_decide)

theorem kpkeDec1024Y_correct : ∀ s, (kpkeDecK kem1024).pre s →
    ∃ t s', Exec isa (kpkeDec kem1024 .avx2 dmInnerY) s t s' ∧ abiPreserved s s' ∧ (kpkeDecK kem1024).post s s' :=
  KpkeDec.kpkeDec_correct PrimsOk.avx2 calls1024 kdWf1024 dmOkY (by lit_decide) (by lit_decide)
    (by lit_decide) (by lit_decide) (by lit_decide)

theorem kpkeDec1024_of {c : Prog isa}
    (hc : ∀ s, (kpkeDecK kem1024).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
      (kpkeDecK kem1024).post s s')
    (hct : ConstantTime isa (kpkeDecK kem1024).pre (kpkeDecK kem1024).pub c) :
    Verified X86_64.target c (Proof.MlKem.Params.kpkeDecryptContract mlKem1024 X86_64.abi) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi,
        X86_64.argRegs, kScr, Kem.k, Kem.ctLen, kem1024, retR, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi,
        X86_64.argRegs, kScr, Kem.k, Kem.ctLen, kem1024, retR, Params.ctLen, mlKem1024]
      pub := by sig_implies_pub [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi,
        X86_64.argRegs, kScr, Kem.k, Kem.ctLen, kem1024, retR, Params.ctLen, mlKem1024]
      sat := by
        refine ⟨kpkeDecSat kem1024, ?_⟩
        sig_pre [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

theorem kpkeDec1024Y_verified :
    Verified X86_64.target (kpkeDec kem1024 .avx2 dmInnerY) (Proof.MlKem.Params.kpkeDecryptContract mlKem1024 X86_64.abi) :=
  kpkeDec1024_of kpkeDec1024Y_correct kpkeDec1024Y_ct

end VG.Proof.MlKem1024.X86_64
