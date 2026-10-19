module
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKg
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16

import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeEncV
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
meta import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.Add16
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
import VerifiedGarbage.Proof.MlKem.X86_64.KgMul16
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.Widen
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncodeAvx2
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompressAvx2
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.Encode1024
meta import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
meta import VerifiedGarbage.Proof.MlKem.X86_64.Add16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragL
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMul16
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
meta import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.Widen
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncodeAvx2
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompressAvx2
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_kpke_keygen`, verified

The proof of `Proof/MlKem/X86_64/KpkeKg.lean` for ML-KEM-1024 with AVX2, its
constant time, and its contract implying the shared one of
`Spec/MlKem/Kpke16.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

theorem kpkeKg1024Y_ct :
    ConstantTime isa (kpkeKgK kem1024).pre (kpkeKgK kem1024).pub (kpkeKg kem1024 .avx2 keygenMul16Y) := by
  unfold kpkeKg
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    (R := fun (s₁ s₂ : State) => ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], s₁.gpr r = s₂.gpr r) ?_ ?_)
  · refine ((RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (fun x y h => kpkeKg_agree kem1024 x y h.1 h.2.1 h.2.2) [] (by taint_decide)).wpDep
      (F := fun σ s => KpkeKg.EO kem1024 σ 0 0 s) fun s₁ s₂ h =>
        ⟨KpkeKg.pre_wp keWf1024 kgMul16Y4_correct (by lit_decide) h.1,
          KpkeKg.pre_wp keWf1024 kgMul16Y4_correct (by lit_decide) h.2.1⟩).mono
      (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, e₁, e₂⟩ => kpkeKg_mid hp e₁ e₂
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r15, .rsp])
      (fun x y h => X86_64.Taint.agree_ofRegs h) [] (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial

theorem kpkeKg1024Y_correct : ∀ s, (kpkeKgK kem1024).pre s →
    ∃ t s', Exec isa (kpkeKg kem1024 .avx2 keygenMul16Y) s t s' ∧ abiPreserved s s' ∧
      (kpkeKgK kem1024).post s s' :=
  KpkeKg.kpkeKg_correct PrimsOk.avx2 keWf1024 kgMul16Y4_correct (by lit_decide) (by lit_decide) (by lit_decide)

theorem kpkeKg1024_of {c : Prog isa}
    (hc : ∀ s, (kpkeKgK kem1024).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
      (kpkeKgK kem1024).post s s')
    (hct : ConstantTime isa (kpkeKgK kem1024).pre (kpkeKgK kem1024).pub c) :
    Verified X86_64.target c (Spec.MlKem.kpkeKeyGenContract 4 X86_64.abi) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [kpkeKeyGenContract, kpkeKeyGenSig, kpkeKgK, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, kem1024, retR, mlKem1024]
      post := by sig_implies_post [kpkeKeyGenContract, kpkeKeyGenSig, kpkeKgK, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, kem1024, retR, mlKem1024]
      pub := by sig_implies_pub [kpkeKeyGenContract, kpkeKeyGenSig, kpkeKgK, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, kem1024, retR, mlKem1024]
      sat := by
        refine ⟨kpkeKgSat kem1024, ?_⟩
        sig_pre [kpkeKeyGenContract, kpkeKeyGenSig, kpkeKgK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReducedW16_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

theorem kpkeKg1024Y_verified :
    Verified X86_64.target (kpkeKg kem1024 .avx2 keygenMul16Y) (Spec.MlKem.kpkeKeyGenContract 4 X86_64.abi) :=
  kpkeKg1024_of kpkeKg1024Y_correct kpkeKg1024Y_ct

end VG.Proof.MlKem1024.X86_64
