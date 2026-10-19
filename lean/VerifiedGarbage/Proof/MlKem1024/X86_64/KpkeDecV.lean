module
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem

import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
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
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
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
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.Encode1024
meta import VerifiedGarbage.Proof.MlKem.PolyW
meta import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragL
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
meta import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncodeAvx2
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompressAvx2
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_kpke_decrypt`, verified

The proof of `Proof/MlKem/X86_64/KpkeDec.lean` for ML-KEM-1024 and each
backend, its constant time, and its contract implying the shared one of
`Spec/MlKem/Kpke16.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

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
    Verified X86_64.target c (mlKem1024.kpkeDecryptContract X86_64.abi) :=
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
    Verified X86_64.target (kpkeDec kem1024 .avx2 dmInnerY) (mlKem1024.kpkeDecryptContract X86_64.abi) :=
  kpkeDec1024_of kpkeDec1024Y_correct kpkeDec1024Y_ct

end VG.Proof.MlKem1024.X86_64
