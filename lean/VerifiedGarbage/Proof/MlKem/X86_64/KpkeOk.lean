module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset

/-! # ML-KEM on x86-64: the K-PKE functions of ML-KEM-768, safe to call -/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem KpkeOk.k768 : KpkeOk kem768 where
  kg := ⟨kpkeKg768Y_correct, kpkeKg768Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  enc := ⟨kpkeEnc768Y_correct, kpkeEnc768Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  dec := ⟨kpkeDec768Y_correct, kpkeDec768Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩

end VG.Proof.MlKem.X86_64
