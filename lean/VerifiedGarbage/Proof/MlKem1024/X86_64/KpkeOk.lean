module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16

/-! # ML-KEM-1024 on x86-64: the K-PKE functions, safe to call -/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64

theorem KpkeOk.k1024 : KpkeOk kem1024 where
  kg := ⟨kpkeKg1024Y_correct, kpkeKg1024Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  enc := ⟨kpkeEnc1024Y_correct, kpkeEnc1024Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  dec := ⟨kpkeDec1024Y_correct, kpkeDec1024Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩

end VG.Proof.MlKem1024.X86_64
