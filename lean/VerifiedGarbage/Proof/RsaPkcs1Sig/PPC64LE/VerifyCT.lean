module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Precomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Precomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode

/-!
# `vg_rsa_pkcs1_verify_precomputed` on PPC64LE: the taint checks

The code between the call and the branches, checked by the taint analysis
from the stack pointer and, after the call, the registers holding `k`, the
zero-extended `hash`, `digest` and `digest_len` (`r28`–`r31`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Ver

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Precomputed

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem ret0_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block ret0) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem afterPub_taint (h : Pins Φ [.r28, .r29, .r30, .r31]) :
    RelCT isa (Two Φ) (.seq (.block encArgs) (.seq encode (.seq tail (.seq (.block mask) (.block restore)))))
      fun _ _ => True :=
  two_taint [.r28, .r29, .r30, .r31] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Sig.PPC64LE.Ver
