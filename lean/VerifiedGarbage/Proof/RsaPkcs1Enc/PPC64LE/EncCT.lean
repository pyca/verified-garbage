module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Precomputed

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: the taint checks

The code around the call, checked by the taint analysis from the stack
pointer and the registers holding public values: after the setup, `PS`'s
place and length (loaded from the stack), `EM`'s place and the message's
place and length; after the call, `out` and `k` in `r28` and `r29`. `PS`
and `M` are secret: only copied, and `PS`'s zero test only masks.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.Proof.RsaPkcs1Sig.PPC64LE

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block setup) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem preCall_taint (h : Pins Φ [.r4, .r9, .r10, .r11, .r12]) : RelCT isa (Two Φ) preCall fun _ _ => True :=
  two_taint [.r4, .r9, .r10, .r11, .r12] h (by taint_decide)

theorem tail_taint (h : Pins Φ [.r28, .r29]) : RelCT isa (Two Φ) tail fun _ _ => True :=
  two_taint [.r28, .r29] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc
