module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Sign
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Sign
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the blocks' taint

The saves, the call's arguments and the restores address only the frame,
through `r12 = r1`; `encode` branches on `hash`, `digest_len` and `k` and
addresses `EM` and `digest` (`r4`–`r8`); the zeros go to `out` (`r26`) or
`EM`, `k` (`r28`) bytes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.Bignum.PPC64LE (Two Pins two_taint)

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ encArgs)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem encode_taint (h : Pins Φ [.r4, .r5, .r6, .r7, .r8]) :
    RelCT isa (Two Φ) Impl.RsaPkcs1Sig.PPC64LE.encode fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem zeroOut_taint (h : Pins Φ [.r26, .r28]) : RelCT isa (Two Φ) zeroOut fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem callArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block callArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem wipe_taint (h : Pins Φ [.r28]) : RelCT isa (Two Φ) wipe fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
