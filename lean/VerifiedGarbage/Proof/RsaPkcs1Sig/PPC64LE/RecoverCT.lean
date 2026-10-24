module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode

/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: the taint checks

The code between the call and the branches, checked by the taint analysis
from the stack pointer and the registers holding public values: `out` and
`out_len` in `r3` and `r4` on entry, and `out`, `out_len`, `k` and the
zero-extended `hash` in `r28`–`r31` after the call.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem zeroArgs_taint (h : Pins Φ [.r3, .r4]) : RelCT isa (Two Φ) zeroArgs fun _ _ => True :=
  two_taint [.r3, .r4] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem afterPub_taint (h : Pins Φ [.r28, .r29, .r30, .r31]) :
    RelCT isa (Two Φ) (.seq (.block encArgs) (.seq encode (.seq tail (.block restore)))) fun _ _ => True :=
  two_taint [.r28, .r29, .r30, .r31] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec
