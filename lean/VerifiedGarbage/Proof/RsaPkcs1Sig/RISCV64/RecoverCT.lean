module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode

/-!
# `vg_rsa_pkcs1_recover_precomputed` on RISC-V: the taint checks

The code between the call and the branches, checked by the taint analysis
from the stack pointer and, after the call, the registers holding `out`,
`out_len`, `k` and the zero-extended `hash` (`s1`–`s4`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Rec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (lenCheck .a3)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem zeroArgs_taint (h : Pins Φ [.a0, .a1]) : RelCT isa (Two Φ) zeroArgs fun _ _ => True :=
  two_taint [.a0, .a1] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem afterPub_taint (h : Pins Φ [.s1, .s2, .s3, .s4]) :
    RelCT isa (Two Φ) (.seq (.block encArgs) (.seq encode (.seq tail (.block restore)))) fun _ _ => True :=
  two_taint [.s1, .s2, .s3, .s4] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Sig.RISCV64.Rec
