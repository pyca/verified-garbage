module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Precomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Precomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: the taint checks

The code between the call and the branches, checked by the taint analysis
from the stack pointer and, after the call, the registers holding `k`, the
zero-extended `hash`, `digest` and `digest_len` (`s1`–`s4`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Ver

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (lenCheck .a1)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem ret0_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block ret0) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem afterPub_taint (h : Pins Φ [.s1, .s2, .s3, .s4]) :
    RelCT isa (Two Φ) (.seq (.block encArgs) (.seq encode (.seq tail (.seq (.block mask) (.block restore)))))
      fun _ _ => True :=
  two_taint [.s1, .s2, .s3, .s4] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Sig.RISCV64.Ver
