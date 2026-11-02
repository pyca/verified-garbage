module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Precomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Precomputed

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on RISC-V: the taint checks

The setup from the stack pointer; the code before the call from the
registers holding `PS`, its length, `EM`'s place after the first two bytes,
the message and its length (`t2`–`t4`, `a6`, `a7`), which the setup loads;
and the code after the call from `out` and `k` (`s1`, `s2`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Enc

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Precomputed VG.Proof.RsaPkcs1Sig.RISCV64

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block setup) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem preCall_taint (h : Pins Φ [.t2, .t3, .t4, .a6, .a7]) : RelCT isa (Two Φ) preCall fun _ _ => True :=
  two_taint [.t2, .t3, .t4, .a6, .a7] h (by taint_decide)

theorem tail_taint (h : Pins Φ [.s1, .s2]) : RelCT isa (Two Φ) tail fun _ _ => True :=
  two_taint [.s1, .s2] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Enc
