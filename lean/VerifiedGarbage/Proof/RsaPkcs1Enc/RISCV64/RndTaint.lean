module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Random
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Random

/-!
# `vg_rsa_pkcs1_encrypt_random` on RISC-V: the taint checks

The pieces of code whose addresses and branches depend only on the stack
pointer and on registers that hold public values: the setup; the scan's
load (from `rand` and the index `t2`) and store (to `PS` at the count `t5`);
the call's arguments (to `tape`, `a2`) and its stack arguments; the end of
the accepting path (from `psLen`, `s1`); and the rejecting path, from the
count of octets kept (`t5`), `out` and its length (`a0`, `a4`), `psLen`,
`rand_len` (`t4`) and `tape`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Rnd

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Random VG.Proof.RsaPkcs1Sig.RISCV64

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block setup) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem load_taint (h : Pins Φ [.t3, .t2]) :
    RelCT isa (Two Φ) (.block [.add .t6 .t3 .t2, .load .b .t6 .t6 0, .addi .t2 .t2 1]) fun _ _ => True :=
  two_taint [.t3, .t2] h (by taint_decide)

theorem store_taint (h : Pins Φ [.t1, .t5]) :
    RelCT isa (Two Φ) (.block [.add .t0 .t1 .t5, .store .b .t6 .t0 0, .addi .t5 .t5 1]) fun _ _ => True :=
  two_taint [.t1, .t5] h (by taint_decide)

theorem nil_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block []) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem li_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.li .t0 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem sub_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.sub .t0 .t4 .t2]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem callRegs_taint (h : Pins Φ [.a2]) : RelCT isa (Two Φ) (.block callRegs) fun _ _ => True :=
  two_taint [.a2] h (by taint_decide)

theorem callStack_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block callStack) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem accTail_taint (h : Pins Φ [.s1]) :
    RelCT isa (Two Φ) (.seq (.block status) (.seq Impl.RsaPkcs1Sig.RISCV64.fillLoop
      (.block Impl.RsaPkcs1Sig.RISCV64.restore))) fun _ _ => True :=
  two_taint [.s1] h (by taint_decide)

theorem reject_taint (h : Pins Φ [.t5, .a0, .a4, .s1, .t4, .a2]) : RelCT isa (Two Φ) reject fun _ _ => True :=
  two_taint [.t5, .a0, .a4, .s1, .t4, .a2] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Rnd
