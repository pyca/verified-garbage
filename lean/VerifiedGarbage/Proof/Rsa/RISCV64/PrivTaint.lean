module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Rsa.RISCV64.Priv
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# `vg_rsa_private_checked` on RISC-V: the blocks' taint

The blocks between the calls address only the frame and our stack
arguments, through `t0 = sp` and `t6 = sp + frameBytes` (`setup_taint`,
`preArgs_taint`, `pubArgs_taint`); the rest, from the public operation's
status on, also addresses `out` and the input and counts `k`, which `s1`,
`s6` and `s3` hold (`tail_taint`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Rsa.RISCV64.Priv
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)

/-- The rest, from the public operation's status on. -/
abbrev tail : Prog isa :=
  .seq (.block cmpArgs) (.seq compare (.seq (.block result) (.seq release (.block restore))))

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => nomatch h

theorem setup_taint {α : Type} (Φ : α → State → Prop) :
    RelCT isa (Two Φ) (.block (save ++ crtArgs)) fun _ _ => True :=
  two_taint [] (pins_nil Φ) (by taint_decide)

theorem preArgs_taint {α : Type} (Φ : α → State → Prop) :
    RelCT isa (Two Φ) (.block preArgs) fun _ _ => True :=
  two_taint [] (pins_nil Φ) (by taint_decide)

theorem pubArgs_taint {α : Type} (Φ : α → State → Prop) :
    RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] (pins_nil Φ) (by taint_decide)

theorem tail_taint {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.s1, .s3, .s6]) :
    RelCT isa (Two Φ) tail fun _ _ => True :=
  two_taint _ hp (by taint_decide)

end VG.Proof.Rsa.RISCV64.Priv
