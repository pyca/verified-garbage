module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# `vg_rsa_private_checked` on PPC64LE: the blocks' taint

The blocks between the calls address only the frame, through `r12 = r1`
(`setup_taint`, `preArgs_taint`, `pubArgs_taint`); the rest, from the
public operation's status on, also addresses `out` and the input and counts
`k`, which `r24`, `r29` and `r26` hold (`tail_taint`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Two Pins two_taint)

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

theorem tail_taint {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.r24, .r26, .r29]) :
    RelCT isa (Two Φ) tail fun _ _ => True :=
  two_taint _ hp (by taint_decide)

end VG.Proof.Rsa.PPC64LE.Priv
