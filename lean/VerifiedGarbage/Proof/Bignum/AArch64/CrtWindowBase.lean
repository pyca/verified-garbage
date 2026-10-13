module

public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelper
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVerified

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64

def body : Window := Window.inline Mont.base WindowVector.selector

theorem body_keeps_link : ∀ i ∈ instrs body.code, vdstOf i ≠ some .v7 := by
  have hb : body.code.allInstrs (fun i => vdstOf i != some .v7) = true := by decide +kernel
  rw [Code.allInstrs_eq,List.all_eq_true] at hb
  intro i hi
  exact bne_iff_ne.mp (hb i hi)

def called : Window := WindowCall.outlined body Spec.Rsa.MontWindow.windowApi.name body_keeps_link

def code : Prog isa := VG.Impl.Rsa.AArch64.WindowFive.code called.code WindowVector.selector.code Mont.base.mm

theorem base_verified : Verified target code (Spec.Rsa.privateCrtContract abi 0) :=
  verified called Mont.base WindowVector.selector

end VG.Proof.Bignum.AArch64.WindowFive
