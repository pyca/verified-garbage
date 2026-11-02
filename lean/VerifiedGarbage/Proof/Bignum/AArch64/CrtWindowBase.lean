module

public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedInterface
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVerified
public import VerifiedGarbage.Proof.Rsa.Contract

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64

def body : Window := WindowShared.window

theorem body_keeps_link : ∀ i ∈ instrs body.code, vdstOf i ≠ some .v7 := by
  have hb : body.code.allInstrs (fun i => vdstOf i != some .v7) = true := by decide +kernel
  rw [Code.allInstrs_eq,List.all_eq_true] at hb
  intro i hi
  exact bne_iff_ne.mp (hb i hi)

def called : Window := WindowCall.outlined body "vg_rsa_square_window5" body_keeps_link

def code : Prog isa :=
  VG.Impl.Rsa.AArch64.WindowFive.code called.code WindowVector.selector.code Mont.calledProductEight.mm

theorem base_verified : Verified target code (Proof.Rsa.privateCrtContract abi 0) :=
  verified called Mont.calledProductEight WindowVector.selector

end VG.Proof.Bignum.AArch64.WindowFive
