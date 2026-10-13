module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitEraseAdx
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitEraseAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# ECDSA verification over P-256 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p256x` (`p256` multiplying with BMI2 and ADX): the
same curve, so the same precondition and postcondition.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64

theorem verify_x86_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP256Adx.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_x86_of (p256x_ok hI) hL (p256_tbls hL hT) rfl (fun _ h => { pre_of h with }) (fun _ _ => id) rfl
    (by lit_decide) (by lit_decide) (by lit_decide) s hs

theorem verify_checks_adx : VerifyChecks p256x p256Table where
  comb := {
    init := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
    head := VG.Taint.constantTime (A := taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
    tail := VG.Taint.constantTime_mapBlocks (c' := tailErasedAdx) taint_eraseInv
      (Taint.ofRegs [.rdi,.rbx,.rdx]) rfl (fun _ _ _ _ h => h) rfl (by taint_decide) }
  before := VG.Taint.constantTime_mapBlocks (c' := beforeErasedAdx) taint_eraseInv
    (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx]) rfl (fun _ _ _ _ h => h) rfl (by taint_decide)
  after := VG.Taint.constantTime_mapBlocks (c' := afterErasedAdx) taint_eraseInv
    (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

theorem verify_ct_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub verifyP256Adx.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact verify_public_ct (c := p256x) (p256x_ok hI).toBaseCfgOk hL (p256_tbls hL hT) rfl (by decide) verify_checks_adx rfl
    _ _ _ _ _ _ (show VPre p256x s₁ from { pre_of (implies.pre _ pre₁) with })
    (show VPre p256x s₂ from { pre_of (implies.pre _ pre₂) with }) (verify_public_of_spec pub) e₁ e₂

theorem verify_verified_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyP256Adx
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) (by lit_decide) (fun s hs => verify_x86_adx hL hT hI s (implies.pre _ hs))
    (verify_ct_adx hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

end VG.Proof.Ecdsa.Verify.X86_64
