module

public import VerifiedGarbage.Proof.Ecdh.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdh.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdh.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
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
# ECDH over P-256 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p256x` (`p256` multiplying with BMI2 and ADX): the
same curve, so the same precondition and postcondition.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64

theorem mulQJP256x_ok (hI : Weierstrass.X86_64.InvSounds) (hL : Weierstrass.Law Spec.P256.curve)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) :
    MulOk p256x (Impl.Ecdh.X86_64.Cfg.mulQJ p256x (Impl.P256.X86_64.doubleHalfPublic p256x.MP' p256x.rcbSlots))
      (mulQJW p256x) :=
  mulQJ_ok (p256x_ok hI) (Or.inl rfl) hL hO (Proof.P256.X86_64.doubleHalfPublic_dblOk rfl
    (Weierstrass.unitMod_pow_two (p256x_ok hI).p_odd _) hL (p256x_ok hI).am3) (Nat.le_of_eq Proof.P256.X86_64.n_mod32.symm)
    Proof.P256.X86_64.n_ge64

theorem ecdh_inlineOk_adx : exchangeP256Adx.InlineOk = true := by lit_decide

theorem ecdh_x86_adx (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP256Adx.inline s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' :=
  ecdh_x86_of (p256x_ok hI) hL (mulQJP256x_ok hI hL hO) (mulQJ_w (p256x_ok hI))
    (fun _ h => { pre_of h with }) (fun _ _ => post_of) rfl ecdh_inlineOk_adx (by lit_decide) s hs

/-- `exchangeP256Adx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def exchangeP256AdxErased : Prog isa := Code.erase exchangeP256Adx

materialize_shared exchangeP256AdxErased

theorem ecdh_ct_adx : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP256Adx :=
  VG.Taint.constantTime_mapBlocks (c' := exchangeP256AdxErased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h0)
    rfl (by taint_decide)

theorem ecdh_verified_adx (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) :
    Verified X86_64.target exchangeP256Adx
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi 8) :=
  Verified.of_inline_ct ecdh_inlineOk_adx (ecdh_x86_adx hL hI hO) ecdh_ct_adx implies8
    (fun _ h => Sig.clear_of_pre h) ecdh_patch

end VG.Proof.Ecdh.X86_64
