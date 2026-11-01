module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Contract
import VerifiedGarbage.Proof.Framework.LitShare
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.P256.Prime
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Contract
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over P-256 on x86-64 with BMI2 and ADX: `Verified`

`p256x` is `p256` multiplying with BMI2 and ADX (`Mod.adx`), which the proof
of `sign_ok` covers as it covers any multiplication (`Proof/Mont/X86_64/Adx.lean`):
the same curve, so the same facts (`p256x_ok`, from `p256_ok` but for the
inversions' constants, decided again) and the same precondition.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p256x_ok (hI : InvSounds) : CfgOk p256x :=
  have h := p256_ok hI
  { h with
    comb := fun d h => by cases h; exact ⟨by decide, by decide, by decide⟩
    inv := fun _ => ⟨by decide, @hI _ p256.C.p_ne_zero Proof.P256.p_prime,
      InvOk.ofMod (by decide +kernel) (by decide)⟩
    inv_n := fun _ _ => ⟨@hI _ p256.C.n_ne_zero Proof.P256.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩ }

/-- `[k]G` is a call of `vg_p256_mul_base_adx`, which calls no other function. -/
theorem p256x_mulBase : MulBaseOk p256x :=
  ⟨fun _ => ⟨_, rfl, by decide, by lit_decide⟩, fun h => absurd h (by decide)⟩

theorem sign_x86_adx (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP256Adx.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  sign_x86_of (p256x_ok hI) hL (p256_tbls hL hT) p256x_mulBase (fun _ h => { pre_of h with }) (fun _ _ => id) rfl
    (by lit_decide) (by lit_decide) (by lit_decide) s hs

/-- `signP256Adx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signP256AdxErased : Prog isa := Code.erase signP256Adx

materialize_shared signP256AdxErased

theorem sign_ct_adx : ConstantTime isa signX86_64.pre signX86_64.pub signP256Adx :=
  VG.Taint.constantTime_mapBlocks (c' := signP256AdxErased) (taintSym_eraseInv ["VG_P256_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86_adx (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds) (s : State) (hs : signX86_64.pre s) (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signP256Adx s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) (by lit_decide) (sign_x86_adx hL hT hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

theorem sign_verified_adx (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP256Adx
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline_ct (by lit_decide) (sign_x86_adx hL hT hI) sign_ct_adx implies8
    (fun _ h => Sig.clear_of_pre_consts h) sign_patch

end VG.Proof.Ecdsa.X86_64
