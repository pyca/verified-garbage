module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.JointIfma
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.TCB.X86_64.Target

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointErased
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.P256.X86_64.JointInitLayout
import VerifiedGarbage.Proof.P256.X86_64.JointPrep
import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Spec.Ecdsa.P256
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.JointIfma
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointAbi
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointErased
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.P256.X86_64.JointInitLayout
meta import VerifiedGarbage.Proof.P256.X86_64.JointPrep
meta import VerifiedGarbage.Proof.P256.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.GContract
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.GContract
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointIfma
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointIfmaLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks
import VerifiedGarbage.Proof.Weierstrass.X86_64.MxcsrInline
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointIfma
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointIfmaLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MxcsrInline

/-!
# ECDSA verification over P-256 on x86-64 with AVX512_IFMA: `Verified`

`jointVerifyP256Ifma`, the joint verifier with the loop over the digits in
vectors, meets the contract of `vg_ecdsa_p256_verify`, as the other joint
verifiers do (`JointVerified.lean`): correct (`jointVerify_p256_ifma_ok`) and
constant time between runs from the same public inputs
(`jointVerify_p256_ifma_public_ct`), with its calls inlined; MXCSR's control
bits kept, as the loop loads MXCSR only between saving it in `r12` and loading
it back (`ctlOk`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Impl.P256.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P256.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

/-- `jointVerifyP256Ifma` without its displacements, as a literal of shared blocks. -/
def jointVerifyP256IfmaErased : Prog isa := Code.erase jointVerifyP256Ifma

materialize_shared jointVerifyP256IfmaErased

theorem jointVerifyP256Ifma_inlineOk : jointVerifyP256Ifma.InlineOk = true :=
  Code.inlineOk_of_erase (show jointVerifyP256IfmaErased.InlineOk = true by lit_decide)

theorem jointVerifyP256Ifma_rsp :
    jointVerifyP256Ifma.allInstrs (fun i => !Taint.clobbers i .rsp) = true :=
  Code.allInstrs_of_erase (fun i => by rw [Instr.clobbers_erase])
    (show jointVerifyP256IfmaErased.allInstrs _ = true by lit_decide)

theorem jointVerifyP256Ifma_ctl : ctlOk jointVerifyP256Ifma = true := by lit_decide

section
variable (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (hI : InvSounds) (hO : PrimeOrder Spec.P256.curve)
include hL hT hI hO

theorem jointVerify_x86_ifma (s : State) (hs : verifyGX86_64.pre s) :
    ∃ t s', Exec isa jointVerifyP256Ifma.inline s t s' ∧ abiPreserved s s' ∧ verifyGX86_64.post s s' :=
  verify_abi_of_wp_ctl hs (jointVerify_p256_ifma_ok hL hT hI hO (preG_of_x hs))
    (by rw [Code.allInstrs_inline]; exact jointVerifyP256Ifma_rsp) (ctlOk_inline jointVerifyP256Ifma_ctl)
    (Code.noCalls_inline jointVerifyP256Ifma_inlineOk)

theorem jointVerify_ifma_ct :
    ConstantTime isa
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)).pre
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)).pub
      jointVerifyP256Ifma.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p256_ifma_public_ct hL hT hI hO _ _ _ _ _ _
    (show VPre p256vx s₁ from { preG_of (impliesG.pre _ pre₁) with })
    (show VPre p256vx s₂ from { preG_of (impliesG.pre _ pre₂) with })
    (show JointPublic p256vx p256GTab s₁ s₂ from { jointPublic_of_spec pub with }) e₁ e₂

theorem jointVerify_verified_ifma : Verified X86_64.target jointVerifyP256Ifma
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyGK₀) jointVerifyP256Ifma_inlineOk
    (fun s hs => jointVerify_x86_ifma hL hT hI hO s (impliesG.pre _ hs))
    (jointVerify_ifma_ct hL hT hI hO) impliesG8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (impliesG.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

/-- `vg_ecdsa_p256_verify_ifma`, taking the hash function's output: `jointVerify_verified_ifma`,
run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified_ifma : Verified X86_64.target
    (Impl.Ecdsa.X86_64.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false jointVerifyP256Ifma)
    (Spec.Ecdsa.P256.inst.verifyHashContract (X86_64.abi.withConsts p256v.combConsts) 96) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.p256_len (by decide) (jointVerify_verified_ifma hL hT hI hO)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by taint_decide)
    (Hash.hashSat_cons (by decide) satG_spec8 (by decide) fun r hr => by
      simp only [satStateG, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end

/-- The verifier's postcondition reads the memory on return only within its buffers, whatever tables of
constants its code takes (`Scrub.withScrubAll`). -/
theorem verifyHashOut_consts (J : Spec.Ecdsa.Instance) (cs : List (String × List (BitVec 64))) (stack : Nat) :
    X86_64.Scrub.PostOut (J.verifyHashContract (X86_64.abi.withConsts cs) stack) (J.verifyHashSig.retBits 64) :=
  X86_64.Scrub.postOut_of_local (X86_64.Scrub.ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

end VG.Proof.Ecdsa.Verify.X86_64
