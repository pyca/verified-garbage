module

import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.LitAdx
public import VerifiedGarbage.Impl.EcKey.P256.X86_64
public import VerifiedGarbage.Proof.EcKey.X86_64.Contract
import VerifiedGarbage.Proof.Framework.LitShare
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.EcKey.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.EcKey.X86_64.LitAdx
meta import VerifiedGarbage.Proof.EcKey.X86_64.Verified
meta import VerifiedGarbage.Impl.EcKey.P256.X86_64
meta import VerifiedGarbage.Proof.EcKey.X86_64.Contract
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.EcKey.X86_64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.EcKey.X86_64.Verified

/-!
# P-256 public keys on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p256x` (`p256` multiplying with BMI2 and ADX): the
same curve, so the same precondition and postcondition.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64

/-- `publicKeyP256Adx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`), and its checks of every
instruction (`Proof/Weierstrass/X86_64/CodeErase.lean`). -/
def publicKeyP256AdxErased : Prog isa := Code.erase publicKeyP256Adx

materialize_shared publicKeyP256AdxErased

theorem pk_inlineOk_adx : publicKeyP256Adx.InlineOk = true := by
  rw [← Code.InlineOk_erase]
  show publicKeyP256AdxErased.InlineOk = true
  lit_decide

theorem pk_x86_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP256Adx.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' :=
  pk_x86_of (p256x_ok hI) hL (p256_tbls hL hT) p256x_mulBase (fun _ h => { pre_of h with }) (fun _ _ => post_of rfl) rfl
    (by
      rw [← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [Taint.clobbers_erase]]
      show publicKeyP256AdxErased.allInstrs _ = true
      lit_decide) pk_inlineOk_adx (by
      rw [← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
      show publicKeyP256AdxErased.allInstrs _ = true
      lit_decide) s hs


theorem pk_ct_adx : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP256Adx :=
  VG.Taint.constantTime_mapBlocks (c' := publicKeyP256AdxErased) (taintSym_eraseInv ["VG_P256_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

theorem pk_verified_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP256Adx
      (Spec.EcKey.P256.inst.publicKeyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline_ct pk_inlineOk_adx (pk_x86_adx hL hT hI) pk_ct_adx implies8
    (fun _ h => Sig.clear_of_pre_consts h) pk_patch

end VG.Proof.EcKey.X86_64
