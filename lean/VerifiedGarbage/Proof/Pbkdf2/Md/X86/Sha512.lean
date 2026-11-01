module

import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFinCT
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.IterateCT
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFinCT
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.IterateCT
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit

/-!
# HMAC-SHA-512's `init` and `finalize` and PBKDF2-HMAC-SHA-512's `iterate` on x86 (32-bit)

The generic proofs at SHA-512 (see `Instances.lean`): the taint checks of
their blocks, and their contracts moved to the shared ones (`sig_implies`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

theorem sha512_iterChecks : Iterate.Checks sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_finChecks : HmacFin.Checks sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_iterImp : (iterW Spec.Hmac.sha512S 234).Implies (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 64 234
  sig_implies [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 64 234

theorem sha512_finImp : (finW Spec.Hmac.sha512S 234).Implies (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 64 234
  sig_implies [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 64 234

theorem sha512_iterate : Verified X86.target sha512M'.iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512I X86.abi 48) :=
  (Iterate.verifiedW sha512Ok' sha512_iterChecks (by decide) sha512_iterImp.sat_left).of_implies sha512_iterImp

theorem sha512_finalize : Verified X86.target sha512M'.hmacFin (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512I X86.abi 48) :=
  (HmacFin.verifiedW sha512Ok' sha512_finChecks (by decide) sha512_finImp.sat_left).of_implies sha512_finImp

theorem sha512_initChecks : HmacInit.Checks sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_initImp : (initW Spec.Hmac.sha512S 234).Implies (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha512_init : Verified X86.target sha512M'.hmacInit (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512I X86.abi 48) :=
  (HmacInit.verifiedW sha512Ok' sha512_initChecks (by decide) sha512_initImp.sat_left).of_implies sha512_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
