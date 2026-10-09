import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances

/-!
# HMAC-SHA-384's `init` and `finalize` and PBKDF2-HMAC-SHA-384's `iterate` on x86 (32-bit)

The generic proofs at SHA-384 (see `Instances.lean`): the taint checks of
their blocks, and their contracts moved to the shared ones (`sig_implies`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

theorem sha384_iterChecks : Iterate.Checks sha384M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha384_finChecks : HmacFin.Checks sha384M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha384_iterImp : (iterW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 48 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 48 234

theorem sha384_finImp : (finW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 48 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 48 234

theorem sha384_iterate : Verified X86.target sha384M.iterate (Spec.Hmac.sha384I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha384Ok sha384_iterChecks (by decide) sha384_iterImp.sat_left).of_implies sha384_iterImp

theorem sha384_finalize : Verified X86.target sha384M.hmacFin (Spec.Hmac.sha384I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW sha384Ok sha384_finChecks (by decide) sha384_finImp.sat_left).of_implies sha384_finImp

theorem sha384_initChecks : HmacInit.Checks sha384M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha384_initImp : (initW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha384_init : Verified X86.target sha384M.hmacInit (Spec.Hmac.sha384I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW sha384Ok sha384_initChecks (by decide) sha384_initImp.sat_left).of_implies sha384_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
