import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances

/-!
# HMAC-MD5's `init` and `finalize` and PBKDF2-HMAC-MD5's `iterate` on x86 (32-bit)

The generic proofs at MD5 (see `Instances.lean`): the taint checks of
their blocks, and their contracts moved to the shared ones (`sig_implies`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

theorem md5_iterChecks : Iterate.Checks md5M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem md5_finChecks : HmacFin.Checks md5M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem md5_iterImp : (iterW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 80 16 48
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 80 16 48

theorem md5_finImp : (finW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 80 16 48
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 80 16 48

theorem md5_iterate : Verified X86.target md5M.iterate (Spec.Hmac.md5I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW md5Ok md5_iterChecks (by decide) md5_iterImp.sat_left).of_implies md5_iterImp

theorem md5_finalize : Verified X86.target md5M.hmacFin (Spec.Hmac.md5I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW md5Ok md5_finChecks (by decide) md5_finImp.sat_left).of_implies md5_finImp

theorem md5_initChecks : HmacInit.Checks md5M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem md5_initImp : (initW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 80 48
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 80 48

theorem md5_init : Verified X86.target md5M.hmacInit (Spec.Hmac.md5I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW md5Ok md5_initChecks (by decide) md5_initImp.sat_left).of_implies md5_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
