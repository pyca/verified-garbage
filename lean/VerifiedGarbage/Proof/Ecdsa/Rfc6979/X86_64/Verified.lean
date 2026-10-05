import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA on x86-64: `Verified`

For any hash function `P`: `sign_ok` gives the contract's postcondition and
keeps the callee-saved registers and the return address; no instruction of
the function or of those it calls loads MXCSR (`sign_mx`: the HMAC
functions' and the compression function's, from what `P` knows of them, and
`core`'s, from what the curve knows of it), so it is kept too (`abiPreserved`). Constant
time up to the number of candidates: `sign_ct`. The function's own code is
checked for each size of hash function and of scalars. Each instance's file shows that its
contract implies `rfcX86_64` (`sign_verified`'s `himp`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (core_hmacInit core_hmacFin core_updC)

variable (P : RfcHash)

theorem cfgOf_H : (cfgOf P).H = P.H := rfl
theorem cfgOf_len : (cfgOf P).len = P.Q := rfl
theorem cfgOf_w : (cfgOf P).w = P.w := rfl
theorem cfgOf_sh : (cfgOf P).sh = P.R.sh := rfl
theorem cfgOf_wide : (cfgOf P).wide = P.R.wide := rfl
theorem reduce_eq : (cfgOf P).reduce = (cfgC P.R.E).reduce := rfl
theorem initCnt_eq : (cfgOf P).initCnt = (cfgC ⟨4, Spec.P256.curve⟩).initCnt := rfl
theorem coreC_eq : (cfgOf P).coreC = P.R.coreC := rfl

/-- No instruction loads MXCSR: not those of the functions it calls, by what
`P` and the proofs of HMAC's functions know of them, nor its own, which the
kernel evaluates for each size of hash function and of scalars. -/
theorem sign_mx : (cfgOf P).sign.allInstrs (fun i => !loadsMxcsr i) = true := by
  have hI : P.H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacInit P.K.cMx P.K.iMx P.C.hinitMx
  have hU : P.H.updC.allInstrs (fun i => !loadsMxcsr i) = true := core_updC P.K.cMx P.C.updMx
  have hF : P.H.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacFin P.K.cMx P.C.hfinMx
  cases hw : P.R.wide
  · have hR := P.R.reduceMx hw
    obtain ⟨hQ8, -, hQD⟩ := P.sizesA hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac,
      Cfg.coreArgs, Cfg.wipe, Cfg.extra, Cfg.digestPtr, Cfg.keepV, Cfg.candTop, Cfg.coreDigest, Cfg.conv,
      Code.allInstrs, cfgOf_wide, cfgOf_len, cfgOf_w, cfgOf_sh, reduce_eq, initCnt_eq, cfgOf_H, coreC_eq,
      Bool.false_eq_true, ite_false, Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreMx, hQ8] at hR ⊢
    simp only [hR, Bool.true_and]
    rcases (P.R.sizesA hw).1 with hn | hn <;> rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      simp only [RfcHash.w, h, h', hn] <;> decide +kernel
  · obtain ⟨hw9, hQ66, hD64, hB⟩ := P.sizesW hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac,
      Cfg.coreArgs, Cfg.wipe, Cfg.extra, Cfg.digestPtr, Cfg.keepV, Cfg.candTop, Cfg.coreDigest, Cfg.conv,
      Code.allInstrs, cfgOf_wide, cfgOf_len, cfgOf_w, cfgOf_sh, reduce_eq, initCnt_eq, cfgOf_H, coreC_eq,
      ite_true, Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreMx, hQ66, hw9, sh7 hw]
    simp only [hD64, hB]
    decide +kernel

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem sign_spSafe : (cfgOf P).sign.all (fun i => !isa.writesSp i) = true := by
  have hI : P.H.hmacInit.allInstrs (fun i => !isa.writesSp i) = true := core_hmacInit P.K.cSp P.K.iSp P.C.hinitSp
  have hU : P.H.updC.allInstrs (fun i => !isa.writesSp i) = true := core_updC P.K.cSp P.updSp
  have hF : P.H.hmacFin.allInstrs (fun i => !isa.writesSp i) = true := core_hmacFin P.K.cSp P.C.hfinSp
  refine Code.all_of_allInstrs ?_
  cases hw : P.R.wide
  · have hR := P.R.reduceSp hw
    obtain ⟨hQ8, -, hQD⟩ := P.sizesA hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac,
      Cfg.coreArgs, Cfg.wipe, Cfg.extra, Cfg.digestPtr, Cfg.keepV, Cfg.candTop, Cfg.coreDigest, Cfg.conv,
      Code.allInstrs, cfgOf_wide, cfgOf_len, cfgOf_w, cfgOf_sh, reduce_eq, initCnt_eq, cfgOf_H, coreC_eq,
      Bool.false_eq_true, ite_false, Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreSp, hQ8] at hR ⊢
    simp only [hR, Bool.true_and]
    rcases (P.R.sizesA hw).1 with hn | hn <;> rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      simp only [RfcHash.w, h, h', hn] <;> decide +kernel
  · obtain ⟨hw9, hQ66, hD64, hB⟩ := P.sizesW hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac,
      Cfg.coreArgs, Cfg.wipe, Cfg.extra, Cfg.digestPtr, Cfg.keepV, Cfg.candTop, Cfg.coreDigest, Cfg.conv,
      Code.allInstrs, cfgOf_wide, cfgOf_len, cfgOf_w, cfgOf_sh, reduce_eq, initCnt_eq, cfgOf_H, coreC_eq,
      ite_true, Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreSp, hQ66, hw9, sh7 hw]
    simp only [hD64, hB]
    decide +kernel

theorem sign_x86 (s : State) (h : (rfcX86_64 P.I (240 + 8 * P.e)).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcX86_64 P.I (240 + 8 * P.e)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sign_ok (P := P) h
  exact ⟨t, s', he, abiPreserved_of_exec (sign_mx P) he hg, hp⟩

/-- The notes on the implementation, for the documentation of the function
with the hash function `H`, for scalars of `q` bytes signed by `core`. -/
def signNotes (H : Impl.Pbkdf2.Md.X86_64.Hash) (q : Nat) (core : String) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost " ++
  toString q ++ " bytes, and each HMAC with `" ++ H.hmacInitN ++ "`, `" ++ H.updN ++ "` and `" ++ H.hmacFinN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, \
  the leftmost " ++ toString q ++ " bytes of `V`, is tried with `" ++ core ++ "`, which uses all of `scratch`; \
  whether to try another is computed without branches from its result and the count of candidates left, so \
  the code branches only on that. `K`, `V`, `h`, the count and the pointers are kept in a 216-byte stack \
  frame, whose secrets are cleared before it is popped; the calls use the 24 bytes below it."

theorem sign_verified (himp : (rfcX86_64 P.I (240 + 8 * P.e)).Implies (P.I.signContract X86_64.abi (240 + 8 * P.e))) :
    Verified X86_64.target (cfgOf P).sign (P.I.signContract X86_64.abi (240 + 8 * P.e)) :=
  Verified.of_correct (sign_x86 P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.X86_64
