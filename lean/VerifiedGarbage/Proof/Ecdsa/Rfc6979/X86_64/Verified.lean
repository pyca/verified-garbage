import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA over P-256 on x86-64: `Verified`

For any hash function `P`: `sign_ok` gives the contract's postcondition and
keeps the callee-saved registers and the return address; no instruction of
the function or of those it calls loads MXCSR (`sign_mx`: the HMAC
functions' and the compression function's, from what `P` knows of them, and
`core`'s, from its literal), so it is kept too (`abiPreserved`). Constant
time up to the number of candidates: `sign_ct`. The function's own code is
checked for each size of hash function. Each instance's file shows that its
contract implies `rfcX86_64` (`sign_verified`'s `himp`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (core_hmacInit core_hmacFin core_updC)

variable (P : RfcHash)

theorem cfgOf_H : (cfgOf P).H = P.H := rfl
theorem reduce_eq : (cfgOf P).reduce = cfgC.reduce := rfl
theorem initCnt_eq : (cfgOf P).initCnt = cfgC.initCnt := rfl
theorem coreC_eq : (cfgOf P).coreC = Impl.Ecdsa.X86_64.signP256 := rfl

/-- No instruction loads MXCSR: not those of the functions it calls, by what
`P` and the proofs of HMAC's functions know of them, nor its own, which the
kernel evaluates for each size of hash function. -/
theorem sign_mx : (cfgOf P).sign.allInstrs (fun i => !loadsMxcsr i) = true := by
  have hI : P.H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacInit P.K.cMx P.K.iMx P.C.hinitMx
  have hU : P.H.updC.allInstrs (fun i => !loadsMxcsr i) = true := core_updC P.K.cMx P.C.updMx
  have hF : P.H.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacFin P.K.cMx P.C.hfinMx
  have hK : Impl.Ecdsa.X86_64.signP256.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide
  simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs,
    reduce_eq, initCnt_eq, cfgOf_H, coreC_eq, hI, hU, hF, hK, Bool.and_true, Bool.true_and]
  rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> decide +kernel

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem sign_spSafe : (cfgOf P).sign.all (fun i => !isa.writesSp i) = true := by
  have hI : P.H.hmacInit.allInstrs (fun i => !isa.writesSp i) = true := core_hmacInit P.K.cSp P.K.iSp P.C.hinitSp
  have hU : P.H.updC.allInstrs (fun i => !isa.writesSp i) = true := core_updC P.K.cSp P.updSp
  have hF : P.H.hmacFin.allInstrs (fun i => !isa.writesSp i) = true := core_hmacFin P.K.cSp P.C.hfinSp
  have hK : Impl.Ecdsa.X86_64.signP256.allInstrs (fun i => !isa.writesSp i) = true := by lit_decide
  refine Code.all_of_allInstrs ?_
  simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs,
    reduce_eq, initCnt_eq, cfgOf_H, coreC_eq, hI, hU, hF, hK, Bool.and_true, Bool.true_and]
  rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> decide +kernel

theorem sign_x86 (s : State) (h : (rfcX86_64 P.I).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcX86_64 P.I).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sign_ok (P := P) h
  exact ⟨t, s', he, abiPreserved_of_exec (sign_mx P) he hg, hp⟩

/-- The notes on the implementation, for the documentation of the function
with the hash function `H`. -/
def signNotes (H : Impl.Pbkdf2.Md.X86_64.Hash) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost \
  32 bytes, and each HMAC with `" ++ H.hmacInitN ++ "`, `" ++ H.updN ++ "` and `" ++ H.hmacFinN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, \
  the leftmost 32 bytes of `V`, is tried with `vg_ecdsa_p256_sign`, which uses all of `scratch`; whether \
  to try another is computed without branches from its result and the count of candidates left, so the \
  code branches only on that. `K`, `V`, `h`, the count and the pointers are kept in a 200-byte stack \
  frame, whose secrets are cleared before it is popped; the calls use the 24 bytes below it."

theorem sign_verified (himp : (rfcX86_64 P.I).Implies (P.I.signContract X86_64.abi 224)) :
    Verified X86_64.target (cfgOf P).sign (P.I.signContract X86_64.abi 224) :=
  Verified.of_correct (sign_x86 P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.X86_64
