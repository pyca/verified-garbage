import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# Deterministic ECDSA over P-256 on AArch64: `Verified`

For any hash function `P`: `sign_ok` gives the contract's postcondition and
keeps the callee-saved registers and the stack pointer; no instruction of
the function or of those it calls writes a callee-saved SIMD register
(`sign_keepsV`: the HMAC functions' and the streaming `update`'s, from what
`P` knows of them, and `core`'s, from its literal), so their low halves are
kept too (`abiPreserved`). Constant time up to the number of candidates:
`sign_ct`. The function's own code is checked for each size of hash
function. Each instance's file shows that its contract implies
`rfcAArch64` (`sign_verified`'s `himp`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable (P : RfcHash)

theorem cfgOf_H : (cfgOf P).H = P.H := rfl
theorem reduce_eq : (cfgOf P).reduce = cfgC.reduce := rfl
theorem initCnt_eq : (cfgOf P).initCnt = cfgC.initCnt := rfl
theorem coreC_eq : (cfgOf P).coreC = Impl.Ecdsa.AArch64.signP256 := rfl

/-- No instruction writes a callee-saved SIMD register: not those of the
functions it calls, by what `P` and the proofs of HMAC's functions know of
them, nor its own, which the kernel evaluates for each size of hash function. -/
theorem sign_keepsV : (cfgOf P).sign.allInstrs keepsV = true := by
  have hI : P.H.hmacInit.allInstrs keepsV = true := P.ok.hmacInit_keepsV
  have hU : P.H.updC.allInstrs keepsV = true := P.ok.updKeepsV
  have hF : P.H.hmacFin.allInstrs keepsV = true := P.ok.hmacFin_keepsV
  have hK : Impl.Ecdsa.AArch64.signP256.allInstrs keepsV = true := by lit_decide
  simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs,
    reduce_eq, initCnt_eq, cfgOf_H, coreC_eq, hI, hU, hF, hK, Bool.and_true, Bool.true_and]
  rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> decide +kernel

theorem sign_a64 (s : State) (h : (rfcAArch64 P.I).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcAArch64 P.I).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hsp⟩, hp⟩ := sign_ok (P := P) h
  exact ⟨t, s', he, ⟨hg, hsp, Exec.preservedV he (sign_keepsV P)⟩, hp⟩

/-- The notes on the implementation, for the documentation of the function
with the hash function `H`. -/
def signNotes (H : Impl.Pbkdf2.Md.AArch64.Hash) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost \
  32 bytes, and each HMAC with `" ++ H.hmacInitN ++ "`, `" ++ H.updN ++ "` and `" ++ H.hmacFinN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, \
  the leftmost 32 bytes of `V`, is tried with `vg_ecdsa_p256_sign`, which uses all of `scratch`; whether \
  to try another is computed without branches from its result and the count of candidates left, so the \
  code branches only on that. `K`, `V`, `h`, the count and the pointers are kept in a 208-byte stack \
  frame, below the 16 bytes saving `x30`, and the secrets are cleared before it is freed; the calls use \
  the 16 bytes below it."

theorem sign_verified (himp : (rfcAArch64 P.I).Implies (P.I.signContract AArch64.abi 240)) :
    Verified AArch64.target (cfgOf P).sign (P.I.signContract AArch64.abi 240) :=
  Verified.of_correct (sign_a64 P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.AArch64
