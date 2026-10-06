import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# Deterministic ECDSA on AArch64: `Verified`

For any hash function `P`: `sign_ok` gives the contract's postcondition and
keeps the callee-saved registers and the stack pointer; no instruction of
the function or of those it calls writes a callee-saved SIMD register
(`sign_keepsV`: the HMAC functions' and the streaming `update`'s, from what
`P` knows of them, and `core`'s, from what the curve knows of it), so their
low halves are kept too (`abiPreserved`). Constant time up to the number of
candidates: `sign_ct`. The function's own code is checked for each size of
hash function and of scalars. Each instance's file shows that its contract implies
`rfcAArch64` (`sign_verified`'s `himp`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable (P : RfcHash)

theorem cfgOf_H : (cfgOf P).H = P.H := rfl
theorem reduce_eq : (cfgOf P).reduce = (cfgC P.R.E).reduce := rfl
theorem initCnt_eq : (cfgOf P).initCnt = (cfgC ⟨4, Spec.P256.curve, [], (0, 0), "", true⟩).initCnt := rfl
theorem coreC_eq : (cfgOf P).coreC = P.R.coreC := rfl

/-- No instruction writes a callee-saved SIMD register: not those of the
functions it calls, by what `P` and the proofs of HMAC's functions know of
them, nor its own, which the kernel evaluates for each size of hash function
and of scalars. -/
theorem sign_keepsV : (cfgOf P).sign.allInstrs keepsV = true := by
  have hI : P.H.hmacInit.allInstrs keepsV = true := P.ok.hmacInit_keepsV
  have hU : P.H.updC.allInstrs keepsV = true := P.ok.updKeepsV
  have hF : P.H.hmacFin.allInstrs keepsV = true := P.ok.hmacFin_keepsV
  have hw' : (cfgOf P).w = P.R.E.n := rfl
  have hl' : (cfgOf P).len = P.R.E.C.len := rfl
  cases hw : P.R.wide
  · have hR := P.R.reduceKeepsV hw
    have e : (cfgOf P).wide = false := hw
    simp only [Cfg.sign, Cfg.body, Cfg.start, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV,
      Cfg.hmac, e, Bool.false_eq_true, ite_false, Code.allInstrs, reduce_eq, initCnt_eq, cfgOf_H, coreC_eq, hI,
      hU, hF, P.R.coreKeepsV, Bool.and_true, Bool.true_and] at hR ⊢
    have hl : P.R.E.C.len = 8 * P.R.E.n := (P.R.sizesA hw).2.1
    simp only [hR, hw', hl', hl, Bool.true_and]
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rcases (P.R.sizesA hw).1 with h'' | h'' <;>
      simp only [h, h', h''] <;> decide +kernel
  · obtain ⟨hw9, hQ66, hD64, hB⟩ := P.sizesW hw
    have e : (cfgOf P).wide = true := hw
    have hs : (cfgOf P).sh = 7 := sh7 hw
    simp only [Cfg.sign, Cfg.body, Cfg.start, Cfg.tryOne, Cfg.cand, Cfg.coreDigest, Cfg.keepV, Cfg.candTop, Cfg.conv,
      Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, e, ite_true, Code.allInstrs, initCnt_eq, cfgOf_H, coreC_eq,
      hI, hU, hF, P.R.coreKeepsV, Bool.and_true, Bool.true_and]
    have hw9' : P.R.E.n = 9 := hw9
    have hQ66' : P.R.E.C.len = 66 := hQ66
    simp only [hw', hl', hs, hw9', hQ66', hD64, hB]
    decide +kernel

theorem sign_a64 (s : State) (h : (rfcAArch64 P.R.E P.I (256 + P.e)).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcAArch64 P.R.E P.I (256 + P.e)).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hsp⟩, hp⟩ := sign_ok (P := P) h
  exact ⟨t, s', he, ⟨hg, hsp, Exec.preservedV he (sign_keepsV P)⟩, hp⟩

/-- The notes on the implementation, for the documentation of the function
with the hash function `H`, for scalars of `q` bytes signed by `core`. -/
def signNotes (H : Impl.Pbkdf2.Md.AArch64.Hash) (q : Nat) (core : String) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost " ++
  toString q ++ " bytes, and each HMAC with `" ++ H.hmacInitN ++ "`, `" ++ H.updN ++ "` and `" ++ H.hmacFinN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, \
  the leftmost " ++ toString q ++ " bytes of `V`, is tried with `" ++ core ++ "`, which uses all of `scratch`; \
  whether to try another is computed without branches from its result and the count of candidates left, so \
  the code branches only on that. `K`, `V`, `h`, the count and the pointers are kept in a 224-byte stack \
  frame, below the 16 bytes saving `x30`, and the secrets are cleared before it is freed; the calls use \
  the 16 bytes below it."

/-- The notes of an instance whose scalars are longer than the hash
(`wide`): `q` bytes of `nb` bits, from a `D`-byte hash. -/
def signNotesWide (H : Impl.Pbkdf2.Md.AArch64.Hash) (q nb D : Nat) (core : String) : String :=
  "Computes `h = bits2octets(digest)` as " ++ toString (q - D) ++ " zero bytes and the digest (whose integer \
  is below `n`), and each HMAC with `" ++ H.hmacInitN ++ "`, `" ++ H.updN ++ "` and `" ++ H.hmacFinN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, the \
  leftmost " ++ toString nb ++ " bits of two successive `V`s, is shifted into " ++ toString q ++ " bytes, as is \
  the digest for the signature (its integer shifted left by " ++ toString (8 * q - nb) ++ " bits), with word \
  loads, shifts and stores through `scratch`, and tried with `" ++ core ++ "`, which uses all of `scratch`; \
  whether to try another is computed without branches from its result and the count of candidates left, so \
  the code branches only on that. `K`, `V`, `h`, the count, the pointers, the candidate and the shifted \
  digest are kept in a 368-byte stack frame, below the 16 bytes saving `x30`, and the secrets are cleared \
  before it is freed; the calls use the 16 bytes below it."

theorem sign_verified
    (himp : (rfcAArch64 P.R.E P.I (256 + P.e)).Implies
      (P.I.signContract (AArch64.abi.withConsts P.R.E.combConsts) (256 + P.e))) :
    Verified AArch64.target (cfgOf P).sign (P.I.signContract (AArch64.abi.withConsts P.R.E.combConsts) (256 + P.e)) :=
  Verified.of_correct (sign_a64 P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.AArch64
