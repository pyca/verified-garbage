module
public import Mathlib.Tactic.Tauto
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT

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

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (core_hmacInit core_hmacFin core_updC)

variable (P : RfcHash)

theorem cfgOf_H : (cfgOf P).H = P.H := rfl
theorem cfgOf_len : (cfgOf P).len = P.Q := rfl
theorem cfgOf_w : (cfgOf P).w = P.w := rfl
theorem cfgOf_sh : (cfgOf P).sh = P.R.sh := rfl
theorem cfgOf_wide : (cfgOf P).wide = P.R.wide := rfl
theorem reduce_eq : (cfgOf P).reduce = (cfgC P.R.E P.R.hHigh).reduce := rfl
theorem cfgOf_hHigh : (cfgOf P).hHigh = P.R.hHigh := rfl
/-- A property of every instruction holds of the count's initial store if it
holds of its two instructions, whatever the count. -/
theorem initCnt_all (p : Instr → Bool) (h₁ : ∀ x, p (.mov32 .rax (.imm x)) = true)
    (h₂ : p (.store (stk fCnt) .rax) = true) :
    List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) (cfgOf P).initCnt = true := by
  show (p _ && (p _ && true)) = true
  rw [h₁, h₂]; rfl

theorem coreC_eq : (cfgOf P).coreC = P.R.coreC := rfl

/-- No instruction loads MXCSR: not those of the functions it calls, by what
`P` and the proofs of HMAC's functions know of them, nor its own, which the
kernel evaluates for each size of hash function and of scalars. -/
theorem sign_mx : (cfgOf P).sign.allInstrs (fun i => !loadsMxcsr i) = true := by
  have hI : P.H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacInit P.K.cMx P.K.iMx P.C.hinitMx
  have hU : P.H.updC.allInstrs (fun i => !loadsMxcsr i) = true := core_updC P.K.cMx P.C.updMx
  have hF : P.H.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacFin P.K.cMx P.C.hfinMx
  have hC := initCnt_all P (fun i => !loadsMxcsr i) (fun _ => rfl) rfl
  cases hw : P.R.wide
  · have hR := P.R.reduceMx hw
    obtain ⟨-, -, hQD⟩ := P.sizesA hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmac, Cfg.hmacVS,
      Cfg.hmacVR, Cfg.hmacS, Cfg.hmacR, Nat.reduceEqDiff, ↓reduceIte, Cfg.coreArgs, Cfg.wipe, Cfg.extra,
      Cfg.digestPtr,
      hC, Code.allInstrs, cfgOf_wide, cfgOf_len, reduce_eq, cfgOf_H, coreC_eq,
      cfgOf_hHigh, fHo_q P hw, hHigh_q P hw,
      Bool.false_eq_true, Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreMx] at hR ⊢
    simp only [hR, Bool.true_and]
    rcases P.sizesQ hw with hq | hq | hq | hq | hq <;> rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      first
      | (exfalso; rw [hq, h] at hQD; omega)
      | (simp only [hq, h, h', Nat.reduceEqDiff, decide_true, decide_false, ite_true, ite_false,
          Bool.false_eq_true]; decide +kernel)
  · obtain ⟨hw9, hQ66, hD64, hB⟩ := P.sizesW hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmac, Cfg.hmacVS,
      Cfg.hmacVR, Cfg.hmacS, Cfg.hmacR, Nat.reduceEqDiff, ↓reduceIte, Cfg.coreArgs, Cfg.wipe, Cfg.extra,
      Cfg.digestPtr, Cfg.keepV, Cfg.candTop, Cfg.coreDigest, Cfg.conv,
      hC, Code.allInstrs, cfgOf_wide, cfgOf_len, cfgOf_w, cfgOf_sh, cfgOf_H, coreC_eq,
      Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreMx, hQ66, hw9, sh7 hw, fHo_wide P hw]
    simp only [hD64, hB]
    decide +kernel

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem sign_spSafe : (cfgOf P).sign.all (fun i => !isa.writesSp i) = true := by
  have hI : P.H.hmacInit.allInstrs (fun i => !isa.writesSp i) = true := core_hmacInit P.K.cSp P.K.iSp P.C.hinitSp
  have hU : P.H.updC.allInstrs (fun i => !isa.writesSp i) = true := core_updC P.K.cSp P.updSp
  have hF : P.H.hmacFin.allInstrs (fun i => !isa.writesSp i) = true := core_hmacFin P.K.cSp P.C.hfinSp
  have hC := initCnt_all P (fun i => !isa.writesSp i) (fun _ => rfl) rfl
  dsimp only at hC
  refine Code.all_of_allInstrs ?_
  cases hw : P.R.wide
  · have hR := P.R.reduceSp hw
    obtain ⟨-, -, hQD⟩ := P.sizesA hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmac, Cfg.hmacVS,
      Cfg.hmacVR, Cfg.hmacS, Cfg.hmacR, Nat.reduceEqDiff, ↓reduceIte, Cfg.coreArgs, Cfg.wipe, Cfg.extra,
      Cfg.digestPtr,
      hC, Code.allInstrs, cfgOf_wide, cfgOf_len, reduce_eq, cfgOf_H, coreC_eq,
      cfgOf_hHigh, fHo_q P hw, hHigh_q P hw,
      Bool.false_eq_true, Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreSp] at hR ⊢
    simp only [hR, Bool.true_and]
    rcases P.sizesQ hw with hq | hq | hq | hq | hq <;> rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      first
      | (exfalso; rw [hq, h] at hQD; omega)
      | (simp only [hq, h, h', Nat.reduceEqDiff, decide_true, decide_false, ite_true, ite_false,
          Bool.false_eq_true]; decide +kernel)
  · obtain ⟨hw9, hQ66, hD64, hB⟩ := P.sizesW hw
    simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmac, Cfg.hmacVS,
      Cfg.hmacVR, Cfg.hmacS, Cfg.hmacR, Nat.reduceEqDiff, ↓reduceIte, Cfg.coreArgs, Cfg.wipe, Cfg.extra,
      Cfg.digestPtr, Cfg.keepV, Cfg.candTop, Cfg.coreDigest, Cfg.conv,
      hC, Code.allInstrs, cfgOf_wide, cfgOf_len, cfgOf_w, cfgOf_sh, cfgOf_H, coreC_eq,
      Bool.and_true, Bool.true_and, hw, hI, hU, hF, P.R.coreSp, hQ66, hw9, sh7 hw, fHo_wide P hw]
    simp only [hD64, hB]
    decide +kernel

theorem sign_x86 (s : State) (h : (rfcX86_64 P.R.E.combConsts P.I (240 + 8 * P.e)).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧
      (rfcX86_64 P.R.E.combConsts P.I (240 + 8 * P.e)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sign_ok (P := P) h
  exact ⟨t, s', he, abiPreserved_of_exec (sign_mx P) he hg, hp⟩

/-- The notes on the implementation, for the documentation of the function
with the hash function `H`, for scalars of `q` bytes signed by `core`, in a
stack frame of `frame` bytes. -/
def signNotes (H : Impl.Pbkdf2.Md.X86_64.Hash) (q : Nat) (core : String) (frame : Nat := 216) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost " ++
  toString q ++ " bytes, and each HMAC with `" ++ H.hmacInitN ++ "`, `" ++ H.updN ++ "` and `" ++ H.hmacFinN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, \
  the leftmost " ++ toString q ++ " bytes of `V`, is tried with `" ++ core ++ "`, which uses all of `scratch`; \
  whether to try another is computed without branches from its result and the count of candidates left, so \
  the code branches only on that. `K`, `V`, `h`, the count and the pointers are kept in a " ++
  toString frame ++ "-byte stack frame, whose secrets are cleared before it is popped; the calls use the 24 \
  bytes below it."

/-- The notes of an instance whose scalars are longer than the hash
(`wide`): `q` bytes of `nb` bits, from a `D`-byte hash. -/
def signNotesWide (H : Impl.Pbkdf2.Md.X86_64.Hash) (q nb D : Nat) (core : String) : String :=
  "Computes `h = bits2octets(digest)` as " ++ toString (q - D) ++ " zero bytes and the digest (whose integer \
  is below `n`), and each HMAC with `" ++ H.hmacInitN ++ "`, `" ++ H.updN ++ "` and `" ++ H.hmacFinN ++ "`, \
  using the start of `scratch` for HMAC's states and working space and the message. Each candidate `k`, the \
  leftmost " ++ toString nb ++ " bits of two successive `V`s, is shifted into " ++ toString q ++ " bytes, as is \
  the digest for the signature (its integer shifted left by " ++ toString (8 * q - nb) ++ " bits), with word \
  loads, shifts and stores, and tried with `" ++ core ++ "`, which uses all of `scratch`; whether to try \
  another is computed without branches from its result and the count of candidates left, so the code branches \
  only on that. `K`, `V`, `h`, the count, the pointers, the candidate and the shifted digest are kept in a \
  360-byte stack frame, whose secrets are cleared before it is popped; the calls use the 24 bytes below it."

theorem sign_verified (himp : (rfcX86_64 P.R.E.combConsts P.I (240 + 8 * P.e)).Implies
      (P.I.signContract (X86_64.abi.withConsts P.R.E.combConsts) (240 + 8 * P.e))) :
    Verified X86_64.target (cfgOf P).sign
      (P.I.signContract (X86_64.abi.withConsts P.R.E.combConsts) (240 + 8 * P.e)) :=
  Verified.of_correct (sign_x86 P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.X86_64
