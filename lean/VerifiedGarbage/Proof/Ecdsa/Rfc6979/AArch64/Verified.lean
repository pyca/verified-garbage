module
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
import Mathlib.Logic.Function.Basic

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

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable (P : RfcHash)

theorem cfgOf_H : (cfgOf P).H = P.H := rfl
theorem reduce_eq : (cfgOf P).reduce = (cfgC P.R.E P.R.hHigh).reduce := rfl
theorem cfgOf_hHigh : (cfgOf P).hHigh = P.R.hHigh := rfl
/-- The count's initial store writes no callee-saved SIMD register, whatever the count. -/
theorem initCnt_keepsV :
    List.rec (motive := fun _ => Bool) true (fun i _ ih => keepsV i && ih) (cfgOf P).initCnt = true := rfl
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
      Cfg.hmac, e, Bool.false_eq_true, ite_false, initCnt_keepsV, Code.allInstrs, reduce_eq, cfgOf_H, coreC_eq, hI,
      hU, hF, P.R.coreKeepsV, Bool.and_true, Bool.true_and, cfgOf_hHigh, fHo_q P hw, hHigh_q P hw] at hR ⊢
    have hQD : P.R.E.C.len ≤ P.H.D := (P.sizesA hw).2.2
    simp only [hR, hw', hl', Bool.true_and]
    rcases (P.R.sizesA hw).1 with hn | hn | hn <;> rcases (P.R.sizesA hw).2.1 with hl | ⟨hn', hl | hl⟩ <;>
      rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      first
      | (exfalso; omega)
      | (simp only [h, h', hn, hl, Nat.reduceMul, Nat.reduceEqDiff, decide_true, decide_false, ite_true,
          ite_false]; decide +kernel)
  · obtain ⟨hw9, hQ66, hD64, hB⟩ := P.sizesW hw
    have e : (cfgOf P).wide = true := hw
    have hs : (cfgOf P).sh = 7 := sh7 hw
    simp only [Cfg.sign, Cfg.body, Cfg.start, Cfg.tryOne, Cfg.cand, Cfg.coreDigest, Cfg.keepV, Cfg.candTop, Cfg.conv,
      Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, e, ite_true, initCnt_keepsV, Code.allInstrs, cfgOf_H, coreC_eq,
      hI, hU, hF, P.R.coreKeepsV, Bool.and_true, Bool.true_and, cfgOf_hHigh, fHo_wide P hw, hHigh_wide P hw]
    have hw9' : P.R.E.n = 9 := hw9
    have hQ66' : P.R.E.C.len = 66 := hQ66
    simp only [hw', hl', hs, hw9', hQ66', hD64, hB]
    decide +kernel

theorem sign_a64 (s : State) (h : (rfcAArch64 P.R.E P.I (256 + P.e)).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcAArch64 P.R.E P.I (256 + P.e)).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hsp⟩, hp⟩ := sign_ok (P := P) h
  exact ⟨t, s', he, ⟨hg, hsp, Exec.preservedV he (sign_keepsV P)⟩, hp⟩

theorem sign_verified
    (himp : (rfcAArch64 P.R.E P.I (256 + P.e)).Implies
      (P.I.signContract (AArch64.abi.withConsts P.R.E.combConsts) (256 + P.e))) :
    Verified AArch64.target (cfgOf P).sign (P.I.signContract (AArch64.abi.withConsts P.R.E.combConsts) (256 + P.e)) :=
  Verified.of_correct (sign_a64 P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.AArch64
