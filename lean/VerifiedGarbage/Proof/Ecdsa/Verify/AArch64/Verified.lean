import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified

/-!
# ECDSA verification over P-256 on AArch64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, given the inversions' last step `InvToM`, and `Law` for its group
law, which the registration file supplies: `Proof.P256.law` and `Proof.Weierstrass.invToM`), so `verify_ok` gives
the contract's postcondition; `x19` and `x20` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so only the pointers affect timing (the contract would let the key, the hash
and the signature affect it too).
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem pre_of {s : State} (h : verifyAArch64.pre s) : VPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem verify_noCalls : verifyP256.noCalls = true := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP256 := by lit_decide

theorem verify_keepsV : verifyP256.allInstrs keepsV = true := by lit_decide

theorem verify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.InvToM)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State)
    (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (p256_ok hI) hL hT (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_noCalls verify_untouched verify_keepsV hsv, hpost⟩

theorem verify_ct : ConstantTime isa verifyAArch64.pre verifyAArch64.pub verifyP256 :=
  VG.Taint.constantTime (A := taintS [p256.tsym]) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.InvToM)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target verifyP256
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (verify_a64 hL hI hT) verify_ct implies

end VG.Proof.Ecdsa.Verify.AArch64
