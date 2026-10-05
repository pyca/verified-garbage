import VerifiedGarbage.Proof.EcKey.AArch64.Main
import VerifiedGarbage.Proof.EcKey.AArch64.P384.Contract
import VerifiedGarbage.Proof.EcKey.AArch64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified

/-!
# P-384 public keys on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P384.law` and `Proof.Weierstrass.AArch64.invSounds`), so `publicKey_ok`
gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

namespace VG.Proof.EcKey.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.EcKey.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

theorem pre_of {s : State} (h : pkAArch64.pre s) : PkPre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem post_of {s s' : State} (h : PkPost p384 s s') : pkAArch64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 97 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 97 = List.replicate 97 0
  revert h
  generalize hq : pk s.mem (s.gpr .x1) = q
  rw [show Spec.EcKey.publicKey p384.C (dk p384 s) = pk s.mem (s.gpr .x1) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_a64 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (s : State)
    (hs : pkAArch64.pre s) :
    ∃ t s', Exec isa publicKeyP384 s t s' ∧ abiPreserved s s' ∧ pkAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-384's
  -- terms before the literals' facts are known.
  have hn : publicKeyP384.noCalls = true := by lit_decide
  have hu : KeepsUntouched publicKeyP384 := by lit_decide
  have hv : publicKeyP384.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (p384_ok hI) hL hT (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, post_of hpost⟩

theorem pk_ct : ConstantTime isa pkAArch64.pre pkAArch64.pub publicKeyP384 :=
  VG.Taint.constantTime (A := taintS [p384.tsym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

theorem pk_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    Verified AArch64.target publicKeyP384
      (Spec.EcKey.P384.inst.publicKeyContract (AArch64.abi.withConsts p384.combConsts)) :=
  Verified.of_correct (pk_a64 hL hI hT) pk_ct implies

end VG.Proof.EcKey.AArch64.P384
