import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdh.AArch64.P224.Contract
import VerifiedGarbage.Proof.Ecdh.AArch64.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified

/-!
# ECDH over P-224 on AArch64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P224.law` and `invSound_of_toM`), so `exchange_ok`
gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.AArch64.P224

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P224

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p224 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p224 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 28 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 28 = List.replicate 28 0
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p224.C (dk p224 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p224.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa exchangeP224 s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-224's
  -- terms before the literals' facts are known.
  have hn : CallsKeep exchangeP224 := by lit_decide
  have hu : KeepsUntouched exchangeP224 := by lit_decide
  have hv : exchangeP224.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok (p224_ok hI) hL (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub exchangeP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target exchangeP224
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI) ecdh_ct implies

end VG.Proof.Ecdh.AArch64.P224
