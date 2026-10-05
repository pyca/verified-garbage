import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdh.AArch64.Contract
import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified

/-!
# ECDH over P-256 on AArch64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, given the inversions' last step `InvToM`, and `Law` for its group
law, which the registration file supplies: `Proof.P256.law` and `Proof.Weierstrass.invToM`), so `exchange_ok`
gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p256 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p256 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 32 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 32 = List.replicate 32 0
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p256.C (dk p256 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p256.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.InvToM) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa exchangeP256 s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok (p256_ok hI) hL (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub exchangeP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.InvToM) :
    Verified AArch64.target exchangeP256
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI) ecdh_ct implies

end VG.Proof.Ecdh.AArch64
