import VerifiedGarbage.Proof.Ecdh.AArch64.Secp256k1.Main
import VerifiedGarbage.Proof.Ecdh.AArch64.Secp256k1.Contract
import VerifiedGarbage.Proof.Ecdh.AArch64.Secp256k1.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi

/-!
# ECDH over secp256k1 on AArch64: `Verified`

secp256k1 is a curve the proof supports (`secp256k1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.Secp256k1.law`), so `exchange_ok`
gives the contract's postcondition; `x19` and `x20` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre secp256k1 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost secp256k1 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 32 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 32 = List.replicate 32 0
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange secp256k1.C (dk secp256k1 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * secp256k1.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa VG.Impl.Ecdh.AArch64.Secp256k1.exchange s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok (secp256k1_ok hI) hL (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub VG.Impl.Ecdh.AArch64.Secp256k1.exchange :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target VG.Impl.Ecdh.AArch64.Secp256k1.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.Secp256k1.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI) ecdh_ct implies

end VG.Proof.Ecdh.AArch64.Secp256k1
