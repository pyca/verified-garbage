module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Contract
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
import VerifiedGarbage.Proof.P384.EcdhDouble.Verified
import VerifiedGarbage.Proof.P384.EcdhMadd
import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Contract
meta import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
meta import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
meta import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
meta import VerifiedGarbage.Impl.Ecdh.P384.AArch64
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
meta import VerifiedGarbage.Proof.P384.EcdhDouble.Verified
meta import VerifiedGarbage.Proof.P384.EcdhMadd

/-!
# ECDH over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P384.law` and `invSound_of_toM`), and of prime order
(`Proof.P384.primeOrder`), so the windows with a Jacobian accumulator compute `[d]P` (`mulJ4_ok`) and
`exchangeWith_ok'` gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p384 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p384 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 48 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 48 = List.replicate 48 0
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p384.C (dk p384 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p384.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa exchangeP384 s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-384's
  -- terms before the literals' facts are known.
  have hn : CallsKeep exchangeP384 := by lit_decide
  have hu : KeepsUntouched exchangeP384 := by lit_decide
  have hv : exchangeP384.allInstrs keepsV = true := by lit_decide
  have hmc : CallsKeep (Impl.Ecdh.AArch64.Cfg.middle p384) := by lit_decide
  have hmu : KeepsUntouched (Impl.Ecdh.AArch64.Cfg.middle p384) := by lit_decide
  have hm : Ecdh.AArch64.MulOk p384 (Cfg.mulJ4 p384
      (some (.block Impl.P384.EcdhAllocatedCode.doubleRD, .block Impl.P384.EcdhAllocatedCode.doubleDR))
      (some (.block Impl.P384.EcdhMadd.madd))) :=
    Ecdh.AArch64.mulJ4_ok (p384_ok hI) hL hO rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (P384.EcdhDouble.dblsOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI)) (Ecdh.AArch64.winAQ (p384_ok hI))
        (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
      (P384.EcdhMadd.maddOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI))
        (Ecdh.AArch64.winAQ (p384_ok hI)) (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
  obtain ⟨t, s', he, hsv, -, hpost⟩ :=
    Ecdh.AArch64.exchangeWith_ok' (p384_ok hI) hL hm (by decide +kernel) hmc hmu (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub exchangeP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    Verified AArch64.target exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI hO) ecdh_ct implies

end VG.Proof.Ecdh.AArch64.P384
