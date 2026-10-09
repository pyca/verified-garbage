import VerifiedGarbage.Proof.EcKey.AArch64.P192.Main
import VerifiedGarbage.Proof.EcKey.AArch64.P192.Contract
import VerifiedGarbage.Proof.EcKey.AArch64.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi

/-!
# p192 public keys on AArch64: `Verified`

p192 is a curve the proof supports (`p192_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P192.law`), so `publicKey_ok`
gives the contract's postcondition; `x19` and `x20` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

namespace VG.Proof.EcKey.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.EcKey.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192

theorem pre_of {s : State} (h : pkAArch64.pre s) : PkPre p192 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem post_of {s s' : State} (h : PkPost p192 s s') : pkAArch64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 49 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 49 = List.replicate 49 0
  revert h
  generalize hq : pk s.mem (s.gpr .x1) = q
  rw [show Spec.EcKey.publicKey p192.C (dk p192 s) = pk s.mem (s.gpr .x1) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_a64 (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) (s : State) (hs : pkAArch64.pre s) :
    ∃ t s', Exec isa publicKeyP192 s t s' ∧ abiPreserved s s' ∧ pkAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (p192_ok hI) hL (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, post_of hpost⟩

theorem pk_ct : ConstantTime isa pkAArch64.pre pkAArch64.pub publicKeyP192 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

theorem pk_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target publicKeyP192 (Spec.EcKey.P192.inst.publicKeyContract AArch64.abi) :=
  Verified.of_correct (pk_a64 hL hI) pk_ct implies

end VG.Proof.EcKey.AArch64.P192
