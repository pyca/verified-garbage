import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi

/-! # p192 signing on AArch64: correctness and constant time -/

namespace VG.Proof.Ecdsa.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64

theorem setup_of {s : State} (h : signAArch64.pre s) : SetupPre p192 s := by
  obtain ⟨hr, hw, _, _, _, _, hd, he, hk, _, hf⟩ := h
  exact ⟨by rw [hw]; simp,
    inRegions_words (by rw [show p192.C.len = 24 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show p192.C.len = 24 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show p192.C.len = 24 from rfl, hr]; simp) (by decide), hd, he, hk, hf⟩

theorem output_of {s : State} (h : signAArch64.pre s) : SignOutput p192 s :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.P192.curve) (hI : InvSounds)
    (s : State) (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signP192 s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  have hn : CallsKeep signP192 := by lit_decide
  have hu : KeepsUntouched signP192 := by lit_decide
  have hv : signP192.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p192_ok hI) hL (setup_of hs) (output_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signP192 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

theorem sign_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : InvSounds) :
    Verified AArch64.target signP192 (Spec.Ecdsa.P192.inst.signContract AArch64.abi) :=
  Verified.of_correct (sign_a64 hL hI) sign_ct implies

end VG.Proof.Ecdsa.AArch64.P192
