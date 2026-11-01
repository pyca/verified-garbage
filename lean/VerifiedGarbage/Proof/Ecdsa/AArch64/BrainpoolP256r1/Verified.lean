module

import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64

/-! # brainpoolP256r1 signing on AArch64: correctness and constant time -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64

theorem setup_of {s : State} (h : signAArch64.pre s) : SetupPre brainpoolp256r1 s := by
  obtain ⟨hr, hw, _, _, _, _, hd, he, hk, _, hf⟩ := h
  exact ⟨by rw [hw]; simp,
    inRegions_words (by rw [show brainpoolp256r1.C.len = 32 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show brainpoolp256r1.C.len = 32 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show brainpoolp256r1.C.len = 32 from rfl, hr]; simp) (by decide), hd, he, hk, hf⟩

theorem output_of {s : State} (h : signAArch64.pre s) : SignOutput brainpoolp256r1 s :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : InvSounds)
    (s : State) (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signBrainpoolP256r1 s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  have hn : CallsKeep signBrainpoolP256r1 := by lit_decide
  have hu : KeepsUntouched signBrainpoolP256r1 := by lit_decide
  have hv : signBrainpoolP256r1.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (brainpoolp256r1_ok hI) hL (setup_of hs) (output_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signBrainpoolP256r1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : InvSounds) :
    Verified AArch64.target signBrainpoolP256r1 (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP256r1.inst AArch64.abi) :=
  Verified.of_correct (sign_a64 hL hI) sign_ct implies

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1
