module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrameCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrameCT

/-! # The complete native primality call accepts uninitialized arithmetic scratch -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

def CheckPrimeBefore (w candidate len draw checks : Nat) (p : PrimeFramePublic) (s : State) : Prop :=
  PrimeFrameInputs p s ∧ Scr s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z ∧
    s.gpr .x0 = p.bytes.call.draw.prime.B ∧ p.bytes.call.draw.prime.w = w ∧
    p.candidate = candidate ∧ p.bytes.call.draw.prime.len = len ∧
    p.bytes.call.draw.prime.drawBytes = draw ∧ p.bytes.call.draw.prime.checks = checks

theorem checkPrime_workspace {w candidate len draw checks : Nat} {p : PrimeFramePublic} {s : State}
    (h : CheckPrimeBefore w candidate len draw checks p s) :
    WP isa (workspace w) s (PrimeFrameBefore candidate len draw checks p) := by
  have hw := primeWorkspace_ready h.1 h.2.1 h.2.2.1
  rw [h.2.2.2.1] at hw
  exact WP.mono hw fun _ ht => ⟨ht, h.2.2.2.2⟩

theorem checkPrime_ct (M : Mont) (K : Kernel) (w candidate len draw checks : Nat)
    (hwidth : PrimeWidths len draw) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (primeArguments candidate len draw checks))) hc₂).isSome = true) :
    RelCT isa (Two (CheckPrimeBefore w candidate len draw checks))
      (checkPrime M.mm K.run w candidate len draw checks) (fun _ _ => True) := by
  unfold checkPrime
  refine RelCT.seq (two_post (two_taint [.x0] ?_ ht₁)
    (fun _ _ h => checkPrime_workspace h)) (primeFromFrame_ct M K candidate len draw checks hwidth ht₂)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.2.2.1.trans ht.2.2.1.symm

end VG.Proof.Dsa.AArch64.Generation
