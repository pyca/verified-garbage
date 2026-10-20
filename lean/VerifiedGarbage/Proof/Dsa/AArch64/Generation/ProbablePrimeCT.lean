module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyCT
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2CT
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TrialCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.Generation.Layout
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ProbablePrime
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyCT
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2CT
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TrialCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Timing of the complete native probable-prime operation. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.RsaKeyGen.AArch64 VG.Proof.MillerRabin.AArch64

structure PrimeCallPublic where
  draw : DrawPublic
  arena : Addr
  base : draw.prime.B = VG.Proof.Bignum.off arena VG.Impl.Dsa.Generation.Layout.arithmetic
  width : draw.prime.w ≤ 48
  tab : slot draw.prime.w aTab + 2048 ≤ draw.prime.Z
  large : 8161 < draw.prime.N
  policy : 1024 < Spec.Dsa.bitLength draw.prime.N ↔ 16 < draw.prime.w

def PrimeCallBefore (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  PrimeInput p.draw.prime p.draw.used s ∧ p.draw.used ≤ p.draw.prime.rand.length ∧
    p.draw.prime.len = len ∧ p.draw.prime.drawBytes = drawBytes

/-- Trial division uses only the public workspace coordinates from RSA's context. -/
def PrimeParams.trialPublic (p : PrimeParams) : VG.Proof.RsaKeyGen.AArch64.FPub :=
  ⟨p.B, p.Z, p.w, [], 0, 0, 0, [], 0, 0, 0, 0, ⟨false, false, false, none⟩⟩

theorem primeTrial_ct (len drawBytes : Nat) : RelCT isa (Two (PrimeCallBefore len drawBytes)) (seqs VG.Impl.RsaKeyGen.AArch64.Candidate.trial) (fun _ _ => True) :=
  two_map (fun p : PrimeCallPublic => p.draw.prime.trialPublic) (fun p _ h => ⟨h.1.ws, p.tab⟩) trial_ws_ct

def PrimeCallTested (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  PrimeCallBefore len drawBytes p s ∧
    isa.eval (.zero .x .x1) s = some (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength p.draw.prime.N) p.draw.prime.N)

theorem primeTrial_tested {len drawBytes : Nat} {p : PrimeCallPublic} {s : State} (h : PrimeCallBefore len drawBytes p s) :
    WP isa (seqs VG.Impl.RsaKeyGen.AArch64.Candidate.trial) s (PrimeCallTested len drawBytes p) :=
  WP.mono (primeTrial_ok h.1 p.width p.tab p.large p.policy) fun _ ⟨hz, ht, _, _⟩ => ⟨⟨ht, h.2⟩, hz⟩

theorem primeCall_setup {len drawBytes : Nat} {p : PrimeCallPublic} {s : State} (h : PrimeCallBefore len drawBytes p s) :
    PrimeSetupBefore p.draw.prime s := ⟨h.1.ws, h.1.n, p.width⟩

theorem primeCall_ready (M : Mont) {len drawBytes : Nat} {p : PrimeCallPublic} {s : State} (h : PrimeCallBefore len drawBytes p s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSetup M.mm) s
      (fun t => DrawBefore len drawBytes p.draw t ∧ p.draw.used ≤ p.draw.prime.rand.length) :=
  WP.mono (primeInputSetup_ok M h.1 p.width) fun _ ⟨ht, _, _⟩ => ⟨⟨ht, h.2.2⟩, h.2.1⟩

theorem probablePrime_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x1])
      (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc₂).isSome = true) :
    RelCT isa (Two (PrimeCallBefore len drawBytes)) (Impl.Dsa.AArch64.Generation.probablePrime M.mm K.run len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.probablePrime
  refine RelCT.seq (two_post (primeTrial_ct len drawBytes) (fun _ _ h => primeTrial_tested h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · refine RelCT.seq (two_post
      (two_map (fun p : PrimeCallPublic => p.draw.prime) (fun _ _ h => primeCall_setup h.1.1) (primeSetup_ct M))
      (fun _ _ h => primeCall_ready M h.1.1)) ?_
    exact two_map PrimeCallPublic.draw (fun _ _ h => h) (millerRabin_ct M K len drawBytes ht₁ ht₂)
  · exact two_taint [.x0] (fun _ _ _ hs ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hs.1.1.1.ws.x0.trans ht.1.1.1.ws.x0.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
