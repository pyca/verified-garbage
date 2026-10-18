module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawRoundCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawRoundCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControlCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControlCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # The guarded primality iteration reveals only the public tape and round -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Proof.RsaKeyGen.AArch64

structure PrimeIterationPublic where
  draw : DrawPublic
  i : Nat
  uni : Nat

def IterationBefore (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  DrawBefore len drawBytes p.draw s ∧ p.draw.used ≤ p.draw.prime.rand.length ∧
    word s.mem p.draw.prime.B (8 * kI) = BitVec.ofNat 64 p.i ∧
    word s.mem p.draw.prime.B (8 * kUni) = BitVec.ofNat 64 p.uni ∧
    p.i < 2 ^ 62 ∧ p.uni < 2 ^ 62

def IterationChecked (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  IterationBefore len drawBytes p s ∧
    isa.eval (.zero .x .x5) s = some (decide (p.draw.prime.rand.length < p.draw.used + p.draw.prime.drawBytes))

theorem iterationCheck_state {len drawBytes : Nat} {p : PrimeIterationPublic} {s : State}
    (h : IterationBefore len drawBytes p s) :
    WP isa (.block Impl.Dsa.AArch64.Generation.tapeCheck) s (IterationChecked len drawBytes p) := by
  have hs := h.1.1
  refine WP.mono (tapeCheck_ok hs h.2.1) fun t ⟨hcf, hm, hk⟩ => ?_
  exact ⟨⟨⟨hs.of_mem hm (hk.mono (by decide)), h.1.2⟩, h.2.1,
    by rw [hm]; exact h.2.2.1, by rw [hm]; exact h.2.2.2.1, h.2.2.2.2⟩, hcf⟩

theorem iterationDraw_state (M : Mont) (K : Kernel) {len drawBytes : Nat}
    {p : PrimeIterationPublic} {s : State} (h : IterationBefore len drawBytes p s)
    (hr : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes) s
      (fun t => t.gpr .x0 = p.draw.prime.B) := by
  have hs := h.1.1
  have hw := drawRound_ok M K hs hr h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  rw [h.1.2.1, h.1.2.2] at hw
  exact WP.mono hw fun _ ht => ht.1.ready.ws.x0

theorem primeIteration_ct (M : Mont) (K : Kernel) (len drawBytes : Nat)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x1])
      (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc₂).isSome = true) :
    RelCT isa (Two (IterationBefore len drawBytes))
      (Impl.Dsa.AArch64.Generation.primeIteration
        (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes)) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.primeIteration
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.x0] ?_ (by taint_decide))
    (fun _ _ h => iterationCheck_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    have hs := hs.1.1
    have ht := ht.1.1
    exact hs.ready.ws.x0.trans ht.ready.ws.x0.symm
  · refine two_ite_seq (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
    · exact two_taint [.x0] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        have hs := hs.1.1.1.1
        have ht := ht.1.1.1.1
        exact hs.ready.ws.x0.trans ht.ready.ws.x0.symm) (by taint_decide)
    · have room (p : PrimeIterationPublic) (s : State)
          (h : IterationChecked len drawBytes p s ∧ isa.eval (.zero .x .x5) s = some false) :
          p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := by
        have he := Option.some.inj (h.1.2.symm.trans h.2)
        simpa only [decide_eq_false_iff_not, Nat.not_lt] using he
      refine RelCT.seq (two_post
        (two_map PrimeIterationPublic.draw (fun p s h => ⟨h.1.1.1, room p s h⟩)
          (drawRound_ct M K len drawBytes ht₁ ht₂))
        (fun p s h => iterationDraw_state M K h.1.1 (room p s h))) ?_
      exact two_taint [.x0] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact hs.trans ht.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
