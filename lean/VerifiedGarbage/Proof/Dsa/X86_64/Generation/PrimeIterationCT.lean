module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRoundCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRound
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRoundCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRound
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The guarded primality iteration reveals only the public tape and round -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaKeyGen.X86_64

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
    s.cf = some (decide (p.draw.prime.rand.length < p.draw.used + p.draw.prime.drawBytes))

theorem iterationCheck_state {len drawBytes : Nat} {p : PrimeIterationPublic} {s : State}
    (h : IterationBefore len drawBytes p s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeCheck) s (IterationChecked len drawBytes p) := by
  obtain ⟨mi, hs⟩ := h.1.1
  refine WP.mono (tapeCheck_ok hs h.2.1) fun t ⟨hcf, hm, hk⟩ => ?_
  exact ⟨⟨⟨⟨mi, hs.of_mem hm (hk.mono (by decide))⟩, h.1.2⟩, h.2.1,
    by rw [hm]; exact h.2.2.1, by rw [hm]; exact h.2.2.2.1, h.2.2.2.2⟩, hcf⟩

theorem iterationDraw_state (M : Mont) (K : Kernel) {len drawBytes : Nat}
    {p : PrimeIterationPublic} {s : State} (h : IterationBefore len drawBytes p s)
    (hr : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run) s
      (fun t => t.gpr .rdi = p.draw.prime.B) := by
  obtain ⟨mi, hs⟩ := h.1.1
  have hw := drawRound_ok M K hs hr h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  exact WP.mono hw fun _ ht => ht.1.ready.good.rdi

theorem primeIteration_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) :
    RelCT isa (Two (IterationBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.primeIteration
        (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeIteration
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => iterationCheck_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1.1
    obtain ⟨mi', ht⟩ := ht.1.1
    exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm
  · refine two_ite_seq (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    · exact two_taint [.rdi] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        obtain ⟨mi, hs⟩ := hs.1.1.1.1
        obtain ⟨mi', ht⟩ := ht.1.1.1.1
        exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm) (by taint_decide)
    · have room (p : PrimeIterationPublic) (s : State)
          (h : IterationChecked len drawBytes p s ∧ isa.eval .b s = some false) :
          p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := by
        simpa only [eval, h.1.2, Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] using h.2
      refine RelCT.seq (two_post
        (two_map PrimeIterationPublic.draw (fun p s h => ⟨h.1.1.1, room p s h⟩)
          (drawRound_ct M K len drawBytes))
        (fun p s h => iterationDraw_state M K h.1.1 (room p s h))) ?_
      exact two_taint [.rdi] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact hs.trans ht.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
