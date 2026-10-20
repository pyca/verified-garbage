module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidthCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidth

/-! # Full-width candidates proceed to the shared native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Dsa.X86_64.Generation

structure PTestFullPublic where
  width : CandidateWidthPublic
  call : PrimeFramePublic
  full : ¬ width.value < 2 ^ (8 * width.len - 1)

def PTestFullBefore (len : Nat) (p : PTestFullPublic) (s : State) : Prop :=
  CheckPrimeBefore (len / 8) Impl.Dsa.Generation.Layout.p len len
    (if len ≤ 256 then 64 else 128) p.call s ∧ CandidateWidthBefore p.width s

theorem pTestFull_ready {len : Nat} {p : PTestFullPublic} {s : State}
    (h : PTestFullBefore len p s) : WP isa (.block candidateWidth) s fun t =>
      CheckPrimeBefore (len / 8) Impl.Dsa.Generation.Layout.p len len
        (if len ≤ 256 then 64 else 128) p.call t ∧ t.cf = some false := by
  refine WP.mono (candidateWidth_ok h.2.ws h.2.pointer p.width.positive p.width.fits h.2.bytes h.2.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  refine ⟨⟨?_, h.1.2.1.congr hk.2.2, (hk.gpr (by decide)).trans h.1.2.2.1, h.1.2.2.2⟩,
    by simp [cf, p.full]⟩
  exact ⟨(hk.gpr (by decide)).trans h.1.1.stack,
    (fun k hk' => by rw [hk.2.1, hk.2.2]; exact h.1.1.read k hk'),
    hm ▸ h.1.1.arena, hm ▸ h.1.1.tapePtr, hm ▸ h.1.1.tapeLength, hm ▸ h.1.1.used,
    h.1.1.tape.congrK (fun _ _ => by rw [hm]) hk,
    h.1.1.source.congrK (fun _ _ => by rw [hm]) hk,
    (fun i hi => by rw [hk.2.2]; exact h.1.1.writable i hi), hk.2.2.trans h.1.1.wr, h.1.1.usedBound⟩

theorem pTest_full_ct (M : Mont) (K : Kernel) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PTestFullBefore len)) (pTest M.mm K.run len) (fun _ _ => True) := by
  unfold pTest
  refine RelCT.seq (two_post ((two_map PTestFullPublic.width (fun _ _ h => h.2) candidateWidth_ct).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => pTestFull_ready h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _⟩
    simpa only [eval, hs.1.2, Bool.false_eq_true, Option.some.injEq] using hs.2
  · apply two_map PTestFullPublic.call (fun _ _ h => h.1.1)
    apply primeCall_ct M K
    rcases hlen with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)))

end VG.Proof.Dsa.X86_64.Generation
