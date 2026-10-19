module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidthCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt

/-! # Full-width candidates proceed to the shared native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

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
        (if len ≤ 256 then 64 else 128) p.call t ∧ eval (.zero .x .x3) t = some false := by
  refine WP.mono (candidateWidth_ok h.2.ws h.2.pointer p.width.positive p.width.fits h.2.bytes h.2.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  refine ⟨⟨?_, h.1.2.1.congr hk.wr, (hk.gpr _ (by decide)).trans h.1.2.2.1, h.1.2.2.2⟩,
    by simpa only [decide_eq_false p.full] using cf⟩
  exact ⟨hk.sp.trans h.1.1.stack,
    (fun k hk' => by rw [hk.rd, hk.wr]; exact h.1.1.read k hk'),
    hm ▸ h.1.1.arena, hm ▸ h.1.1.tapePtr, hm ▸ h.1.1.tapeLength, hm ▸ h.1.1.used,
    h.1.1.tape.congrK (fun _ _ => by rw [hm]) hk,
    h.1.1.source.congrK (fun _ _ => by rw [hm]) hk,
    (fun i hi => by rw [hk.wr]; exact h.1.1.writable i hi), h.1.1.usedBound⟩

theorem pTest_full_ct (M : Mont) (K : Kernel) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PTestFullBefore len)) (pTest M.mm K.run len) (fun _ _ => True) := by
  unfold pTest
  refine RelCT.seq (two_post ((two_map PTestFullPublic.width (fun _ _ h => h.2) candidateWidth_ct).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => pTestFull_ready h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _, _⟩
    cases Option.some.inj (hs.1.2.symm.trans hs.2)
  · apply two_map PTestFullPublic.call (fun _ _ h => h.1.1)
    apply primeCall_ct M K
    rcases hlen with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)))

end VG.Proof.Dsa.AArch64.Generation
