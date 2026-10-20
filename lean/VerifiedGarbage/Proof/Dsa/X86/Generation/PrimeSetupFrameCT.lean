module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadFrameCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputArguments
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadFrameCT

/-! # Candidate loading uses only the public source and workspace frame slots -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def PrimeLoadPointers (p : PublicFrame) (s : State) : Prop :=
  s.gpr .edi = p.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic ∧
    s.gpr .esi = p.words 22 ∧ (s.gpr .esp).toNat = p.base.toNat

theorem primeSetupFromFrame_ct (len : Nat) : RelCT isa (Two (FrameAt [5, 22]))
    (primeSetupFromFrame len) (fun _ _ => True) := by
  unfold primeSetupFromFrame
  refine RelCT.seq (two_piece (Ψ := PrimeLoadPointers) [.esp] (frameAt_pins _) (by taint_decide) ?_)
    (RelCT.seq ((loadComponent_frame_ct _ _ _).mono ?_ (fun _ _ h => h)) ?_)
  · intro p s R
    refine WP.mono (primeInputArgs_ok R.1 (observedWords_rep p.base s)) fun t ⟨di, si, _, K⟩ => ?_
    exact ⟨di.trans (congrArg (· + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic) (R.2 5 (by simp))),
      si.trans (R.2 22 (by simp)), by rw [K.1 _ (by decide)]; exact R.1.esp_toNat⟩
  · rintro s t ⟨p, hs, ht⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.1.trans ht.2.1.symm
    · exact BitVec.eq_of_toNat_eq (hs.2.2.trans ht.2.2.symm)
  · exact RelCT.taint (A := taint) (τr [.edi, .esp]) (fun _ _ h => agree_regs h) (by taint_decide)
end VG.Proof.Dsa.X86.Generation
