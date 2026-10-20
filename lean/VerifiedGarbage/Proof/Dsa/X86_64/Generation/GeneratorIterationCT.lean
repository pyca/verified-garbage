module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchTailCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchTailCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Timing of a complete generator tape iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem generatorSearch_before_pins (len : Nat) : Pins (GeneratorSearchBefore len) [.rsp] := by
  intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem generatorIteration_ct_of (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rsp]) (.block (chunkCheck generatorTape len)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rsp]) (.block (tapeTake generatorTape len)) hc₂).isSome = true) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  unfold tapeIteration
  refine RelCT.seq (two_piece [.rsp] (generatorSearch_before_pins len) ht₁
    (fun _ _ h => generatorSearch_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => generatorSearch_exhausted h.1 h.2)
    intro p s t hs ht r hr
    exact generatorSearch_before_pins len p s t hs.1.1 ht.1.1 r hr
  · have tail : RelCT isa (Two (GeneratorSearchAvailable len))
        (.seq (.block (tapeTake generatorTape len))
          (.seq (generatorStep Sq.mm M.mm len) (.block tapeStatus)))
        (Two (GeneratorSearchIterationAfter len)) := by
      refine RelCT.seq (two_piece [.rsp] ?_ ht₂ (fun _ _ h => generatorSearch_take h))
        (RelCT.seq (two_post (generatorSearch_body_ct M Sq len hl)
          (fun _ _ h => generatorSearch_body_ready M Sq h)) ?_)
      · intro p s t hs ht r hr
        exact generatorSearch_before_pins len p s t hs.1 ht.1 r hr
      · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => generatorSearch_status h)
        intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hs.layout.rsp.trans ht.layout.rsp.symm
    exact two_map (fun p : GeneratorSearchPublic => p)
      (fun _ _ h => generatorSearch_available h.1 h.2) tail

theorem generatorIteration_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  rcases hl with rfl | rfl | rfl
  all_goals
    exact generatorIteration_ct_of M Sq _ (by omega) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
