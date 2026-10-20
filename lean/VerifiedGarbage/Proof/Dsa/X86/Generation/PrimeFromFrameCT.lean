module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeSetupFrameCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameInputs
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeSetupFromFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTest
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeSetupFrameCT

/-! # The frame bridge keeps unused frame words private across the complete prime test -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure PrimeFramePublic (G : PrimeConfig) where
  frame : PublicFrame
  start : PrimeStartPublic G

def PrimeFromAt (G : PrimeConfig) (p : PrimeFramePublic G) (s : State) : Prop :=
  ∃ W, PrimeFrameInputs G p.frame.base W p.start.used s ∧
    W 5 = p.frame.words 5 ∧ W 22 = p.frame.words 22 ∧
    Spec.Rsa.bytesAt s.mem (G.tape.setWidth 64) G.tapeLen = p.start.tape

def PrimeFrameSetupAt (G : PrimeConfig) (p : PrimeFramePublic G) (s : State) : Prop :=
  PrimeTestAt G p.start s ∧ SearchFrame s p.frame.base

theorem PrimeFromAt.frame {G : PrimeConfig} {p : PrimeFramePublic G} {s : State} (R : PrimeFromAt G p s) :
    FrameAt [5, 22] p.frame s := by
  obtain ⟨W, R, w5, w22, _⟩ := R
  refine ⟨R.search, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact (R.slots 5 (by decide)).trans w5
  · exact (R.slots 22 (by decide)).trans w22

theorem primeSetup_phase_ct (G : PrimeConfig) : RelCT isa (Two (PrimeFromAt G))
    (primeSetupFromFrame G.len) (Two (PrimeFrameSetupAt G)) := by
  refine two_post (two_map (fun p => p.frame) (fun _ _ R => R.frame) (primeSetupFromFrame_ct G.len)) ?_
  rintro p s ⟨W, R, _, _, tape⟩
  refine WP.mono (primeSetupFromFrame_ok R) fun t ⟨inputs, F, _, used, O, _⟩ => ?_
  have same := drawFrame_bytes (p := G.tape.setWidth 64) (len := G.tapeLen) O
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact G.tapeScratch) (by have := G.tapeLen32; omega)
  exact ⟨⟨inputs, used, same.trans tape⟩, F⟩

theorem primeFromFrame_ct (G : PrimeConfig) : RelCT isa (Two (PrimeFromAt G))
    (primeFromFrame G.len) (fun _ _ => True) := by
  refine RelCT.seq (primeSetup_phase_ct G) (RelCT.seq
    (two_post (Ψ := fun p s => PrimeReady G s ∧ SearchFrame s p.frame.base)
      (two_map (fun p => p.start) (fun _ _ h => h.1) (primeTest_ct G)) ?_) ?_)
  · intro p s R
    refine WP.mono (primeTest_ok R.1.inputs p.start.usedBound R.1.used) fun t ⟨Rt, _, _, _, _, K⟩ => ?_
    exact ⟨Rt, R.2.keeps K (by decide)⟩
  · refine two_taint [.edi, .esp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.1.context.scr.edi_toNat.trans ht.1.context.scr.edi_toNat.symm)
    · exact BitVec.eq_of_toNat_eq (hs.2.esp_toNat.trans ht.2.esp_toNat.symm)
end VG.Proof.Dsa.X86.Generation
