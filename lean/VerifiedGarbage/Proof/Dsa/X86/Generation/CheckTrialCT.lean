module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckPrimeCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFromFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory

/-! # Trial rejection preserves the public frame and untouched witness tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

def CheckTrialAt (G : PrimeConfig) (p : CheckPrimePublic G) (s : State) : Prop :=
  PrimeFromAt G p.frame s ∧ s.gpr .eax = (if Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus then 0 else 1)

theorem checkTrial_ct (G : PrimeConfig) (large : 8161 < G.modulus) : RelCT isa (Two (CheckPrimeAt G))
    (trialFromFrame G.len) (Two (CheckTrialAt G)) := by
  refine two_post (two_map (checkTrialPublic G) (fun _ _ h => h.2) (trialFromFrame_ct G.len)) ?_
  rintro p s ⟨⟨W, R, w5, w22, tape⟩, T⟩
  have inputs : TrialInputs (allocated 16 s) p.stack (W 22) (W 5) G.len (if G.len ≤ 128 then 512 else 1024) := by
    rw [w22, w5]; exact T.2.2.1
  refine WP.mono (trialFromFrame_ok R inputs T.2.1 p.frameStack large) fun t ⟨Rt, ax, F, _⟩ => ?_
  have same := drawFrame_bytes (p := G.tape.setWidth 64) (len := G.tapeLen) F
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact p.tapeStack) (by have := G.tapeLen32; omega)
  exact ⟨⟨W, Rt, w5, w22, same.trans tape⟩, ax⟩
end VG.Proof.Dsa.X86.Generation
