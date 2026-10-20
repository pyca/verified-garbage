module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFromFrameCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameKeep

/-! # Public frame locations and separated trial stack for a complete candidate check -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure CheckPrimePublic (G : PrimeConfig) where
  frame : PrimeFramePublic G
  stack : Addr
  frameStack : Region.Disjoint ⟨frame.frame.base, frameBytes⟩ ⟨stack, 16⟩
  tapeStack : Region.Disjoint ⟨G.tape.setWidth 64, G.tapeLen⟩ ⟨stack, 16⟩

def checkTrialPublic (G : PrimeConfig) (p : CheckPrimePublic G) : TrialBridgePublic :=
  ⟨p.frame.frame, p.stack, G.modulus⟩

def CheckPrimeAt (G : PrimeConfig) (p : CheckPrimePublic G) (s : State) : Prop :=
  PrimeFromAt G p.frame s ∧ TrialBridgeAt G.len (if G.len ≤ 128 then 512 else 1024) (checkTrialPublic G p) s

theorem PrimeFromAt.keep {G : PrimeConfig} {p : PrimeFramePublic G} {s t : State} {regs : List Reg}
    (R : PrimeFromAt G p s) (mem : t.mem = s.mem) (K : Keeps regs s t) (sp : .esp ∉ regs) : PrimeFromAt G p t := by
  obtain ⟨W, R, w5, w22, tape⟩ := R
  have F : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨W, R.keep F K sp (by intro _ h; cases h) (by intro _ h; cases h), w5, w22, by rw [mem]; exact tape⟩
end VG.Proof.Dsa.X86.Generation
