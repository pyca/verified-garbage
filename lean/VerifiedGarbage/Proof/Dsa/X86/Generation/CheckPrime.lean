module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFromFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDecision
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTapeSpec
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameKeep
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFromFrame

/-! # Complete primality checking with trial rejection and exact witness consumption -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

def checkPrimeWrites (G : PrimeConfig) (frame stack : Addr) : List Region :=
  ⟨stack, 16⟩ :: primeFromFrameWrites G frame

theorem checkPrime_ok {G : PrimeConfig} {frame stack : Addr} {words : Nat → BitVec 32} {used : Nat} {s : State}
    (R : PrimeFrameInputs G frame words used s)
    (T : TrialInputs (allocated 16 s) stack (words 22) (words 5) G.len (if G.len ≤ 128 then 512 else 1024))
    (sp : 16 ≤ (s.gpr .esp).toNat)
    (frameStack : Region.Disjoint ⟨frame, frameBytes⟩ ⟨stack, 16⟩)
    (tapeStack : Region.Disjoint ⟨G.tape.setWidth 64, G.tapeLen⟩ ⟨stack, 16⟩)
    (large : 8161 < G.modulus) :
    WP isa (checkPrime G.len) s fun t =>
      let result := primeDecision G s.mem used
      SearchFrame t frame ∧
      FrameWords t.mem frame (frameUpdate (frameUpdate words 16 (BitVec.ofNat 32 result.used))
        19 (BitVec.ofNat 32 result.status)) ∧
      (result.status = 1 → PrimeReady G t) ∧
      Frame (checkPrimeWrites G frame stack) s.mem t.mem ∧ Keeps trialRegs s t := by
  unfold checkPrime
  refine WP.seq (WP.mono (trialFromFrame_ok R T sp frameStack large) fun a ⟨Ra, ax, Oa, Ka⟩ => ?_)
  refine WP.seq (wp_cmpi fun b ab _ zb => WP.block_nil ?_)
  have Rb := Ra.keep (rs := []) (by rw [ab.mem]; exact Frame.refl _ _) (ab.keeps []) (by decide)
    (by intro r hr; cases hr) (by intro r hr; cases hr)
  have Ob : Frame [⟨stack, 16⟩] s.mem b.mem := by rw [ab.mem]; exact Oa
  have Kb := Ka.trans (ab.keeps trialRegs)
  have first : Frame (checkPrimeWrites G frame stack) s.mem b.mem := Ob.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [checkPrimeWrites])
  by_cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus = true
  · refine WP.ite false (by simp [eval, zb, ax, composite]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.mono (frameStatus_ok Rb.search Rb.slots 3) fun t ⟨Ft, Wt, Ot, Kt⟩ => ?_
    simp only [primeDecision, composite, ite_true]
    rw [frameUpdate_same R.usedValue]
    have outside : Outside frame 64 16 b.mem t.mem := Ot.mono (by decide) (by decide)
    have last : Frame [⟨off frame 64, 16⟩] b.mem t.mem :=
      sampleOuts_frame (Outs.of_outside outside (rs := [(64, 16)]) (by simp)) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr; decide)
    exact ⟨Ft, Wt, by intro h; contradiction,
      first.trans (last.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [checkPrimeWrites, primeFromFrameWrites])),
      Kb.trans (Kt.mono (by decide))⟩
  · refine WP.ite true (by simp [eval, zb, ax, composite]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (primeFromFrame_ok Rb) fun t ⟨ready, Ft, Wt, Ot, Kt⟩ => ?_
    have tape : Spec.Rsa.bytesAt b.mem (G.tape.setWidth 64) G.tapeLen =
        Spec.Rsa.bytesAt s.mem (G.tape.setWidth 64) G.tapeLen := by
      apply drawFrame_bytes Ob ?_ (by have := G.tapeLen32; omega)
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact tapeStack
    rw [primeRun_tape used 0 tape] at Wt
    simp only [primeDecision, composite]
    exact ⟨Ft, Wt, fun _ => ready, first.trans (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)), Kb.trans Kt⟩
end VG.Proof.Dsa.X86.Generation
