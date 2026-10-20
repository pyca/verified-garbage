module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReturn
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReadyMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTapeSpec
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameInputs
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRun
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeSetupFromFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTest

/-! # Complete candidate loading, primality testing, and cursor return -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

def primeFromFrameWrites (G : PrimeConfig) (frame : Addr) : List Region :=
  [⟨G.base, G.size⟩, ⟨G.witness.setWidth 64, G.len⟩, ⟨off frame 64, 16⟩]

theorem primeFromFrame_ok {G : PrimeConfig} {frame : Addr} {words : Nat → BitVec 32} {used : Nat} {s : State}
    (R : PrimeFrameInputs G frame words used s) :
    WP isa (primeFromFrame G.len) s fun t =>
      let result := primeRun G s.mem used 0
      PrimeReady G t ∧ SearchFrame t frame ∧
      FrameWords t.mem frame (frameUpdate (frameUpdate words 16 (BitVec.ofNat 32 result.used))
        19 (BitVec.ofNat 32 result.status)) ∧
      Frame (primeFromFrameWrites G frame) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have room : primeWitness + 4 ≤ G.size := by have := G.room; unfold primeWitness primeExponent at *; omega
  unfold primeFromFrame
  refine WP.seq (WP.mono (primeSetupFromFrame_ok R) fun a ⟨Ia, Fa, Wa, useda, Oa, Ka⟩ => ?_)
  have tape : Spec.Rsa.bytesAt a.mem (G.tape.setWidth 64) G.tapeLen =
      Spec.Rsa.bytesAt s.mem (G.tape.setWidth 64) G.tapeLen := by
    apply drawFrame_bytes Oa ?_ (by have := G.tapeLen32; omega)
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact G.tapeScratch
  refine WP.seq (WP.mono (primeTest_ok Ia R.usedBound useda) fun b ⟨Rb, _, status, usedb, Ob, Kb⟩ => ?_)
  rw [primeRun_tape used 0 tape] at status usedb
  have Fb := Fa.keeps Kb (by decide)
  have Wb := Wa.keep Ob (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact R.frameScratch
    · exact R.frameWitness)
  refine WP.mono (primeReturn_ok Fb Rb.context.scr Wb room R.frameScratch)
    fun t ⟨Ft, _, Wt, Ot, Kt⟩ => ?_
  rw [usedb, status] at Wt
  have returned : Frame [⟨off frame 64, 16⟩] b.mem t.mem :=
    sampleOuts_frame (Outs.of_outside Ot (rs := [(64, 16)]) (by simp)) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; decide)
  have same : ∀ d, d + 4 ≤ G.size → t.mem.readW (off G.base d) 32 = b.mem.readW (off G.base d) 32 := by
    intro d hd
    apply returned.readW (r := ⟨G.base, G.size⟩)
      (Offset.contains_base _ hd (by have := R.nowrap; omega)) ?_ (by decide)
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact R.frameScratch.symm.sub_right (Offset.sub_base _ (by unfold frameBytes; decide))
  have ready := Rb.sameWorkspace same Kt (by decide) (by decide)
  have first : Frame (primeFromFrameWrites G frame) s.mem a.mem := Oa.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [primeFromFrameWrites])
  have middle : Frame (primeFromFrameWrites G frame) a.mem b.mem := Ob.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [primeFromFrameWrites])
  have last : Frame (primeFromFrameWrites G frame) b.mem t.mem := returned.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [primeFromFrameWrites])
  exact ⟨ready, Ft, Wt, (first.trans middle).trans last,
    (Ka.trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
