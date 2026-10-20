module
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLayout
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorOutput
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReadyMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestFrame

/-! # Filter one h candidate and evaluate it using p's existing Montgomery setup -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem generatorCandidate_ok {G : PrimeConfig} {frame : Addr} {parent : BitVec 32}
    {words : Nat → BitVec 32} {s : State}
    (L : GeneratorLayout G frame parent) (R : GeneratorResources G frame parent words s)
    (fit : (s.gpr .esi).toNat + G.len ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, G.len⟩ ⟨G.base, G.size⟩) :
    WP isa (generatorCandidate G.len) s fun t =>
      let h := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) G.len)
      let e := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((generatorExponentPointer parent).setWidth 64) G.len)
      let accepted := 1 < h ∧ h < G.modulus - 1 ∧ 1 < h ^ e % G.modulus
      PrimeReady G t ∧ SearchFrame t frame ∧
      FrameWords t.mem frame (frameUpdate words 19 (if accepted then 1 else 3)) ∧
      (accepted → Spec.Rsa.bytesAt t.mem ((generatorOutputPointer parent).setWidth 64) G.len =
        Spec.Dsa.encodeBE G.len (h ^ e % G.modulus)) ∧
      Frame [⟨G.base, G.size⟩, ⟨G.witness.setWidth 64, G.len⟩, ⟨off frame 76, 4⟩,
        ⟨(generatorOutputPointer parent).setWidth 64, G.len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  let h := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) G.len)
  let e := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((generatorExponentPointer parent).setWidth 64) G.len)
  unfold generatorCandidate
  refine WP.seq (WP.mono (generatorRange_ready R.ready fit read apart) fun a ⟨Ra, hv, zf, Oa, Ka⟩ => ?_)
  change wordsVal a.mem G.base (slot G.n 5) G.n = h at hv
  change a.zf = some (decide (¬ (1 < h ∧ h < G.modulus - 1))) at zf
  have Fa := R.searchFrame.keeps Ka (by decide)
  have Wa := R.representation.keep Oa.testFrame L.frameApart
  have parentA : a.mem.readW (off frame 20) 32 = parent := (Wa 5 (by decide)).trans R.savedParent
  by_cases range : 1 < h ∧ h < G.modulus - 1
  · refine WP.ite false (by change a.zf = some false; rw [zf]; congr 1; exact decide_eq_false (fun bad => bad range))
      (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono (bufferPointer_ok Fa parentA .esi VG.Impl.Dsa.Generation.Layout.exponent)
      fun b ⟨si, mem, Kb⟩ => ?_)
    change b.gpr .esi = generatorExponentPointer parent at si
    have Rb := Ra.frame (by rw [mem]; exact Frame.refl [] a.mem) (by simp) Kb (by decide) (by decide)
    have Ksb : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s b :=
      (Ka.mono (by decide)).trans (Kb.mono (by decide))
    refine WP.seq (WP.mono (generatorEvaluate_ready Rb
      (by rw [si]; exact L.exponentFit)
      (by intro d hd; rw [si, Ksb.2.1, Ksb.2.2]; exact R.exponentRead d hd)
      (by rw [si]; exact L.exponentScratch)) fun c ⟨Rc, value, status, Oc, Kc⟩ => ?_)
    have eb : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt b.mem ((b.gpr .esi).setWidth 64) G.len) = e := by
      rw [si, mem, drawFrame_bytes Oa.testFrame L.exponentApart (by have := G.lenMax; omega)]
    rw [eb, mem, hv] at value status
    have Ksc : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s c := Ksb.trans (Kc.mono (by decide))
    have accum : PrimeTestFrame G s.mem c.mem := by
      have Ob : PrimeTestFrame G s.mem b.mem := by rw [mem]; exact Oa.testFrame
      exact Ob.trans Oc.testFrame
    have Fc := R.searchFrame.keeps Ksc (by decide)
    have Wc := R.representation.keep accum L.frameApart
    refine WP.mono (generatorOutput_ok Rc Fc Wc R.savedParent value status L.frameScratch L.outputFit
      (by intro d k hk; rw [Ksc.2.2]; exact R.outputWrite d k hk) L.outputScratch L.frameOutput)
      fun t ⟨Rt, Ft, Wt, output, Ot, Kt⟩ => ?_
    have accepted : (1 < h ∧ h < G.modulus - 1 ∧ 1 < h ^ e % G.modulus) ↔ 1 < h ^ e % G.modulus := by
      exact ⟨fun hh => hh.2.2, fun hh => ⟨range.1, range.2, hh⟩⟩
    refine ⟨Rt, Ft, ?_, fun hh => output hh.2.2, ?_, Ksc.trans Kt⟩
    · change FrameWords t.mem frame (frameUpdate words 19 (if 1 < h ∧ h < G.modulus - 1 ∧ 1 < h ^ e % G.modulus then 1 else 3))
      simpa only [accepted] using Wt
    · exact (accum.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp)).trans
        (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
  · refine WP.ite true (by change a.zf = some true; simp only [zf, range, not_false_eq_true, decide_true])
      (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (frameStatus_ok Fa Wa 3) fun t ⟨Ft, Wt, Ot, Kt⟩ => ?_
    have frameT := sampleOutside_frame Ot (by decide)
    have Rt := Ra.frame frameT (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact L.frameScratch.symm.sub_right (Offset.sub_base _ (by unfold frameBytes; decide))) Kt (by decide) (by decide)
    have rejected : ¬ (1 < h ∧ h < G.modulus - 1 ∧ 1 < h ^ e % G.modulus) := fun hh => range ⟨hh.1, hh.2.1⟩
    refine ⟨Rt, Ft, ?_, fun hh => (rejected hh).elim, ?_, (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
    · change FrameWords t.mem frame (frameUpdate words 19 (if 1 < h ∧ h < G.modulus - 1 ∧ 1 < h ^ e % G.modulus then 1 else 3))
      rw [ite_eq_right rejected]
      exact Wt
    · exact (Oa.testFrame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp)).trans
        (frameT.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp))
end VG.Proof.Dsa.X86.Generation
