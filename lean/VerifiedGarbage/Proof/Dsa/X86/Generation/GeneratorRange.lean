module
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleHead

/-! # Generator range rejection preserves the prepared p context and all h bytes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem generatorRange_ready {s : State} {G : PrimeConfig} (R : PrimeReady G s)
    (fit : (s.gpr .esi).toNat + G.len ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, G.len⟩ ⟨G.base, G.size⟩) :
    WP isa (sampleHead G.len) s fun t =>
      let h := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) G.len)
      PrimeReady G t ∧ wordsVal t.mem G.base (slot G.n 5) G.n = h ∧
      t.zf = some (decide (¬ (1 < h ∧ h < G.modulus - 1))) ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (sampleHead_ok R.context G.width G.flagRoom R.one rfl G.lenMin G.lenWords fit read apart)
    fun t ⟨_, value, _, zf, _, O, K⟩ => ?_
  have frame : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem :=
    primeFrame_sample (O.mono (by intro r hr; exact List.mem_append_left _ hr))
  refine ⟨R.keep frame K (by decide) (by decide), value, ?_, frame, K⟩
  rw [zf]
  congr 2
end VG.Proof.Dsa.X86.Generation
