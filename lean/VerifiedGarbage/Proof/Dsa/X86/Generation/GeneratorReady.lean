module
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorEvaluate
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorEvaluate

/-! # Generator evaluation preserves p's prepared constants for the next h candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem generatorEvaluate_ready {s : State} {G : PrimeConfig} (R : PrimeReady G s)
    (fit : (s.gpr .esi).toNat + G.len ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, G.len⟩ ⟨G.base, G.size⟩) :
    WP isa (generatorEvaluate G.len) s fun t =>
      let value := wordsVal s.mem G.base (slot G.n 5) G.n ^
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) G.len) % G.modulus
      PrimeReady G t ∧ wordsVal t.mem G.base (slot G.n 6) G.n = value ∧
      t.gpr .eax = (if 1 < value then 1 else 3) ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  refine WP.mono (generatorEvaluate_ok R.context G.width rfl R.one R.r2 G.lenMin G.lenWords fit read apart)
    fun t ⟨_, value, status, O, K⟩ => ?_
  have frame : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem := by
    apply primeFrame_local O ?_ G.width G.flagRoom (by have := R.context.scr.nowrap; omega)
    intro r hr
    simp only [exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | (((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl) <;>
      simp [primeWrites, show 4 * (2 * G.n) = 8 * G.n by omega]
  exact ⟨R.keep frame K (by decide) (by decide), value, status, frame, K⟩
end VG.Proof.Dsa.X86.Generation
