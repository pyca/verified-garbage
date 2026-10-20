module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeStep
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeWitnessSpec
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDrawCTState

/-! # Public tape slices and bounded counters for repeated witness draws -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure PrimeLoopPublic (G : PrimeConfig) where
  tape : List (BitVec 8)
  used : Nat
  uniform : Nat
  usedBound : used ≤ G.tapeLen
  uniformBound : uniform < G.checks

theorem PrimeLoopPublic.bound {G : PrimeConfig} (p : PrimeLoopPublic G) : p.uniform + 1 < 2 ^ 32 := by
  have h := p.uniformBound
  unfold PrimeConfig.checks Spec.Dsa.primeChecks at h
  split at h <;> omega

structure PrimeLoopAt (G : PrimeConfig) (p : PrimeLoopPublic G) (s : State) : Prop where
  ready : PrimeReady G s
  used : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 p.used
  count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 p.uniform
  tape : Spec.Rsa.bytesAt s.mem (G.tape.setWidth 64) G.tapeLen = p.tape

theorem PrimeLoopAt.keep {G : PrimeConfig} {p : PrimeLoopPublic G} {s t : State} {rs : List Reg}
    (R : PrimeLoopAt G p s) (mem : t.mem = s.mem) (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs) :
    PrimeLoopAt G p t :=
  ⟨R.ready.unchanged mem K di sp, mem ▸ R.used, mem ▸ R.count, by rw [mem]; exact R.tape⟩

def loopDrawPublic (G : PrimeConfig) (p : PrimeLoopPublic G) (full : p.used + G.draw ≤ G.tapeLen) : PrimeDrawPublic G :=
  ⟨p.used, p.uniform, Spec.Dsa.decodeBE (VG.Proof.RsaKeyGen.seg p.tape (p.used + (G.draw - G.len)) G.len), full, p.bound⟩

theorem PrimeLoopAt.draw {G : PrimeConfig} {p : PrimeLoopPublic G} {s : State}
    (R : PrimeLoopAt G p s) (full : p.used + G.draw ≤ G.tapeLen) : PrimeDrawAt G (loopDrawPublic G p full) s := by
  refine ⟨R.ready, R.used, R.count, ?_⟩
  change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off (G.tape.setWidth 64) (p.used + (G.draw - G.len))) G.len) = _
  have enough : G.len ≤ G.draw := by unfold PrimeConfig.draw PrimeConfig.n; omega
  rw [← primeTape_segment _ _ (k := G.tapeLen) (by omega), R.tape]
  rfl

def primePublicStep (G : PrimeConfig) (p : PrimeLoopPublic G) : PrimeStepResult :=
  if p.used + G.draw ≤ G.tapeLen then
    let w := Spec.RsaKeyGen.witness (G.modulus - 1) (Spec.Dsa.decodeBE (VG.Proof.RsaKeyGen.seg p.tape (p.used + (G.draw - G.len)) G.len))
    let passed := Spec.RsaKeyGen.mrIteration G.modulus G.twos G.exponent w.1
    ⟨primeResultStatus passed (p.uniform + w.2.toNat) G.checks,
      if passed then p.uniform + w.2.toNat else p.uniform, p.used + G.draw⟩
  else ⟨0, p.uniform, p.used⟩

theorem PrimeLoopAt.stepResult {G : PrimeConfig} {p : PrimeLoopPublic G} {s : State}
    (R : PrimeLoopAt G p s) : primeStepResult G s.mem p.used p.uniform = primePublicStep G p := by
  unfold primeStepResult primePublicStep
  split
  · rename_i full
    have enough : G.len ≤ G.draw := by unfold PrimeConfig.draw PrimeConfig.n; omega
    unfold primeDrawValue
    rw [← primeTape_segment _ _ (a := p.used + (G.draw - G.len)) (n := G.len) (k := G.tapeLen) (by omega), R.tape]
  · rfl
end VG.Proof.Dsa.X86.Generation
