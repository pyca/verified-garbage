module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OutputTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StartPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CoreReadonlyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Derive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters

/-! # Shared derivation and the outputs publish only the specified retry bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment stage_scratch_frame deriveArrays prepareArrays keyPartArrays)
open VG.Proof.RsaKeyGen.X86.KeyArgs (argsRegion)

theorem deriveArgs_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputRegion i))
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeImported E sp e p q p' q') deriveLoaded (OutputStart E sp) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, out⟩ := deriveOutput_trace E sp e p q p' q' release _ _ _ _ _ _ P A C
  have valid := P.imported.inputs.left.valid
  have widths := valid.widths
  have apart' : ∀ i < 7, (argsRegion sp).Disjoint (E.outputs.region i) := fun i hi => by
    rw [valid.outputRegion hi]
    exact apart i hi
  have frame {a b : State} {tr' : List Leak} (H : Ws a E.base E.size E.n 32)
      (L : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q a ∨
        VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p' q' a)
      (X : Exec isa deriveLoaded a tr' b) :
      ∃ rs : List Reg, Keeps rs a b ∧ .edi ∉ rs ∧ .esp ∉ rs ∧
        Frame [E.workspaceRegion, below (a.gpr .esp) 52] a.mem b.mem := by
    have go {e₁ p₁ q₁ : Nat} (L : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e₁ p₁ q₁ a) :
        ∃ rs : List Reg, Keeps rs a b ∧ .edi ∉ rs ∧ .esp ∉ rs ∧
          Frame [E.workspaceRegion, below (a.gpr .esp) 52] a.mem b.mem := by
      obtain ⟨_, O, _, K⟩ := wp_result (deriveLoaded_ok H widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
        widths.1 widths.2.1 L.pBound L.qBound L.zero L.one (L.loaded.trans L.exponent.symm)) X
      exact ⟨_, K, by decide, by decide, O.toFrame fun _ _ O =>
        stage_scratch_frame H.old (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) O⟩
    rcases L with L | L <;> exact go L
  obtain ⟨rs, KS, ediS, espS, FS⟩ := frame P.left (Or.inl P.imported.left) A
  obtain ⟨rt, KT, ediT, espT, FT⟩ := frame P.right (Or.inr P.imported.right) C
  rw [P.leftArgs.sp] at FS
  rw [P.rightArgs.sp] at FT
  exact ⟨trace, out, ⟨valid, P.leftArgs.keepBelow KS FS ediS espS, apart'⟩,
    ⟨valid, P.rightArgs.keepBelow KT FT ediT espT, apart'⟩⟩

theorem front_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputRegion i))
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeStart E sp e p q p' q') front
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true)) := by
  unfold front
  exact RelCT.seq (runtime_input_trace E sp e p q p' q')
    (RelCT.seq (deriveArgs_trace E sp e p q p' q' apart release) (writeOutputs_trace E sp))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
