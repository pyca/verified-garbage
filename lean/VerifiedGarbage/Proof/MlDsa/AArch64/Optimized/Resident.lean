import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix

/-! The resident core uses the established two-lane Keccak proof. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

/-- An inline paired permutation, with no custom ABI or external symbol. -/
structure Core where
  code : Prog isa
  correct : ∀ {s : State} {A B : Spec.Sha3.State}, Pairs s A B →
    WP isa code s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)

def originalCore : Core :=
  ⟨Impl.MlDsa.AArch64.Optimized.Resident.permute, VG.Proof.Sha3.AArch64.Neon.Hw.rounds2_ok⟩

def n2Core : Core :=
  ⟨.block Impl.MlDsa.AArch64.Optimized.KeccakMix.rounds, KeccakMix.rounds2_ok⟩

/-- Neither stream constrains the other: every input bit in both lanes is
covered, and the inline permutation leaves memory untouched. -/
theorem permute_ok {s : State} {A B : Spec.Sha3.State} (h : Pairs s A B) :
    WP isa Impl.MlDsa.AArch64.Optimized.Resident.permute s fun t =>
      CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) :=
  VG.Proof.Sha3.AArch64.Neon.Hw.rounds2_ok h
end VG.Proof.MlDsa.AArch64.Optimized.Resident
