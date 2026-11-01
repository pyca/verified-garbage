module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRound

/-! # Witness tests retain entropy bookkeeping and the two outer round counters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRound
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def safeHeader (d : Nat) : Prop :=
  d + 4 ≤ 8 ∨ 16 ≤ d ∧ d + 4 ≤ 144 ∨ 148 ≤ d ∧ d + 4 ≤ 184 ∨
    192 ≤ d ∧ d + 4 ≤ 208 ∨ 216 ≤ d ∧ d + 4 ≤ 232 ∨ 248 ≤ d ∧ d + 4 ≤ 256

theorem ranges_apart32 {g : Geometry} {d : Nat} (safe : safeHeader d) :
    ∀ r ∈ ranges g, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro r mem
  simp only [ranges, WitnessMont.ranges, montWrites, roundWrites, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with (((rfl | rfl | rfl) | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl <;>
    simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Impl.RsaKeyGen.X86.WitnessRound.uniformOffset] <;> unfold safeHeader at safe <;> omega

theorem header32 {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {d : Nat} (safe : safeHeader d) : w32 t g.W d = w32 s g.W d :=
  congrArg BitVec.toNat (F.read32 (by have := v.headerFit; unfold safeHeader at safe; omega) (ranges_apart32 safe))

end VG.Proof.RsaKeyGen.X86.WitnessRound
