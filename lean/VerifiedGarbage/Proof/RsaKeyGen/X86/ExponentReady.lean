module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Exponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGaps

/-! # Preparing the exponent retains the prepared Montgomery context and constants -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

def preparedRanges (g : Geometry) : List (Nat × Nat) := ranges g.w (g.array 0) (g.array 27)

theorem prepared_preserve {g : Geometry} (v : g.Valid) {s t : Mem} (O : Outs g.W (preparedRanges g) s t)
    {j : Nat} (index : j = 4 ∨ j = 5 ∨ j = 9 ∨ j = 10) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply O.val32
  · intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl | rfl <;> rcases mem with rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
        VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega
  · have bound := v.maxWidth
    rcases index with rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega

/-- `Ready` kept by writes to the exponent's ranges. -/
theorem ready_keep {g : Geometry} (v : g.Valid) {s t : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (O : Outs g.W (preparedRanges g) s.mem t.mem) (K : Keeps clob s t) :
    Ready g c capacity p t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  have fits : ∀ r ∈ preparedRanges g, r.1 + r.2 ≤ g.L := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega
  have metadata : ∀ r ∈ preparedRanges g, (128 ≤ r.1 ∧ r.1 + r.2 ≤ 224) ∨ 256 ≤ r.1 := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · left; decide
    · right; have := v.arrayHeader 0; omega
    · right; exact v.arrayHeader 27
  have F := WorkspaceFrame.of_outs S.scratch.nowrap O
  refine ⟨Prepared.keepGaps v S.context K (by unfold clob; decide) O metadata,
    S.modulus.keep v F (fun r mem => by have := metadata r mem; omega) ?_,
    S.caller.keepOuts K (by unfold clob; decide) O fits,
    S.scratch.of_keeps K (by unfold clob; decide)⟩
  intro r mem
  simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
  have top := v.arrayHeader 0
  have before := g.arrayBefore (i := 0) (j := 27) (by decide)
  rcases mem with rfl | rfl | rfl
  · right; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega
  · left; unfold Geometry.words; omega
  · left; exact before

theorem ready_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (minusOne : val32 s.mem g.W (g.array 5) g.words = c - 1)
    (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.Exponent.code g.w (g.array 5) (g.array 0) (g.array 27)) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c ∧
      word t.mem g.W (g.array 27 + 8 * g.w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps clob s t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have apart := Prepared.paddedBefore g (i := 0) (j := 27) (by decide)
  have head := v.headerFit
  refine WP.mono (code_ok S.scratch (by have := v.minWidth; omega)
    (by have := v.arrayFit (j := 5) (by decide); unfold Geometry.words at this; omega)
    (by omega) (by omega) (by have := v.arrayHeader 0; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega)
    (by omega) S.modulus.candidate minusOne odd large) fun t ⟨E, marker, O, K⟩ => ?_
  exact ⟨ready_keep v S O K, E, marker, O, K⟩

end VG.Proof.RsaKeyGen.X86.Exponent
