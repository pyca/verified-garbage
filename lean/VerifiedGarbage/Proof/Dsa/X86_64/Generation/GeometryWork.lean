module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryHash
import VerifiedGarbage.Proof.Framework.Omega

/-! # The p phase's mutable regions leave q, the controller, and input tapes intact -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.pWork (p : GenerationGeometry) : List Region :=
  [p.part shaped p.pLen, p.part hashes ((p.count + 1) * p.qLen), p.part wrappedSeed p.qLen,
   p.part VG.Impl.Dsa.Generation.Layout.hash oRsa, retR p.F,
   p.part arithmetic arithmeticBytes, p.part VG.Impl.Dsa.Generation.Layout.p p.pLen,
   p.part exponent p.pLen, p.part arithmetic arithmeticBytes, p.part witness p.pLen,
   below p.F 128, ⟨p.F, frameBytes⟩]

theorem GenerationGeometry.small_bound (p : GenerationGeometry) {d n : Nat}
    (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) : d + n ≤ usedBytes p.pLen := by
  rcases p.width with h | h | h <;> rw [h] <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega

theorem GenerationGeometry.pWork_separate (p : GenerationGeometry) {d n : Nat}
    (which : (d = control ∧ n = 24) ∨ (d = q ∧ n = p.qLen)) :
    ∀ r ∈ p.pWork, (p.part d n).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  have hn := p.hashSizes.2.1
  have hd : d + n ≤ usedBytes p.pLen := by
    apply p.small_bound
    · rcases which with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
    · rcases which with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> unfold arithmeticBytes <;> omega
  intro r hr
  simp only [pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply p.parts_disjoint hd (p.small_bound (d := shaped) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · apply p.parts_disjoint hd (p.small_bound (d := hashes) (n := (p.count + 1) * p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · apply p.parts_disjoint hd (p.small_bound (d := wrappedSeed) (n := p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · apply p.parts_disjoint hd (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · exact (p.stack_part hd).symm.sub_right (below_sub (by decide) (by decide))
  · apply p.parts_disjoint hd (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · apply p.parts_disjoint hd (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · apply p.parts_disjoint hd (p.small_bound (d := exponent) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · apply p.parts_disjoint hd (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · apply p.parts_disjoint hd (p.small_bound (d := witness) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega
  · exact (p.stack_part hd).symm
  · exact (p.frame_part hd).symm

theorem GenerationTape.pWork {p : GenerationGeometry} (tape : GenerationTape p) :
    ∀ r ∈ p.pWork, (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  have hn := p.hashSizes.2.1
  intro r hr
  simp only [GenerationGeometry.pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tape.part (p.small_bound (d := shaped) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.part (p.small_bound (d := hashes) (n := (p.count + 1) * p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.part (p.small_bound (d := wrappedSeed) (n := p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.part (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.stack.sub_right (below_sub (by decide) (by decide))
  · exact tape.part (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.part (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.part (p.small_bound (d := exponent) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.part (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.part (p.small_bound (d := witness) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega))
  · exact tape.stack
  · exact tape.frame

end VG.Proof.Dsa.X86_64.Generation
