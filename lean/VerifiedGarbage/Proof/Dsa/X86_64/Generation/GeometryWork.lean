module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate

/-! ### `Dsa.X86_64.Generation.GeometryHash`, which this module and modules that import it used -/

section

/-! # Concrete hash-contribution buffers for each supported parameter size -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.count (p : GenerationGeometry) : Nat := (8 * p.pLen - 1) / (8 * p.qLen)

theorem GenerationGeometry.hashSizes (p : GenerationGeometry) :
    p.count ≤ 11 ∧ (p.count + 1) * p.qLen ≤ 384 ∧ p.pLen ≤ (p.count + 1) * p.qLen := by
  unfold count
  rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide

def GenerationGeometry.hashPlan (p : GenerationGeometry) (seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = off p.B wrappedSeed)
    (h4 : W 4 = off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset) : HashPlan := by
  have hn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega_using [h]
  have hw : wrappedSeed + p.qLen ≤ usedBytes p.pLen := by
    have := p.width
    rcases this with h | h | h <;> rw [h] <;> unfold wrappedSeed usedBytes domainCheck <;> omega_using [hn]
  have hh : hashes + (p.count + 1) * p.qLen ≤ usedBytes p.pLen := by
    have hb := p.hashSizes.2.1
    rcases p.width with h | h | h <;> rw [h] <;> unfold hashes usedBytes domainCheck <;> omega_using [hb]
  have hs : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hwh : (p.part wrappedSeed p.qLen).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.hash oRsa) :=
    p.parts_disjoint hw hs (Or.inr (by decide))
  have hhh : (p.part hashes ((p.count + 1) * p.qLen)).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.hash oRsa) :=
    p.parts_disjoint hh hs (Or.inr (by decide))
  exact {
    F := p.F
    S := p.hash
    seedPtr := seed.ptr
    wrapped := off p.B wrappedSeed
    output := off p.B hashes
    len := p.qLen
    count := p.count
    offset := offset
    seed := seed.bytes
    W := W
    width := p.qWidth
    count_le := p.hashSizes.1
    carry := carry
    seed_len := seedLength
    seed_slot := h1
    wrapped_slot := h3
    output_slot := h4
    offset_slot := h2
    wrapped_sep := bufferSeparate_of_regions (len := p.qLen) (by omega_using [hn]) (p.frame_part hw).symm hwh
    output_sep := bufferSeparate_of_regions (len := (p.count + 1) * p.qLen)
      (by omega_using [p.hashSizes.2.1]) (p.frame_part hh).symm hhh
    seed_wrap := by simpa only [seedLength, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hw
    seed_output := by simpa only [seedLength, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hh
    seed_scratch := by simpa only [seedLength, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hs
    seed_stack := by simpa only [seedLength] using seed.stack.sub_right (below_sub (a := 16) (by decide) (by decide))
    output_wrap := p.parts_disjoint hh hw (Or.inr (by unfold wrappedSeed hashes; omega_using [hn]))
    output_scratch := hhh
    output_stack := (p.stack_part hh).symm.sub_right (below_sub (by decide) (by decide)) }

end VG.Proof.Dsa.X86_64.Generation

end

end

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
   below p.F 192, ⟨p.F, frameBytes⟩]

theorem GenerationGeometry.small_bound (p : GenerationGeometry) {d n : Nat}
    (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) : d + n ≤ usedBytes p.pLen := by
  rcases p.width with h | h | h <;> rw [h] <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega_using [hd, hn]

theorem GenerationGeometry.pWork_separate (p : GenerationGeometry) {d n : Nat}
    (which : (d = control ∧ n = 24) ∨ (d = q ∧ n = p.qLen)) :
    ∀ r ∈ p.pWork, (p.part d n).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega_using [h]
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega_using [h]
  have hn := p.hashSizes.2.1
  have hd : d + n ≤ usedBytes p.pLen := by
    apply p.small_bound
    · rcases which with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
    · rcases which with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> unfold arithmeticBytes <;> omega_arith
  intro r hr
  simp only [pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply p.parts_disjoint hd (p.small_bound (d := shaped) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_using [pn]
  · apply p.parts_disjoint hd (p.small_bound (d := hashes) (n := (p.count + 1) * p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [hn]))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_using [hn]
  · apply p.parts_disjoint hd (p.small_bound (d := wrappedSeed) (n := p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [qn]))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_using [qn]
  · apply p.parts_disjoint hd (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using []))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_using []
  · exact (p.stack_part hd).symm.sub_right (below_sub (by decide) (by decide))
  · apply p.parts_disjoint hd (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using []))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_arith
  · apply p.parts_disjoint hd (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_arith
  · apply p.parts_disjoint hd (p.small_bound (d := exponent) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_arith
  · apply p.parts_disjoint hd (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using []))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_arith
  · apply p.parts_disjoint hd (p.small_bound (d := witness) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
    rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      dsimp only [VG.Impl.Dsa.Generation.Layout.control, q, shaped, hashes, wrappedSeed, VG.Impl.Dsa.Generation.Layout.hash, oRsa, arithmetic,
        arithmeticBytes, VG.Impl.Dsa.Generation.Layout.p, exponent, witness] <;> omega_arith
  · exact (p.stack_part hd).symm
  · exact (p.frame_part hd).symm

theorem GenerationTape.pWork {p : GenerationGeometry} (tape : GenerationTape p) :
    ∀ r ∈ p.pWork, (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega_using [h]
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega_using [h]
  have hn := p.hashSizes.2.1
  intro r hr
  simp only [GenerationGeometry.pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tape.part (p.small_bound (d := shaped) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
  · exact tape.part (p.small_bound (d := hashes) (n := (p.count + 1) * p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [hn]))
  · exact tape.part (p.small_bound (d := wrappedSeed) (n := p.qLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [qn]))
  · exact tape.part (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using []))
  · exact tape.stack.sub_right (below_sub (by decide) (by decide))
  · exact tape.part (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using []))
  · exact tape.part (p.small_bound (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
  · exact tape.part (p.small_bound (d := exponent) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
  · exact tape.part (p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using []))
  · exact tape.part (p.small_bound (d := witness) (n := p.pLen) (by decide) (by dsimp only [arithmeticBytes, oRsa] at *; omega_using [pn]))
  · exact tape.stack
  · exact tape.frame

end VG.Proof.Dsa.X86_64.Generation
