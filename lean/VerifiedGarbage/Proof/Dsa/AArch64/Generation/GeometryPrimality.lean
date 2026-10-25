module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryConstruct
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Concrete p-primality buffers preserve the generated candidate and exponent -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.primalityPlan (p : GenerationGeometry) (seed rand : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = VG.Proof.Bignum.off p.B wrappedSeed)
    (h4 : W 4 = VG.Proof.Bignum.off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B shaped)
    (h14 : W 14 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : PPrimalityPlan := by
  have bound (d : Nat) (hd : d ≤ domainCheck) (n : Nat) (hn : n ≤ arithmeticBytes) :
      d + n ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  have ha := bound arithmetic (by decide) arithmeticBytes (by rfl)
  have hh := bound VG.Impl.Dsa.Generation.Layout.hash (by decide) oRsa (by decide)
  have hw := bound witness (by decide) p.pLen (by unfold arithmeticBytes; omega)
  have hp := bound VG.Impl.Dsa.Generation.Layout.p (by decide) p.pLen (by unfold arithmeticBytes; omega)
  have he := bound exponent (by decide) p.pLen (by unfold arithmeticBytes; omega)
  refine {
    construct := p.constructPlan seed seedLength W offset carry h1 h3 h4 h2 h5 h0
    rand := rand.bytes
    rp := rand.ptr
    size := rfl
    tapePtr := h14
    tapeLength := h15
    randMax := rand.size
    bufferSeparate := ?_
    bufferOutside := ?_
    tapeBuffer := ?_
    framePrime := ?_
    hashPrime := ?_
    pPrime := ?_
    exponentPrime := ?_
    tapeConstruct := ?_ }
  · change (p.part arithmetic arithmeticBytes).Disjoint ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩
    rw [h5]
    exact p.parts_disjoint ha hw (Or.inr (by unfold witness arithmetic; omega))
  · change ∀ i < p.pLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) witness) i)
    rw [h5]
    intro i hi
    exact out_scr (p.parts_disjoint hw ha (Or.inl (by unfold witness arithmetic; omega)))
      (Offset.contains_base _ (by omega) (by omega))
  · change (⟨rand.ptr, rand.bytes.length⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩
    rw [h5]
    exact rand.part hw
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩],
      (⟨p.F, frameBytes⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.frame_part ha
    · exact p.frame_part hw
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩],
      (⟨p.hash, oRsa⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.parts_disjoint hh ha (Or.inl (by decide))
    · exact p.parts_disjoint hh hw (Or.inl (by decide))
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩, ⟨p.F, frameBytes⟩],
      (⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.parts_disjoint hp ha (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p arithmetic; omega))
    · exact p.parts_disjoint hp hw (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p witness; omega))
    · exact (p.frame_part hp).symm
  · change ∀ r ∈ [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) witness, p.pLen⟩, ⟨p.F, frameBytes⟩],
      (⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.parts_disjoint he ha (Or.inl (by unfold exponent arithmetic; omega))
    · exact p.parts_disjoint he hw (Or.inl (by unfold exponent witness; omega))
    · exact (p.frame_part he).symm
  · change ∀ r ∈ (⟨VG.Proof.Bignum.off (W 5) shaped, p.pLen⟩ ::
      [⟨VG.Proof.Bignum.off p.B hashes, (p.count + 1) * p.qLen⟩, ⟨VG.Proof.Bignum.off p.B wrappedSeed, p.qLen⟩, ⟨p.hash, oRsa⟩, retR p.F]) ++
      [⟨VG.Proof.Bignum.off p.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩],
      (⟨rand.ptr, rand.bytes.length⟩ : Region).Disjoint r
    rw [h5]
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rand.part (bound shaped (by decide) p.pLen (by unfold arithmeticBytes; omega))
    · exact rand.part (bound hashes (by decide) ((p.count + 1) * p.qLen) (by
        have := p.hashSizes.2.1; unfold arithmeticBytes; omega))
    · exact rand.part (bound wrappedSeed (by decide) p.qLen (by unfold arithmeticBytes; omega))
    · exact rand.part hh
    · exact rand.stack.sub_right (below_sub (by decide) (by decide))
    · exact rand.part ha
    · exact rand.part hp
    · exact rand.part he

end VG.Proof.Dsa.AArch64.Generation
