module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometrySearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset

/-! # The accepted subgroup supplies the bounded p-search preconditions -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def searchWords (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (VG.Proof.Bignum.off B shaped)) 2 0) 25 (VG.Proof.Bignum.off B wrappedSeed)

def GenerationMemory.searchPlan {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h1 : W 1 = seed.ptr) : SearchPlan :=
  p.geo.searchPlan seed p.rand hlen (searchWords p.geo.B W) 0
    (by have := p.geo.hashSizes.1; omega)
    (by simpa [searchWords, upd] using h1)
    (by simpa [searchWords, upd] using (h.slots 3 (by simp [generationSlots])).trans p.wrappedSlot)
    (by simpa [searchWords, upd] using (h.slots 4 (by simp [generationSlots])).trans p.hashesSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, upd] using (h.slots 5 (by simp [generationSlots])).trans p.baseSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, upd] using (h.slots 14 (by simp [generationSlots])).trans p.randSlot)
    (by simpa [searchWords, upd] using (h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot)

theorem GenerationMemory.searchState {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)) :
    SearchMemory (h.searchPlan seed hlen h1) W s := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have ha := p.geo.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hqbound := p.geo.small_bound (d := q) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega)
  have hb := p.geo.small_bound (d := wrappedSeed) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega)
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have write (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∀ i < n, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B d) i) 1 := by
    intro i hi
    rw [VG.Proof.Bignum.off_off]
    exact h.scratch.region (by have := p.geo.small_bound hd hn; omega) (by decide)
  refine {
    layout := h.layout
    rep := h.rep
    slots := ?_
    label := ?_
    seedRead := ?_
    wrappedWrite := write wrappedSeed p.geo.qLen (by decide) (by unfold arithmeticBytes; omega)
    hashWrite := write hashes ((p.geo.count + 1) * p.geo.qLen) (by decide)
      (by have := p.geo.hashSizes.2.1; unfold arithmeticBytes; omega)
    seed := ?_
    scratch := h.scratch.sub (n := arithmeticBytes) ha (by decide)
    qSource := ?_
    tape := h.rand.source ha
    shapedWrite := ?_
    pWrite := ?_
    exponentWrite := ?_
    witnessWrite := ?_ }
  · intro k hk
    change W k = searchWords p.geo.B W k
    have : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 25 := by simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp [searchWords, upd, this.1, this.2.1, this.2.2]
  · change LabAt s p.geo.F p.geo.hash (searchWords p.geo.B W) (VG.Proof.Bignum.off p.geo.B wrappedSeed) p.geo.qLen
    refine ⟨by simp [searchWords, upd], ?_, by omega, ?_, ?_, ?_, ?_⟩
    · simpa [searchWords, upd] using (h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot
    · exact Covers.right (Covers.one (h.scratch.region hb (by rcases p.geo.qWidth with hh | hh <;> omega)))
    · exact p.geo.parts_disjoint hb hh (Or.inr (by unfold wrappedSeed VG.Impl.Dsa.Generation.Layout.hash oRsa; omega))
    · exact (p.geo.frame_part hb).symm
    · exact (p.geo.stack_part hb).sub_left (below_sub (a := 16) (by decide) (by decide))
  · change ∀ i < p.geo.qLen, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off seed.ptr i) 1
    intro i hi
    exact hseed.cover _ _ ⟨⟨seed.ptr, seed.bytes.length⟩, by simp, Offset.contains_base _ (by omega_using [hi, hlen]) (by omega_using [hi, qn])⟩
  · change Spec.Rsa.bytesAt s.mem seed.ptr p.geo.qLen = seed.bytes
    rw [← hlen]; exact hseed.bytes
  · change Src s (VG.Proof.Bignum.off p.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (W 5) q)
      (Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    rw [h5]
    apply arena_source h.scratch
    · simpa only [VG.Proof.Dsa.encodeBE_length] using hqbound
    · rw [VG.Proof.Dsa.encodeBE_length]; omega
    · simpa only [VG.Proof.Dsa.encodeBE_length] using hq
    · simpa only [VG.Proof.Dsa.encodeBE_length, GenerationGeometry.part] using p.geo.parts_disjoint hqbound ha (Or.inl (by unfold q arithmetic; omega))
  all_goals
    change ∀ i < p.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) _) i) 1
    rw [h5]
    apply write _ p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)

end VG.Proof.Dsa.AArch64.Generation
