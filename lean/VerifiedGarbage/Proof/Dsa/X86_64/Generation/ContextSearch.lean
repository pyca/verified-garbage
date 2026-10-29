module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryPrimality
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchPlan

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Data.Nat.Basic
/-! # The accepted subgroup supplies the bounded p-search preconditions -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeometrySearch.lean`, which only this module imported.
section

/-! # Concrete bounded p-search controller and its unchanged seed and q -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.searchPlan (p : GenerationGeometry) (seed rand : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = off p.B wrappedSeed)
    (h4 : W 4 = off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h5 : W 5 = p.B) (h0 : W 0 = off p.B shaped)
    (h13 : W 13 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SearchPlan := by
  let a := p.primalityPlan seed rand seedLength W offset carry h1 h3 h4 h2 h5 h0 h13 h15
  have writes : a.changed = p.pWork := by
    dsimp only [a, PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed,
      HashPlan.changed, GenerationGeometry.primalityPlan, GenerationGeometry.constructPlan, GenerationGeometry.hashPlan]
    rw [h5]
    rfl
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  have hc := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.control) (n := 24) (by decide) (by decide)
  have hq := p.small_bound (d := q) (n := p.qLen) (by decide) (by unfold arithmeticBytes; omega)
  have hh := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hp := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  have he := p.small_bound (d := exponent) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  refine {
    attempt := a
    C := off p.B VG.Impl.Dsa.Generation.Layout.control
    controlBase := ?_
    controlSeparate := ?_
    frameControl := p.frame_part hc
    hashControl := p.parts_disjoint hh hc (Or.inl (by decide))
    pControl := ?_
    exponentControl := ?_
    seedSeparate := ?_
    qSeparate := ?_
    tapeSeparate := ?_ }
  · change W 5 + _ = _
    rw [h5]
  · change ∀ r ∈ ⟨p.F, frameBytes⟩ :: a.changed,
      (p.part VG.Impl.Dsa.Generation.Layout.control 24).Disjoint r
    rw [writes]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (p.frame_part hc).symm
    · exact p.pWork_separate (Or.inl ⟨rfl, rfl⟩) r hr
  · change (⟨off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩ : Region).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.control 24)
    rw [h5]
    exact p.parts_disjoint hp hc (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p VG.Impl.Dsa.Generation.Layout.control; omega))
  · change (⟨off (W 5) exponent, p.pLen⟩ : Region).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.control 24)
    rw [h5]
    exact p.parts_disjoint he hc (Or.inl (by unfold exponent VG.Impl.Dsa.Generation.Layout.control; omega))
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨seed.ptr, p.qLen⟩ : Region).Disjoint r
    rw [writes, ← seedLength]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact seed.part hc
    rcases List.mem_cons.mp hr with rfl | hr
    · exact seed.frame
    exact seed.pWork r hr
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨off (W 5) q, (Spec.Dsa.encodeBE p.qLen (Spec.Dsa.qCandidate (8 * p.qLen) seed.bytes)).length⟩ : Region).Disjoint r
    rw [writes, h5, VG.Proof.Dsa.encodeBE_length]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact p.parts_disjoint hq hc (Or.inl (by unfold q VG.Impl.Dsa.Generation.Layout.control; omega))
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (p.frame_part hq).symm
    exact p.pWork_separate (Or.inr ⟨rfl, rfl⟩) r hr
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨rand.ptr, rand.bytes.length⟩ : Region).Disjoint r
    rw [writes]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rand.part hc
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rand.frame
    exact rand.pWork r hr

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def searchWords (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (off B shaped)) 2 0) 27 (off B wrappedSeed)

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
    (by simpa [searchWords, upd] using (h.slots 13 (by simp [generationSlots])).trans p.randSlot)
    (by simpa [searchWords, upd] using (h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot)

theorem GenerationMemory.searchState {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen =
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
      ∀ i < n, InRegions s.wr (off (off p.geo.B d) i) 1 := by
    intro i hi
    rw [off_off]
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
    witnessWrite := ?_
    arena := (by
      have hb := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
      have := h.scratch.sub (o := 0) (n := domainCheck) (by unfold usedBytes; omega) (by decide)
      simp only [off, BitVec.add_zero] at this
      change Scr s (W 5) domainCheck
      rw [hb]; exact this)
    tapeCover := h.rand.cover }
  · intro k hk
    change W k = searchWords p.geo.B W k
    have : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 27 := by simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp [searchWords, upd, this.1, this.2.1, this.2.2]
  · change LabAt s p.geo.F p.geo.hash (searchWords p.geo.B W) (off p.geo.B wrappedSeed) p.geo.qLen
    refine ⟨by simp [searchWords, upd], ?_, by omega, ?_, ?_, ?_⟩
    · simpa [searchWords, upd] using (h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot
    · exact Covers.right (Covers.one (h.scratch.region hb (by rcases p.geo.qWidth with hh | hh <;> omega)))
    · exact p.geo.parts_disjoint hb hh (Or.inr (by unfold wrappedSeed VG.Impl.Dsa.Generation.Layout.hash oRsa; omega))
    · exact (p.geo.stack_part hb).sub_left (below_sub (a := 16) (by decide) (by decide))
  · change ∀ i < p.geo.qLen, InRegions (s.rd ++ s.wr) (off seed.ptr i) 1
    intro i hi
    exact hseed.cover _ _ ⟨⟨seed.ptr, seed.bytes.length⟩, by simp, Offset.contains_base _ (by omega_using [hi, hlen]) (by omega_using [hi, qn])⟩
  · change Spec.Rsa.bytesAt s.mem seed.ptr p.geo.qLen = seed.bytes
    rw [← hlen]; exact hseed.bytes
  · change Src s (off p.geo.B arithmetic) arithmeticBytes (off (W 5) q)
      (Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    rw [h5]
    apply arena_source h.scratch
    · simpa only [VG.Proof.Dsa.encodeBE_length] using hqbound
    · rw [VG.Proof.Dsa.encodeBE_length]; omega
    · simpa only [VG.Proof.Dsa.encodeBE_length] using hq
    · simpa only [VG.Proof.Dsa.encodeBE_length, GenerationGeometry.part] using p.geo.parts_disjoint hqbound ha (Or.inl (by unfold q arithmetic; omega))
  all_goals
    change ∀ i < p.geo.pLen, InRegions s.wr (off (off (W 5) _) i) 1
    rw [h5]
    apply write _ p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)

end VG.Proof.Dsa.X86_64.Generation
