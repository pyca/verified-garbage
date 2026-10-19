module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSearchFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashChoice
public import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Framework.Omega

/-! # The full p search returns to the persistent seed-search state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

theorem GenerationGeometry.qDecode (p : GenerationGeometry) (seed : List Byte) :
    Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.qLen (Spec.Dsa.qCandidate (8 * p.qLen) seed)) =
      Spec.Dsa.qCandidate (8 * p.qLen) seed := by
  rw [← VG.Proof.Dsa.decodeBE_os2ip]
  apply VG.Proof.Dsa.decodeBE_encodeBE
  have h := (VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases p.qWidth with hh | hh <;> omega : 2 ≤ 8 * p.qLen) seed).2.2
  simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using h

theorem seedPrime_ok (H : GenerationHashes) (M : Mont) (K : Kernel)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 M.mm K.run p.geo.pLen p.geo.qLen) s fun t =>
      let res := Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
        (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes (p.rand.bytes.drop used)
      ∃ W' used', used' ≤ p.rand.bytes.length ∧ GenerationMemory p W' t ∧
        W' 16 = BitVec.ofNat 64 used' ∧
        (∀ k ∈ searchSlots, W' k = W k) ∧
        Spec.Rsa.bytesAt t.mem (off p.geo.B q) p.geo.qLen =
          Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) ∧
        ((W' 19 = 0 ∧ res = none) ∨
         (W' 19 = 1 ∧ ∃ value, res = some (some value, p.rand.bytes.drop used') ∧
           VG.Proof.Dsa.Generation.PDomain p.geo.pLen value ∧
           Spec.Rsa.bytesAt t.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value ∧
           Spec.Rsa.bytesAt t.mem (off p.geo.B exponent) p.geo.pLen =
             Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)) ∨
         (W' 19 = 3 ∧ res = some (none, p.rand.bytes.drop used'))) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let a := h.searchPlan seed hlen h1
  have state := h.searchState seed hlen hseed h1 hq
  have hw : a.attempt.construct.hash.len = 20 ∨ a.attempt.construct.hash.len = 32 := p.geo.qWidth
  have hc := h.scratch.sub (n := 24) (p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.control)
    (n := 24) (by decide) (by decide)) (by decide)
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have qdecode := p.geo.qDecode seed.bytes
  have remaining : a.remaining 0 used = Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
      (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes (p.rand.bytes.drop used) := by
    change VG.Proof.Dsa.Generation.primeSearch _ _ _ _ 0 _ = _
    rw [VG.Proof.Dsa.Generation.primeSearch_start]
    change Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
      (Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)))
      seed.bytes (p.rand.bytes.drop used) = _
    rw [qdecode]
  refine WP.mono (nativeSearch_ok (H.streamOK _) (H.hash_matches _) (H.hash_size _) M K
    (H.hash_width hw) (generationHash_seed hw) (H.seed_size hw) state hc h16 hu)
    fun t ⟨Wt, usedt, mt, hut, h16t, outcome, ft, rd, wr⟩ => ?_
  have ff := h.search_frame seed hlen h1 ft
  have slots : ∀ k ∈ searchSlots, Wt k = W k := by
    intro k hk
    have he := mt.slots k hk
    change Wt k = searchWords p.geo.B W k at he
    have hn : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 27 := by simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simpa [searchWords, upd, hn.1, hn.2.1, hn.2.2] using he
  have mem := h.frame mt.layout mt.rep (fun k hk => slots k (by
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [searchSlots])) ff rd wr
  refine ⟨Wt, usedt, hut, mem, h16t, slots, ?_, ?_, ff, rd, wr⟩
  · have bytes := source_octets mt.qSource
    change Spec.Rsa.bytesAt t.mem (off (W 5) q) (Spec.Dsa.encodeBE p.geo.qLen
      (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)).length =
        Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) at bytes
    simpa only [h5, VG.Proof.Dsa.encodeBE_length] using bytes
  · rcases outcome with ⟨h19, hr⟩ | ⟨h19, value, hr, bp, be⟩ | ⟨h19, hr⟩
    · exact Or.inl ⟨h19, remaining ▸ hr⟩
    · refine Or.inr (Or.inl ⟨h19, value, remaining ▸ hr, ?_, ?_, ?_⟩)
      · apply VG.Proof.Dsa.Generation.primeSearch_domain p.geo.width (H.seed_size p.geo.qWidth) seed.bytes
          (List.range (4 * (8 * p.geo.pLen))) (p.rand.bytes.drop used) (p.rand.bytes.drop usedt)
        exact remaining ▸ hr
      · change Spec.Rsa.bytesAt t.mem (off (W 5) VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value at bp
        simpa only [h5] using bp
      · change Spec.Rsa.bytesAt t.mem (off (W 5) exponent) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.geo.qLen
            (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))) at be
        simpa only [h5, qdecode] using be
    · exact Or.inr (Or.inr ⟨h19, remaining ▸ hr⟩)
end VG.Proof.Dsa.X86_64.Generation
