module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashChoice
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBody
import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
/-! # The full p search returns to the persistent seed-search state -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ContextSearchFrame.lean`, which only this module imported.
section

/-! # Lift the bounded prime search back to the persistent generation state -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem GenerationMemory.search_frame {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h1 : W 1 = seed.ptr) {m m' : Mem}
    (hf : Frame (searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C) m m') :
    Frame p.changed m m' := by
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have writes : searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C =
      p.geo.part VG.Impl.Dsa.Generation.Layout.control 24 :: ⟨p.geo.F, frameBytes⟩ :: p.geo.pWork := by
    dsimp only [searchWrites, GenerationMemory.searchPlan, GenerationGeometry.searchPlan,
      PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed,
      HashPlan.changed, GenerationGeometry.primalityPlan, GenerationGeometry.constructPlan,
      GenerationGeometry.hashPlan, searchWords, upd]
    rw [h5]
    rfl
  rw [writes] at hf
  apply GenerationContext.frame_parts hf
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have part (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed],
      p.geo.part_sub (p.geo.small_bound hd hn)⟩
  intro r hr
  simp only [GenerationGeometry.pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part VG.Impl.Dsa.Generation.Layout.control 24 (by decide) (by decide)
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact part shaped p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part hashes ((p.geo.count + 1) * p.geo.qLen) (by decide)
      (by have := p.geo.hashSizes.2.1; unfold arithmeticBytes; omega)
  · exact part wrappedSeed p.geo.qLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part VG.Impl.Dsa.Generation.Layout.hash oRsa (by decide) (by decide)
  · exact ⟨below p.geo.F 192, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part VG.Impl.Dsa.Generation.Layout.p p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part exponent p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part witness p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact ⟨below p.geo.F 192, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SearchSemantics.lean`, which only this module imported.
section

/-! # Match each native body result to the reviewed p-search recursion -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

def SearchPlan.remaining (p : SearchPlan) (counter used : Nat) : Option (Option Nat × List Byte) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * p.attempt.construct.len) (8 * p.attempt.construct.hash.len)
    (Spec.Rsa.os2ip p.attempt.construct.qb) p.attempt.construct.hash.seed counter (p.attempt.rand.drop used)

theorem SearchPlan.stepCursor {p : SearchPlan} {counter used : Nat} {b : Bool} {rest : List Byte}
    (h : p.stepResult counter used = some (b, rest)) :
    p.attempt.rand.drop (p.attempt.rand.length - rest.length) = rest := by
  unfold SearchPlan.stepResult at h
  split at h
  · cases h
    apply VG.Proof.Dsa.Generation.suffix_drop_length
    exact List.drop_suffix _ _
  · exact VG.Proof.Dsa.Generation.probablePrime_cursor h

theorem SearchPlan.remaining_step {p : SearchPlan} {counter used : Nat}
    (hc : counter < 32 * p.attempt.construct.len) :
    p.remaining counter used =
      match p.stepResult counter used with
      | none => none
      | some (true, rest) => some (some (p.candidate counter), rest)
      | some (false, rest) => p.remaining (counter + 1) (p.attempt.rand.length - rest.length) := by
  have hc' : counter < 4 * (8 * p.attempt.construct.len) := by omega
  unfold SearchPlan.remaining
  rw [VG.Proof.Dsa.Generation.primeSearch_step _ _ hc']
  rw [← p.attempt.construct.hashCount]
  change (if p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1) then _ else _) = _
  by_cases hs : p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1)
  · simp only [hs, ite_true, SearchPlan.stepResult]
    rw [VG.Proof.Dsa.Generation.suffix_drop_length (List.drop_suffix used p.attempt.rand)]
  · simp only [hs, ite_false, SearchPlan.stepResult]
    rcases hp : Spec.Dsa.probablePrime (p.candidate counter) (p.attempt.rand.drop used) with _ | ⟨b, rest⟩
    · simp only [SearchPlan.candidate] at hp
      rw [hp]
    · have hp' := hp
      simp only [SearchPlan.candidate] at hp'
      rw [hp']
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        rw [VG.Proof.Dsa.Generation.probablePrime_cursor hp]
      · rfl

theorem SearchPlan.remaining_done (p : SearchPlan) (used : Nat) :
    p.remaining (32 * p.attempt.construct.len) used = some (none, p.attempt.rand.drop used) :=
  VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SearchInvariant.lean`, which only this module imported.
section

/-! # The p-search invariant retains its exact specification result -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def SearchOutcome (p : SearchPlan) (res : Option (Option Nat × List Byte))
    (W : Nat → BitVec 64) (used : Nat) (t : State) : Prop :=
  (W 19 = BitVec.ofNat 64 0 ∧ res = none) ∨
  (W 19 = BitVec.ofNat 64 1 ∧ ∃ value,
    res = some (some value, p.attempt.rand.drop used) ∧
    Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len value ∧
    Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) exponent) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len ((value - 1) / Spec.Rsa.os2ip p.attempt.construct.qb)) ∨
  (W 19 = BitVec.ofNat 64 3 ∧ res = some (none, p.attempt.rand.drop used))

def SearchInvariant (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State)
    (counter : Nat) (t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (0 < counter → W 19 = BitVec.ofNat 64 3) ∧ res = p.remaining counter used ∧
    Frame (searchWrites p.attempt p.C) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

def SearchFinished (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    SearchOutcome p res W used t ∧ Frame (searchWrites p.attempt p.C) s.mem t.mem ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem controller_frame {C : Addr} {m m' : Mem} (hf : Outside C 0 24 m m') : Frame [⟨C, 24⟩] m m' := by
  intro a ha
  apply hf a
  right
  have hn := ha ⟨C, 24⟩ (by simp)
  change ¬ ofs C a < 24 at hn
  omega

theorem searchInvariant_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) (c : Nat) :
    SearchPayload p.C (SearchInvariant p res s c) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  exact ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, h19, hr,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.2.1.trans rd, hk.2.2.trans wr⟩

theorem searchFinished_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) :
    SearchPayload p.C (SearchFinished p res s) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, ho, ff, rd, wr⟩ := h
  refine ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, ?_,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.2.1.trans rd, hk.2.2.trans wr⟩
  rcases ho with ho | ⟨h19, value, hr, hp, he⟩ | ho
  · exact Or.inl ho
  · refine Or.inr (Or.inl ⟨h19, value, hr, ?_, ?_⟩)
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.pControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega), hp]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.exponentControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega), he]
  · exact Or.inr (Or.inr ho)

theorem searchInvariant_done {p : SearchPlan} {res : Option (Option Nat × List Byte)} {s t : State}
    (h : SearchInvariant p res s (32 * p.attempt.construct.len) t) : SearchFinished p res s t := by
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  refine ⟨W, used, hm, hu, h16, Or.inr (Or.inr ⟨h19 ?_, ?_⟩), ff, rd, wr⟩
  · rcases p.attempt.construct.width with hh | hh | hh <;> omega
  · exact hr.trans (p.remaining_done used)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/NativeSearch.lean`, which only this module imported.
section

/-! # Complete native bounded p search against the specification -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64

theorem nativeSearch_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream} {p : SearchPlan}
    (hG : Calls.StreamOK (if p.attempt.construct.hash.len = 20 then G1 else G256))
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.attempt.construct.hash.len = 20 then G1 else G256).D)
    (T : PrimeTest)
    (hd : (if p.attempt.construct.hash.len = 20 then G1 else G256).D = p.attempt.construct.hash.len)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs).length = 8 * p.attempt.construct.hash.len)
    {s : State} {W : Nat → BitVec 64} {used : Nat} (h : SearchMemory p W s)
    (hC : Scr s p.C 24) (hused : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.attempt.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSearch G1 G256 T.run
      p.attempt.construct.len p.attempt.construct.hash.len) s
      (SearchFinished p (p.remaining 0 used) s) := by
  have hlimit : 0 < 32 * p.attempt.construct.len ∧ 32 * p.attempt.construct.len ≤ 12288 := by
    rcases p.attempt.construct.width with hh | hh | hh <;> omega
  have hstride : p.attempt.construct.hash.count + 1 ≤ 12 := by
    have := p.attempt.construct.hash.count_le; omega
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.X86_64.Generation.primeSearch
  rw [← p.attempt.construct.hashCount]
  refine WP.seq (WP.mono (controlBase_ok (B := p.C) h.layout R (by
    rw [h.slots 5 (by simp [searchSlots])]; exact p.controlBase)) fun u ⟨udi, um, ku⟩ => ?_)
  have Ru : Rep u.mem p.attempt.construct.hash.F p.attempt.construct.hash.S V W := um ▸ R
  have Lu := lay_of_rep h.layout R Ru rfl (ku.gpr (by decide)) ku.2.2
  have fu : Frame (searchWrites p.attempt p.C) s.mem u.mem := by rw [um]; exact Frame.refl _ _
  have mu := h.frame Lu ⟨V, Ru⟩ (fun _ _ => rfl) fu ku.2.1 ku.2.2
  apply pSearch_ok hlimit.2 hlimit.1 hstride
    (searchInvariant_stable p (p.remaining 0 used) s) (searchFinished_stable p (p.remaining 0 used) s)
    (fun t ht _ _ => searchInvariant_done ht)
    (fun c v hc hi ctrl => ?_)
    (show SearchInvariant p (p.remaining 0 used) s 0 u from
      ⟨W, used, mu, hu, hused, by omega, rfl, fu, ku.2.1, ku.2.2⟩)
    (hC.congr ku.2.2) udi
  obtain ⟨Wv, usedv, mv, huv, h16v, _, hremaining, fv, rdv, wrv⟩ := hi
  refine WP.mono (searchBody_ok hG hHh hsize T hd hhash hseedsize mv ctrl hc h16v huv)
    fun t ⟨ct, Wt, usedt, status, mt, hut, h16t, h19t, hct, bp, be, he, hr, ft, rdt, wrt⟩ => ?_
  have frame := fv.trans ft
  have rd := rdt.trans rdv
  have wr := wrt.trans wrv
  have step := hremaining.trans (p.remaining_step hc)
  rcases result : p.stepResult c usedv with _ | ⟨b, rest⟩
  · have hs := he result
    rw [result] at step
    refine ⟨ct, 0, by decide, hct.trans hs, ?_⟩
    change SearchFinished p (p.remaining 0 used) s t
    exact ⟨Wt, usedt, mt, hut, h16t, Or.inl ⟨h19t.trans hs, step⟩, frame, rd, wr⟩
  · obtain ⟨hs, hcursor⟩ := hr b rest result
    rw [result] at step
    cases b with
    | false =>
      refine ⟨ct, 3, by decide, hct.trans hs, ?_⟩
      change SearchInvariant p (p.remaining 0 used) s (c + 1) t
      refine ⟨Wt, usedt, mt, hut, h16t, fun _ => h19t.trans hs, ?_, frame, rd, wr⟩
      rw [hcursor]
      exact step
    | true =>
      refine ⟨ct, 1, by decide, hct.trans hs, ?_⟩
      change SearchFinished p (p.remaining 0 used) s t
      refine ⟨Wt, usedt, mt, hut, h16t, Or.inr (Or.inl ⟨h19t.trans hs, p.candidate c, ?_, bp, be⟩), frame, rd, wr⟩
      rw [hcursor, p.stepCursor result]
      exact step

end VG.Proof.Dsa.X86_64.Generation
end

end

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

theorem seedPrime_ok (H : GenerationHashes) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 T.run p.geo.pLen p.geo.qLen) s fun t =>
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
  refine WP.mono (nativeSearch_ok (H.streamOK _) (H.hash_matches _) (H.hash_size _) T
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
