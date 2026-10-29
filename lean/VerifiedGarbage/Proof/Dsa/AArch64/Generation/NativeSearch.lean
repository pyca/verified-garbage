module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBody
public import VerifiedGarbage.Proof.Dsa.Generation.Search
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchLoop

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.Generation.Memory
/-! # Complete native bounded p search against the specification -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SearchSemantics.lean`, which only this module imported.
section

/-! # Match each native body result to the reviewed p-search recursion -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64

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

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SearchInvariant.lean`, which only this module imported.
section

/-! # The p-search invariant retains its exact specification result -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def SearchOutcome (p : SearchPlan) (res : Option (Option Nat × List Byte))
    (W : Nat → BitVec 64) (used : Nat) (t : State) : Prop :=
  (W 19 = BitVec.ofNat 64 0 ∧ res = none) ∨
  (W 19 = BitVec.ofNat 64 1 ∧ ∃ value,
    res = some (some value, p.attempt.rand.drop used) ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len value ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.attempt.construct.hash.W 5) exponent) p.attempt.construct.len =
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
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.rd.trans rd, hk.wr.trans wr⟩

theorem searchFinished_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) :
    SearchPayload p.C (SearchFinished p res s) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, ho, ff, rd, wr⟩ := h
  refine ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, ?_,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.rd.trans rd, hk.wr.trans wr⟩
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

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Pbkdf2.Md.AArch64

theorem nativeSearch_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash} {p : SearchPlan}
    (hG : Calls.StreamOK (if p.attempt.construct.hash.len = 20 then G1 else G256).stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.attempt.construct.hash.len = 20 then G1 else G256).D)
    (T : PrimeTest)
    (hd : (if p.attempt.construct.hash.len = 20 then G1 else G256).D = p.attempt.construct.hash.len)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs).length = 8 * p.attempt.construct.hash.len)
    {s : State} {W : Nat → BitVec 64} {used : Nat} (h : SearchMemory p W s)
    (hC : Scr s p.C 24) (hused : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.attempt.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSearch G1 G256 T.run
      p.attempt.construct.len p.attempt.construct.hash.len) s
      (SearchFinished p (p.remaining 0 used) s) := by
  have hlimit : 0 < 32 * p.attempt.construct.len ∧ 32 * p.attempt.construct.len ≤ 12288 := by
    rcases p.attempt.construct.width with hh | hh | hh <;> omega
  have hstride : p.attempt.construct.hash.count + 1 ≤ 12 := by
    have := p.attempt.construct.hash.count_le; omega
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.AArch64.Generation.primeSearch
  rw [← p.attempt.construct.hashCount]
  refine WP.seq (WP.mono (controlBase_ok (B := p.C) h.layout R (by
    rw [h.slots 5 (by simp [searchSlots])]; exact p.controlBase)) fun u ⟨udi, um, ku⟩ => ?_)
  have Ru : Rep u.mem p.attempt.construct.hash.F p.attempt.construct.hash.S V W := um ▸ R
  have Lu := lay_of_rep h.layout R Ru rfl ku.sp ku.wr
  have fu : Frame (searchWrites p.attempt p.C) s.mem u.mem := by rw [um]; exact Frame.refl _ _
  have mu := h.frame Lu ⟨V, Ru⟩ (fun _ _ => rfl) fu ku.rd ku.wr
  apply pSearch_ok hlimit.2 hlimit.1 hstride
    (searchInvariant_stable p (p.remaining 0 used) s) (searchFinished_stable p (p.remaining 0 used) s)
    (fun t ht _ _ => searchInvariant_done ht)
    (fun c v hc hi ctrl => ?_)
    (show SearchInvariant p (p.remaining 0 used) s 0 u from
      ⟨W, used, mu, hu, hused, by omega, rfl, fu, ku.rd, ku.wr⟩)
    (hC.congr ku.wr) udi
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

end VG.Proof.Dsa.AArch64.Generation
