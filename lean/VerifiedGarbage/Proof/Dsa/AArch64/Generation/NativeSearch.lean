module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchInvariant
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus

/-! # Complete native bounded p search against the specification -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.MillerRabin.AArch64

theorem nativeSearch_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash} {p : SearchPlan}
    (hG : Calls.StreamOK (if p.attempt.construct.hash.len = 20 then G1 else G256).stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.attempt.construct.hash.len = 20 then G1 else G256).D)
    (M : Mont) (T : PrimeTest)
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
  refine WP.mono (searchBody_ok hG hHh hsize M T hd hhash hseedsize mv ctrl hc h16v huv)
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
