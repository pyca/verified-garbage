module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
public import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete verified construction of p and its generator exponent -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.Generation.Layout

theorem pConstruct_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D)
    {p : PConstructPlan} (hd : G.D = p.hash.len) {s : State} (hs : PConstructState p H s)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.hash.len) bs).length = 8 * p.hash.len) :
    WP isa (Impl.Dsa.AArch64.Generation.pConstruct G p.len p.hash.len) s fun t =>
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.hash.W 5) Impl.Dsa.Generation.Layout.p) p.len =
        Spec.Dsa.encodeBE p.len p.value ∧
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.hash.W 5) exponent) p.len =
        Spec.Dsa.encodeBE p.len ((p.value - 1) / Spec.Rsa.os2ip p.qb) ∧
      p.value % 2 = 1 ∧ p.value < 2 ^ (8 * p.len) ∧
      Lay t p.hash.F p.hash.S ∧ (∃ V, Rep t.mem p.hash.F p.hash.S V p.hash.W) ∧
      Ws t p.B p.Z (p.len / 8) ∧
      VG.Proof.Bignum.word t.mem p.B 160 = VG.Proof.Bignum.off (p.hash.W 5) Impl.Dsa.Generation.Layout.p ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hl : 2 ≤ p.len ∧ p.len ≤ 1024 ∧ p.len = 8 * (p.len / 8) ∧
      2 ≤ p.len / 8 ∧ p.len / 8 < 2 ^ 24 := by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide
  have hql : p.hash.len ≤ p.len := by rcases p.hash.width with hh | hh <;> rcases p.width with hp | hp | hp <;> omega
  unfold Impl.Dsa.AArch64.Generation.pConstruct
  rw [← p.hashCount]
  refine WP.seq (WP.mono (pBuild_ok hG hHh hsize hd hs.hash hl.1 hl.2.1 p.hashRoom
    p.hashCount hhash hseedsize p.shapedSlot hs.shapedWrite p.shapedInput p.shapedHash
    (Spec.Rsa.os2ip p.qb)) fun u ⟨he, hx, Lu, ⟨Vu, Ru⟩, rdu, wru, _, fu⟩ => ?_)
  let xb := Spec.Rsa.bytesAt u.mem (VG.Proof.Bignum.off (p.hash.W 5) shaped) p.len
  have hxb : xb.length = p.len := bytesAt_length _ _ _
  have sx : Src u p.B p.Z (VG.Proof.Bignum.off (p.hash.W 5) shaped) xb := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [hxb] at hi
      obtain ⟨r, hr, hc⟩ := hs.shapedWrite i hi
      rw [rdu, wru]
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · intro i hi; simp [xb, Spec.Rsa.bytesAt]
    · intro i hi; exact p.shapedOutside i (hxb ▸ hi)
  have sq := source_of_frame hs.qSource fu p.qHash (by rw [p.qLength]; have := p.hash.size; omega) rdu wru
  refine WP.mono (reduceFromFrame_ok Lu Ru (hs.scratch.congr wru) p.base p.workspaceRoom
    hl.2.2.2.1 (by rcases p.width with h | h | h <;> rw [h] <;> decide) hl.2.2.1 hql p.frameHeaders p.frameOutside sx sq hxb p.qLength
    (by rcases p.hash.width with hh | hh <;> omega) p.qPositive p.qFits
    (fun i hi => by rw [wru]; exact hs.pWrite i hi)
    (fun i hi => by rw [wru]; exact hs.exponentWrite i hi)
    p.pOutside p.exponentOutside p.pExponent) fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  have hvalue : Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip p.qb) = p.value := he
  have Rt := rep_of_disjoint_frame Ru ft p.frameArithmetic p.hashArithmetic
  refine ⟨by rw [tp, hvalue], by rw [te, hvalue], ?_, ?_,
    lay_of_rep Lu Ru Rt rfl kt.sp kt.wr, ⟨Vu, Rt⟩, ht, hp, ?_,
    kt.rd.trans rdu, kt.wr.trans wru⟩
  · rw [← hvalue]; exact VG.Proof.Dsa.Generation.pReduction_odd _ _
  · rw [← hvalue]
    exact Nat.lt_of_le_of_lt (VG.Proof.Dsa.Generation.pReduction_le hx.1).2 hx.2.2
  · exact (fu.mono (fun r hr => List.mem_append_left _ hr)).trans
      (ft.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.AArch64.Generation
