module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
import VerifiedGarbage.Proof.Dsa.Generation.PReduction

/-! ### `Dsa.AArch64.Generation.PConstruct`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.ReduceFromFrame`, which only this module used -/

section

/-! # Reduce the shaped candidate from an uninitialized arithmetic workspace -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/CandidateFromFrame.lean`, which only this module imported.
section

/-! # Candidate arithmetic and output storage from retained frame arguments -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Impl.Dsa.AArch64.Generation
open VG.Impl.Dsa.Generation.Layout

theorem candidateFromFrame_ok {s : State} {B F : Addr} {Z w pLen qLen : Nat}
    {W : Nat → BitVec 64} {xb qb : List Byte}
    (h : Ws s B Z w) (hpLen : pLen = 8 * w) (hqLen : qLen ≤ pLen) (hpMax : pLen ≤ 1024)
    (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (sx : Src s B Z (off (W 5) shaped) xb) (sq : Src s B Z (off (W 5) q) qb)
    (hx : xb.length = pLen) (hq : qb.length = qLen) (hqposlen : 1 ≤ qLen)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hwide : reduceWords ≤ w) (hnarrow : qLen ≤ 32)
    (hpw : ∀ i < pLen, InRegions s.wr (off (off (W 5) p) i) 1)
    (hew : ∀ i < pLen, InRegions s.wr (off (off (W 5) exponent) i) 1)
    (hpo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) p) i))
    (heo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) exponent) i))
    (hpe : ∀ i < pLen, ∀ j < pLen, off (off (W 5) p) i ≠ off (off (W 5) exponent) j) :
    WP isa (candidateFromFrame pLen qLen) s fun t =>
      let value := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem (off (W 5) p) pLen = Spec.Dsa.encodeBE pLen value ∧
      Spec.Rsa.bytesAt t.mem (off (W 5) exponent) pLen =
        Spec.Dsa.encodeBE pLen ((value - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ word t.mem B 160 = off (W 5) p ∧ Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hpl : pLen < 2 ^ 16 := by omega
  have hql : qLen < 2 ^ 16 := by omega
  unfold candidateFromFrame
  refine WP.seq (WP.mono (candidateArguments_ok h hpl hql hsp hr hwords hsep)
    fun u ⟨hu, hxp, hxl, hqp, hqlen, hpp, hep, hm, hf, hk⟩ => ?_)
  have frame : Frm B [(128, 128)] s.mem u.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_singleton, forall_eq]
    exact h.h256
  have sxu := sx.congrK (InScr.of_frm frame bound) hk
  have squ := sq.congrK (InScr.of_frm frame bound) hk
  refine WP.mono (candidateBuild_ok hu hxp (by rw [hx]; exact hxl) hqp (by rw [hq]; exact hqlen)
    hpp hep hm sxu squ (hx.trans hpLen) (by omega) (by omega) hqpos hqfit hwide (hq ▸ hnarrow)
    (fun i hi => by rw [hk.wr]; exact hpw i (hpLen ▸ hi))
    (fun i hi => by rw [hk.wr]; exact hew i (hpLen ▸ hi))
    (fun i hi => hpo i (hpLen ▸ hi)) (fun i hi => heo i (hpLen ▸ hi))
    (fun i hi j hj => hpe i (hpLen ▸ hi) j (hpLen ▸ hj))) fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  rw [← hpLen] at tp te ft
  refine ⟨tp, te, ht, hp, ?_, (hk.trans kt).mono (by decide)⟩
  have ff : Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem u.mem := by
    intro a ha
    apply hf a
    right
    have hn := ha ⟨B, Z⟩ (by simp)
    change ¬ ofs B a < Z at hn
    have := h.h256
    omega
  exact ff.trans ft

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Generation.Layout

theorem reduceFromFrame_ok {s : State} {B F S : Addr} {Z w pLen qLen : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} {xb qb : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hS : Scr s B Z)
    (hB : W 5 + BitVec.ofNat 64 arithmetic = B)
    (hZ : slot w 16 ≤ Z) (hw1 : 2 ≤ w) (hw48 : w ≤ 48)
    (hpLen : pLen = 8 * w) (hqLen : qLen ≤ pLen)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (VG.Proof.Bignum.off F (8 * k)) 8 (VG.Proof.Bignum.off B (8 * j)) 8)
    (hframe : ∀ k < 34, ∀ i < 8, Z ≤ ofs B (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) i))
    (sx : Src s B Z (VG.Proof.Bignum.off (W 5) shaped) xb) (sq : Src s B Z (VG.Proof.Bignum.off (W 5) q) qb)
    (hx : xb.length = pLen) (hq : qb.length = qLen) (hqposlen : 1 ≤ qLen)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hwide : Impl.Dsa.AArch64.Generation.reduceWords ≤ w) (hnarrow : qLen ≤ 32)
    (hpw : ∀ i < pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) p) i) 1)
    (hew : ∀ i < pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i) 1)
    (hpo : ∀ i < pLen, Z ≤ ofs B (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) p) i))
    (heo : ∀ i < pLen, Z ≤ ofs B (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i))
    (hpe : ∀ i < pLen, ∀ j < pLen, VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) p) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) j) :
    WP isa (seqs [.block Impl.Dsa.AArch64.Generation.workspaceBase,
      Impl.Dsa.AArch64.Generation.workspace w, Impl.Dsa.AArch64.Generation.candidateFromFrame pLen qLen]) s fun t =>
      let value := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) p) pLen = Spec.Dsa.encodeBE pLen value ∧
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) exponent) pLen =
        Spec.Dsa.encodeBE pLen ((value - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ VG.Proof.Bignum.word t.mem B 160 = VG.Proof.Bignum.off (W 5) p ∧
      Frame [⟨B, Z⟩, ⟨VG.Proof.Bignum.off (W 5) p, pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, pLen⟩] s.mem t.mem ∧
      Keep (.x0 :: mmRegs) s t := by
  simp only [seqs]
  refine WP.seq (WP.mono (workspaceBase_ok L R hB) fun u ⟨hdi, hm, ku⟩ => ?_)
  have sxu := sx.congrK (fun a _ => by rw [hm]) ku
  have squ := sq.congrK (fun a _ => by rw [hm]) ku
  refine WP.seq (WP.mono (workspace_ok (hS.congr ku.wr) hdi hZ hw1 hw48)
    fun v ⟨hv, _, fv, kv⟩ => ?_)
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  have hb : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ Z := by
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega_using [hz]
  refine WP.mono (candidateFromFrame_ok hv hpLen hqLen (by omega_using [hw48, hpLen])
    (kv.sp.trans (ku.sp.trans L.sp))
    (fun k hk => by rw [kv.rd, kv.wr, ku.rd, ku.wr]; exact L.ld (d := 8 * k) (n := 8) (by unfold VG.Impl.RsaOaep.AArch64.frameBytes; omega_using [hk]))
    (fun k hk => (frame_word_of_workspace fv hb (hframe k hk)).trans (by rw [hm]; exact R.fr k hk))
    hsep (sxu.congrK (InScr.of_frm fv hb) kv) (squ.congrK (InScr.of_frm fv hb) kv)
    hx hq hqposlen hqpos hqfit hwide hnarrow
    (fun i hi => by rw [kv.wr, ku.wr]; exact hpw i hi)
    (fun i hi => by rw [kv.wr, ku.wr]; exact hew i hi) hpo heo hpe)
    fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  refine ⟨tp, te, ht, hp, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  have fs : Frame [⟨B, Z⟩, ⟨VG.Proof.Bignum.off (W 5) p, pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, pLen⟩] s.mem v.mem := by
    intro a ha
    rw [fv a (fun r hr => Or.inr (Nat.le_trans (hb r hr) (by
      have hn := ha ⟨B, Z⟩ (by simp)
      change ¬ ofs B a < Z at hn
      omega_using [hn]))), hm]
  exact fs.trans ft

end VG.Proof.Dsa.AArch64.Generation

end

end


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
  have hql : p.hash.len ≤ p.len := by rcases p.hash.width with hh | hh <;> rcases p.width with hp | hp | hp <;> omega_using [hh, hp]
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
  have sq := source_of_frame hs.qSource fu p.qHash (by rw [p.qLength]; have := p.hash.size; omega_using [this]) rdu wru
  refine WP.mono (reduceFromFrame_ok Lu Ru (hs.scratch.congr wru) p.base p.workspaceRoom
    hl.2.2.2.1 (by rcases p.width with h | h | h <;> rw [h] <;> decide) hl.2.2.1 hql p.frameHeaders p.frameOutside sx sq hxb p.qLength
    (by rcases p.hash.width with hh | hh <;> omega_using [hh]) p.qPositive p.qFits
    (by rcases p.width with hh | hh | hh <;> rw [hh] <;> decide)
    (by rcases p.hash.width with hh | hh <;> omega_using [hh])
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

end

end

/-! ### `Dsa.AArch64.Generation.PTestFull`, which only this module used -/

section

/-! # A full-width p candidate is tested by the probable-prime function -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64

theorem PrimeCallPlan.bits_eq (p : PrimeCallPlan) : 8 * p.prime.len = p.bits := by
  rw [p.len]; rcases p.supported with h | h | h | h | h <;> rw [h]

theorem pTest_full_ok (T : PrimeTest) {p : PrimeCallPlan} {used : Nat} {s : State}
    {V : Nat → Byte} {pp : Addr}
    (L : Lay s p.F p.hash) (R : Rep s.mem p.F p.hash V p.W)
    (h : Ws s p.prime.B p.prime.Z p.prime.w)
    (hptr : VG.Proof.Bignum.word s.mem p.prime.B 160 = pp)
    (hbound : p.prime.N < 256 ^ p.prime.len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) (hfull : ¬ p.prime.N < 2 ^ (8 * p.prime.len - 1))
    (hcandidate : Impl.Dsa.AArch64.ProbablePrime.candidate p.bits = Impl.Dsa.Generation.Layout.p)
    (hused : p.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.prime.rand.length)
    (hA : Scr s (p.W 5) Impl.Dsa.Generation.Layout.domainCheck)
    (htc : Covers [⟨p.prime.rp, p.prime.rand.length⟩] (s.rd ++ s.wr))
    (htape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand)
    (hcand : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off (p.W 5) Impl.Dsa.Generation.Layout.p)
      p.prime.len) = p.prime.N) :
    WP isa (Impl.Dsa.AArch64.Generation.pTest T.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status, used' ≤ p.prime.rand.length ∧ Lay t p.F p.hash ∧
        Rep t.mem p.F p.hash V (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.pTest
  refine WP.seq (WP.mono (candidateWidth_ok h hptr (by have := p.prime.len2; omega_using [this])
    hbound hbytes hrd) fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem p.F p.hash V p.W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl ku.sp ku.wr
  refine WP.ite false (by simp [hcf, hfull]) (fun he => Bool.noConfusion he) (fun _ => ?_)
  rw [p.bits_eq]
  have hin : PrimeCallInputs p.bits p.F p.hash (p.W 5) p.prime.rp p.prime.rand p.prime.N used p.W V u := {
    layout := Lu
    rep := Ru
    arena := rfl
    arenaWrite := hA.congr ku.wr
    tapePtr := p.tapePtr
    tapeLength := p.tapeLength
    usedSlot := hused
    usedBound := hu
    tapeSize := p.prime.randMax
    tapeCover := by rw [ku.rd, ku.wr]; exact htc
    tapeBytes := by rw [hm]; exact bytes_of_src htape
    candidate := by rw [hcandidate, hm, ← p.bits_eq, Nat.mul_div_cancel_left _ (by decide)]; exact hcand
    odd := p.prime.odd
    bitLen := by rw [p.prime.bitLength_eq, p.bits_eq] }
  refine WP.mono (primeCall_ok T p.supported hin p.geometry)
    fun t ⟨used', status, hb, Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
  refine ⟨used', status, hb, Lt, Rt, he, hr, ?_, rdt.trans ku.rd, wrt.trans ku.wr⟩
  rw [p.changed_eq, ← hm]
  exact ft

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PTestSmall`, which only this module used -/

section

/-! # Undersized p candidates retry without consuming witness bytes -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64

theorem pTest_small_ok {s : State} {B F S pp : Addr} {Z w len value : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64}
    (prime : Nat → Prog isa)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (h : Ws s B Z w) (hptr : VG.Proof.Bignum.word s.mem B 160 = pp)
    (hlen : 0 < len) (hbound : value < 256 ^ len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp len = Spec.Dsa.encodeBE len value)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) (hsmall : value < 2 ^ (8 * len - 1)) :
    WP isa (Impl.Dsa.AArch64.Generation.pTest prime len) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 3)) ∧
      Outside F 152 8 s.mem t.mem ∧ Keep [.x1, .x3] s t := by
  unfold Impl.Dsa.AArch64.Generation.pTest
  refine WP.seq (WP.mono (candidateWidth_ok h hptr hlen hbound hbytes hrd)
    fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl ku.sp ku.wr
  refine WP.ite true (by simp [hcf, hsmall]) (fun _ => ?_) (fun he => Bool.noConfusion he)
  refine WP.mono (stackStatus_ok Lu Ru 3 (by decide)) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  exact ⟨Lt, Rt, hm ▸ ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # A p candidate is constructed and tested entirely by verified native code -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.Generation.Layout

def PConstructTestEnd (p : PPrimalityPlan) (used : Nat) (s t : State) : Prop :=
  ∃ (used' : Nat) (status : BitVec 64) (V : Nat → Byte),
    used' ≤ p.rand.length ∧ Lay t p.construct.hash.F p.construct.hash.S ∧
    Rep t.mem p.construct.hash.F p.construct.hash.S V
      (upd (upd p.construct.hash.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.construct.len =
      Spec.Dsa.encodeBE p.construct.len p.construct.value ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.construct.hash.W 5) exponent) p.construct.len =
      Spec.Dsa.encodeBE p.construct.len ((p.construct.value - 1) / Spec.Rsa.os2ip p.construct.qb) ∧
    (p.result used = none → status = BitVec.ofNat 64 0) ∧
    (∀ b rest, p.result used = some (b, rest) →
      status = BitVec.ofNat 64 (if b then 1 else 3) ∧ used' = p.rand.length - rest.length) ∧
    Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem pConstructTest_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D) (T : PrimeTest)
    {p : PPrimalityPlan} (hd : G.D = p.construct.hash.len) {s : State}
    (hs : PConstructState p.construct H s)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.construct.hash.len) bs).length = 8 * p.construct.hash.len)
    {used : Nat} (hused : p.construct.hash.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.length)
    (htape : Src s p.construct.B p.construct.Z p.rp p.rand)
    (hA : Scr s (p.construct.hash.W 5) domainCheck)
    (htc : Covers [⟨p.rp, p.rand.length⟩] (s.rd ++ s.wr)) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.pConstruct G p.construct.len p.construct.hash.len)
      (Impl.Dsa.AArch64.Generation.pTest T.run p.construct.len)) s (PConstructTestEnd p used s) := by
  refine WP.seq (WP.mono (pConstruct_ok hG hHh hsize hd hs hhash hseedsize)
    fun u ⟨up, ue, ho, hb, Lu, ⟨Vu, Ru⟩, wu, hp, fu, rdu, wru⟩ => ?_)
  have hlen : 0 < p.construct.len ∧ p.construct.len < 2 ^ 64 := by
    rcases p.construct.width with hh | hh | hh <;> omega_using [hh]
  have hbound : p.construct.value < 256 ^ p.construct.len := by
    simpa only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using hb
  have hread : InRegions (u.rd ++ u.wr) (VG.Proof.Bignum.off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) 1 := by
    obtain ⟨r, hr, hc⟩ := hs.pWrite 0 hlen.1
    rw [rdu, wru]
    exact ⟨r, List.mem_append_right _ hr, by simpa [VG.Proof.Bignum.off] using hc⟩
  by_cases hsmall : p.construct.value < 2 ^ (8 * p.construct.len - 1)
  · refine WP.mono (pTest_small_ok T.run Lu Ru wu hp hlen.1 hbound up hread hsmall)
      fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    have ff : Frame p.testWrites u.mem t.mem := by
      intro a ha
      apply ft a
      right
      have hn := ha ⟨p.construct.hash.F, frameBytes⟩ (by simp [PPrimalityPlan.testWrites])
      change ¬ ofs p.construct.hash.F a < frameBytes at hn
      unfold frameBytes at hn
      omega_using [hn]
    have hself : upd p.construct.hash.W 16 (BitVec.ofNat 64 used) = p.construct.hash.W := by
      funext i
      by_cases hi : i = 16 <;> simp [upd, hi, hused]
    refine ⟨used, 3, Vu, hu, Lt, ?_, ?_, ?_, ?_, ?_, ?_, kt.rd.trans rdu, kt.wr.trans wru⟩
    · rw [hself]; exact Rt
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff p.pPrime (Nat.le_of_lt hlen.2), up]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff p.exponentPrime (Nat.le_of_lt hlen.2), ue]
    · simp [PPrimalityPlan.result, hsmall]
    · intro b rest hr
      simp only [PPrimalityPlan.result, hsmall, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact ⟨rfl, by simp only [List.length_drop]; omega_using [hu]⟩
    · exact (fu.mono (fun r hr => List.mem_append_left _ hr)).trans
        (ff.mono (fun r hr => List.mem_append_right _ hr))
  · have domain : VG.Proof.Dsa.Generation.PDomain p.construct.len p.construct.value :=
      ⟨p.construct.width, ho, Nat.le_of_not_gt hsmall, hb⟩
    let call := p.call domain
    have tape := source_of_frame htape fu p.tapeConstruct p.randMax rdu wru
    have hcand : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt u.mem
        (VG.Proof.Bignum.off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.construct.len) = p.construct.value := by
      rw [up]; exact VG.Proof.Dsa.decodeBE_encodeBE hbound
    have hcandidate : Impl.Dsa.AArch64.ProbablePrime.candidate call.bits = Impl.Dsa.Generation.Layout.p := by
      change (if 8 * p.construct.len ≤ 256 then _ else _) = _
      exact ite_eq_right (by rcases p.construct.width with hh | hh | hh <;> omega_using [hh])
    refine WP.mono (pTest_full_ok T (p := call) Lu Ru wu hp hbound up hread hsmall hcandidate hused hu
      (hA.congr wru) (by rw [rdu, wru]; exact htc) tape hcand)
      fun t ⟨used', status, hbound', Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
    dsimp only [call, PPrimalityPlan.call, PPrimalityPlan.prime] at he hr
    refine ⟨used', status, Vu, hbound', Lt, Rt, ?_, ?_, ?_, ?_, ?_, rdt.trans rdu, wrt.trans wru⟩
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft p.pPrime (Nat.le_of_lt hlen.2), up]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft p.exponentPrime (Nat.le_of_lt hlen.2), ue]
    · simpa only [PPrimalityPlan.result, hsmall, ite_false] using he
    · simpa only [PPrimalityPlan.result, hsmall, ite_false] using hr
    · exact (fu.mono (fun r hr => List.mem_append_left _ hr)).trans
        (ft.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.AArch64.Generation
