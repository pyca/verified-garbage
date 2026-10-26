module
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Hashing and shaping construct q while retaining the complete caller frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64 VG.Proof.Pbkdf2.Md.AArch64
open VG.Proof.Ffdh.ParameterCandidate

theorem qCandidate_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp qp : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) (hp : W 0 = qp)
    (hqw : ∀ i < len, InRegions s.wr (VG.Proof.Bignum.off qp i) 1)
    (dFQ : Region.Disjoint ⟨F, frameBytes⟩ ⟨qp, len⟩)
    (dSQ : Region.Disjoint ⟨S, oRsa⟩ ⟨qp, len⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.qCandidate G1 G256) s fun t =>
      Lay t F S ∧ Step F S [⟨qp, len⟩] s t ∧
      Frame [⟨S, oRsa⟩, ⟨qp, len⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem qp len = shapedOctets
        (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)) 7 := by
  unfold Impl.Dsa.AArch64.Generation.qCandidate
  refine WP.seq (WP.mono (seedHash_frame_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 hlen L R A)
    fun u ⟨Lu, step, huf, V', Ru, _, hdigest⟩ => ?_)
  refine WP.seq (WP.mono (qArgs_ok Lu Ru hp A.hll) fun v ⟨hv2, hv12, hv9, hvm, kv⟩ => ?_)
  have bslen : (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)).length = len := by
    rw [← hdigest, bytesAt_length]
  have Lv : Lay v F S := Lu.congr kv.sp kv.wr (by rw [hvm])
  have Rv : Rep v.mem F S V' W := hvm ▸ Ru
  have hread : ∀ i < len, InRegions (v.rd ++ v.wr) (VG.Proof.Bignum.off (VG.Proof.Bignum.off S oDig) i) 1 := by
    intro i hi
    rw [kv.rd, kv.wr, VG.Proof.Bignum.off_off]
    exact Lu.sld (o := oDig + i) (n := 1) (by rcases hlen with rfl | rfl <;> simp only [oDig, oRsa] <;> omega)
  have hwrite : ∀ i < len, InRegions v.wr (VG.Proof.Bignum.off qp i) 1 := by
    intro i hi; rw [kv.wr, step.wr]; exact hqw i hi
  have hsep : ∀ i < len, ∀ j < len, VG.Proof.Bignum.off (VG.Proof.Bignum.off S oDig) i ≠ VG.Proof.Bignum.off qp j := by
    intro i hi j hj he
    apply dSQ (VG.Proof.Bignum.off qp j)
    · rw [← he, VG.Proof.Bignum.off_off]
      exact cS S (o := oDig + i) (n := 1) (by rcases hlen with rfl | rfl <;> simp only [oDig, oRsa] <;> omega)
    · exact Offset.contains_base qp (by omega) (by rcases hlen with rfl | rfl <;> omega)
  have hbytes : ∀ i < len, v.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off S oDig) i) =
      (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)).getD i 0 := by
    intro i hi
    have hh := congrArg (fun xs : List Byte => xs.getD i 0) hdigest
    simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi, VG.Proof.Bignum.off, hvm] using hh
  have hshape := qShape_ok (bs := Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len))
    (by rw [bslen]; rcases hlen with rfl | rfl <;> omega)
    (by rw [bslen]; rcases hlen with rfl | rfl <;> omega)
    hv12 hv2 (by rw [bslen]; exact hv9) (by rw [bslen]; exact hread)
    (by rw [bslen]; exact hwrite) (by rw [bslen]; exact hbytes) (by rw [bslen]; exact hsep)
  rw [bslen] at hshape
  refine WP.mono hshape fun t ⟨hq, hf, kt⟩ => ?_
  have hwords : ∀ d, d + 8 ≤ frameBytes → VG.Proof.Bignum.word t.mem F d = VG.Proof.Bignum.word v.mem F d :=
    words_outside_bytes (by decide) hf (fun i hi =>
      out_scr dFQ.symm (Offset.contains_base qp (by omega) (by rcases hlen with rfl | rfl <;> omega)))
  have Lt : Lay t F S := Lv.congr kt.sp kt.wr (hwords sScr (by decide))
  have qframe : Frame [⟨qp, len⟩] v.mem t.mem := by
    intro a ha
    apply hf
    intro i hi he
    apply ha ⟨qp, len⟩ (by simp)
    rw [he]
    exact Offset.contains_base qp (by omega) (by rcases hlen with rfl | rfl <;> omega)
  have hfinal : Frame [⟨S, oRsa⟩, ⟨qp, len⟩, retR F] s.mem t.mem := by
    have hvf : Frame [⟨S, oRsa⟩, retR F] s.mem v.mem := by rw [hvm]; exact huf
    exact (hvf.mono (by simp)).trans (qframe.mono (by simp))
  have k := kv.trans kt
  refine ⟨Lt, ⟨k.rd.trans step.rd, k.wr.trans step.wr, k.sp.trans step.sp, ?_,
    step.vec.trans k.vcs, hfinal.mono (by simp)⟩, hfinal, ⟨fun o => t.mem (VG.Proof.Bignum.off S o), ?_⟩, hq⟩
  · intro r hr h30
    trans u.gpr r
    · apply k.gpr r
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | decide | exact (h30 rfl).elim
    · exact step.cs r hr h30
  · exact ⟨fun _ _ => rfl, fun k hk => (hwords (8 * k) (by unfold nW at hk; omega)).trans (Rv.fr k hk)⟩

end VG.Proof.Dsa.AArch64.Generation
