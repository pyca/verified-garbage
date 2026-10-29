module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The native digest shaper emits the exact fixed-width encoding of q. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem qBuild_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp op : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) (hop : W 0 = op)
    (hout : ∀ i < len, InRegions s.wr (off op i) 1)
    (hframe : Region.Disjoint ⟨F, frameBytes⟩ ⟨op, len⟩)
    (hscratch : Region.Disjoint ⟨S, oRsa⟩ ⟨op, len⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.qCandidate G1 G256) s fun t =>
      Spec.Rsa.bytesAt t.mem op len =
        Spec.Dsa.encodeBE len (Spec.Dsa.qCandidate (8 * len) (Spec.Rsa.bytesAt s.mem rp len)) ∧
      Step F S [⟨op, len⟩] s t ∧ Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      Lay t F S ∧ ∃ V', Rep t.mem F S V' W := by
  refine WP.mono (qCandidate_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 hlen L R A hop
    hout hframe hscratch) fun t ⟨Lt, step, hf, Rt, hb⟩ => ?_
  have hhash : (Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len)).length = len := by
    rcases hlen with rfl | rfl
    · simpa only [Nat.reduceMul, Spec.Dsa.seedHash, Spec.Mgf1.sha1, beq_self_eq_true, ite_true] using (hs1 _).trans hd1
    · simpa only [Nat.reduceMul, Spec.Dsa.seedHash, Spec.Mgf1.sha256, show (256 == 160) = false from rfl,
        Bool.false_eq_true, ite_false] using (hs256 _).trans hd256
  have he := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt t.mem op len)
  rw [VG.Proof.Bignum.bytesAt_length, hb,
    VG.Proof.Dsa.Generation.qCandidate_octets (by rcases hlen with rfl | rfl <;> omega)
      _ (by rw [hhash])] at he
  exact ⟨hb.trans he.symm, step, hf.mono (by simp), Lt, Rt⟩

end VG.Proof.Dsa.AArch64.Generation
