module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeContext

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHash
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeChecks
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Complete byte-string correctness of the i686 EMSA encoder -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86 Spec.RsaPkcs1Sig

theorem encode_ok {s0 : State} {x : BitVec 32} {k : Nat} (pre : EPre s0 x k) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.encode s0 (EPost s0 x k) := by
  unfold VG.Impl.RsaPkcs1Sig.X86.encode
  refine WP.seq (dispatch_ok (fun _ h => lens h) noLens x pre.hash hashes 0 (by decide) ?_ ?_
    s0 ⟨rfl, rfl, rfl, rfl⟩)
  · intro j hj eq s same
    have id : Hash.ofId x.toNat = some hashes[j] := by
      rw [eq, Nat.zero_add, ofId_hashes j hj]
    refine WP.mono (lens_ok hashes[j] s) fun s1 ⟨m1, l1, info, len⟩ => ?_
    exact checked_ok pre hashes[j] id ((same.keeps _).trans l1) (m1.trans same.2.1) info len
  · intro absent s same
    have large : hashes.length ≤ x.toNat := by
      by_contra no
      have member : x.toNat < hashes.length := by omega
      exact absent _ member (by omega)
    refine WP.mono (noLens_ok s) fun s1 ⟨m1, l1, info⟩ => ?_
    exact unchecked_ok pre (ofId_ge large) ((same.keeps _).trans l1) (m1.trans same.2.1) info

end VG.Proof.RsaPkcs1Sig.X86
