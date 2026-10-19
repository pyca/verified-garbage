module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeContext

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHash
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeChecks

/-! # Complete byte-string correctness of the i686 EMSA encoder -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86 Spec.RsaPkcs1Sig

theorem encode_ok {s0 : State} {x : BitVec 32} {k : Nat} (pre : EPre s0 x k) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.encode s0 (EPost s0 x k) := by
  unfold VG.Impl.RsaPkcs1Sig.X86.encode
  refine dispatch_ok (fun _ h => encodeHash h) fail x pre.hash hashes 0 (by decide) ?_ ?_
    s0 ⟨rfl, rfl, rfl, rfl⟩
  · intro j hj eq s same
    have id : Hash.ofId x.toNat = some hashes[j] := by
      rw [eq, Nat.zero_add, ofId_hashes j hj]
    exact encodeHash_ok pre hashes[j] id same
  · intro absent s same
    have large : hashes.length ≤ x.toNat := by
      by_contra no
      have member : x.toNat < hashes.length := by omega
      exact absent _ member (by omega)
    apply refuse_ok (same.keeps _) same.2.1
    simp only [encodeId, ofId_ge large, Option.bind_none]

end VG.Proof.RsaPkcs1Sig.X86
