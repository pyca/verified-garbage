module

public import VerifiedGarbage.Spec.HashFns
public import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Sha512.Md

/-!
# The streaming functions a hash function's number names

What the proofs of a function calling the streaming functions of a hash
function by its number (`Spec.HashFns.streaming`) need of them, for every
number that names one: the state's representation depends only on its bytes
(`ReprLocal`), the sizes are small, and the digest is the one `HashId.mgf1`
names (`streaming_ok`).
-/

@[expose] public section

namespace VG.Proof.HashFns

open Spec.HashFns (Streaming streaming)

/-- What the proofs need of a hash function's streaming functions, of the
hash function `H` as RSA's padding takes it. -/
structure StreamingOK (T : Streaming) (H : Spec.Mgf1.Hash) : Prop where
  local_ : Proof.Hmac.ReprLocal T.S
  state : T.S.stateBytes ≤ 256
  out : T.outBytes ≤ 64
  scratch : 8 * T.scratch ≤ 2048
  digest : T.S.digestBytes ≤ T.outBytes
  pos : 0 < T.S.digestBytes
  len : H.len = T.S.digestBytes
  hash : H.hash = T.S.H.hash
  valid : Proof.Mgf1.Valid H

theorem take_length {n : Nat} {xs : List Byte} (h : n ≤ xs.length) : (xs.take n).length = n := by
  rw [List.length_take]; omega

theorem streaming_ok {i : Nat} {T : Streaming} (h : streaming i = some T) :
    ∃ H, Spec.HashId.mgf1 i = some H ∧ StreamingOK T H := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals simp only [streaming, Option.some.injEq, reduceCtorEq] at h
  all_goals try subst h
  · exact ⟨_, rfl, ⟨Proof.Hmac.md5_local, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
      by decide, fun x => Proof.Md5.md.digest_length _⟩⟩
  · exact ⟨_, rfl, ⟨Proof.Hmac.sha1_local, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
      by decide, fun x => Proof.Sha1.md.digest_length _⟩⟩
  · exact ⟨_, rfl, ⟨Proof.Hmac.sha224_local, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
      by decide, fun x => take_length (by
        have : (Spec.Sha256.finalHash Spec.Sha256.H0_224 x).length = 32 := Proof.Sha256.md.digest_length _
        omega)⟩⟩
  · exact ⟨_, rfl, ⟨Proof.Hmac.sha256_local, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
      by decide, fun x => Proof.Sha256.md.digest_length _⟩⟩
  · exact ⟨_, rfl, ⟨Proof.Hmac.sha384_local, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
      by decide, fun x => take_length (by
        rw [Proof.Sha512.finalHash_eq]
        have := Proof.Sha512.md.digest_length
        simp only [MdStream.Md.hash, this]; decide)⟩⟩
  · exact ⟨_, rfl, ⟨Proof.Hmac.sha512_local, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
      by decide, fun x => Proof.Sha512.md.digest_length _⟩⟩
  · exact ⟨_, rfl, ⟨Proof.Hmac.sha512_224_local, by decide, by decide, by decide, by decide, by decide, rfl,
      rfl, by decide, fun x => take_length (by
        rw [Proof.Sha512.finalHash_eq]
        have := Proof.Sha512.md.digest_length
        simp only [MdStream.Md.hash, this]; decide)⟩⟩
  · exact ⟨_, rfl, ⟨Proof.Hmac.sha512_256_local, by decide, by decide, by decide, by decide, by decide, rfl,
      rfl, by decide, fun x => take_length (by
        rw [Proof.Sha512.finalHash_eq]
        have := Proof.Sha512.md.digest_length
        simp only [MdStream.Md.hash, this]; decide)⟩⟩

end VG.Proof.HashFns
