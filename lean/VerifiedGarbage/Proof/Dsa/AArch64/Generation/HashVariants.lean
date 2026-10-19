module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-! # Select the SHA-1 and SHA-256 stream implementations for DSA generation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Pbkdf2.Md.AArch64

theorem sha1_of_name (v : MdHash) (h : v.mgf.G.rust = "sha1") : v.mgf.G = Spec.Mgf1.sha1 := by
  have hm := v.mgf.mem
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  all_goals rw [hm] at h
  all_goals first | exact hm | contradiction

theorem sha256_of_name (v : MdHash) (h : v.mgf.G.rust = "sha256") : v.mgf.G = Spec.Mgf1.sha256 := by
  have hm := v.mgf.mem
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  all_goals rw [hm] at h
  all_goals first | exact hm | contradiction

theorem hashCode_size (v : MdHash) (x : List (BitVec 8)) : (v.mgf.G.hash x).length = v.H.D := by
  rw [v.mgf.hash, v.ok.hash, List.length_take, MdStream.Md.hash, v.ok.md.digest_length]
  exact Nat.min_eq_left v.ok.sizes.DN

def generationHashes (v1 v256 : MdHash) (h1 : v1.mgf.G.rust = "sha1")
    (h256 : v256.mgf.G.rust = "sha256") : GenerationHashes where
  sha1 := v1.H
  sha256 := v256.H
  h1 := v1.ok.stream
  h256 := v256.ok.stream
  hash1 x := by rw [← sha1_of_name v1 h1]; exact v1.mgf.hash x
  hash256 x := by rw [← sha256_of_name v256 h256]; exact v256.mgf.hash x
  size1 x := by rw [← sha1_of_name v1 h1]; exact hashCode_size v1 x
  size256 x := by rw [← sha256_of_name v256 h256]; exact hashCode_size v256 x
  width1 := by
    change v1.H.D = 20
    rw [← v1.mgf.len, sha1_of_name v1 h1]
    rfl
  width256 := by
    change v256.H.D = 32
    rw [← v256.mgf.len, sha256_of_name v256 h256]
    rfl

end VG.Proof.Dsa.AArch64.Generation
