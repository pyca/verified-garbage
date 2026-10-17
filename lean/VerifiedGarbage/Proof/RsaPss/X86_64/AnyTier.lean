module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySafe
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.Spec.RsaPss.AnyHash

/-!
# RSASSA-PSS with the hash functions as arguments on x86-64: a tier's hash functions

The code of a tier's hash functions, by number (`tierHashes`), and what
signing and verification need of them: their number, that the `i`th is the
one `HashId.mgf1 i` names, and their proofs (`tier_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink Tier MdHash)

/-! ## The tier's hash functions -/

/-- The code of a tier's hash functions, by number. -/
def tierHashes (t : Tier) : List Hash := t.hashes.map (·.H)

theorem tier_length (t : Tier) : t.hashes.length = 8 := by
  have := congrArg List.length t.mgf_ok
  simpa using this

theorem tierHashes_length (t : Tier) : (tierHashes t).length = 8 := by
  rw [tierHashes, List.length_map, tier_length]

theorem tierHashes_get (t : Tier) {i : Nat} (hi : i < (tierHashes t).length) :
    (tierHashes t)[i] = (t.hashes[i]'(by rw [tierHashes, List.length_map] at hi; exact hi)).H := by
  simp [tierHashes]

theorem tier_mgf1 (t : Tier) {i : Nat} (hi : i < t.hashes.length) :
    Spec.HashId.mgf1 i = some (t.hashes[i]).mgf.G := by
  have := congrArg (·[i]?) t.mgf_ok
  have h8 : i < 8 := by rw [tier_length] at hi; exact hi
  simp only [List.getElem?_map, List.getElem?_range h8, List.getElem?_eq_getElem hi, Option.map_some,
    Option.some.injEq] at this
  exact this.symm

theorem tier_ok (t : Tier) : TierOk (tierHashes t) := fun h hh => by
  simp only [tierHashes, List.mem_map] at hh
  obtain ⟨v, -, rfl⟩ := hh
  exact ⟨⟨v.ok⟩, v.K⟩

theorem sel_lt {x : Nat} (h : x ∈ Spec.RsaPss.hashIds) : x < 8 := by
  simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at h; omega

end VG.Proof.RsaPss.X86_64.Any
