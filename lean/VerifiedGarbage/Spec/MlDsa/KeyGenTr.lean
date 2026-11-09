module

public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Spec.Sha3.Length

/-!
# ML-DSA: the private key holds `tr`

**Trusted** (as every file in `Spec/`), though it defines nothing.
`vg_mldsa*_verify_message_cached` (`CachedVerify.lean`) requires its 64 bytes
`tr` to be `pkTr pk`, `H(pk, 64)`. After `vg_mldsa*_keygen`, the Rust takes
`tr` from the private key, as its bytes `64 … 128` (`skTr`, where
`skDecode` finds it, FIPS 204 Algorithm 25), rather than hashing `pk` again:
`keyGenInternal_tr` states that those bytes are `pkTr pk` for every key pair
that `ML-DSA.KeyGen_internal(ξ)` (Algorithm 6) gives.
-/

@[expose] public section

namespace VG.Spec.MlDsa

theorem keyGenInternal_tr {p : Params} {b : Bounds} {ξ pk sk : List Byte}
    (h : keyGenInternal p b ξ = some (pk, sk)) : skTr sk = pkTr pk := by
  have hl : (H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128).length = 128 :=
    Sha3.shake256_length _ _
  unfold keyGenInternal at h
  generalize H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128 = hξ at h hl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨_, _, _, _, rfl, rfl⟩ := h
  have hρ : (hξ.take 32).length = 32 := by rw [List.length_take, hl]; rfl
  have hK : ((hξ.drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hl]; rfl
  simp only [skTr, pkTr, skEncode, List.append_assoc]
  rw [← List.append_assoc (hξ.take 32),
    List.drop_left' (by rw [List.length_append, hρ, hK]),
    List.take_left' (show (H _ 64).length = 64 from Sha3.shake256_length _ _)]

end VG.Spec.MlDsa
