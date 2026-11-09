module

public import VerifiedGarbage.Spec.MlKem
public import VerifiedGarbage.Spec.Sha3.Length

/-!
# ML-KEM: the decapsulation key holds `H(ek)`

**Trusted** (as every file in `Spec/`), though it defines nothing.
`vg_mlkem*_encaps_h` (`EncapsH.lean`) requires its 32 bytes `h` to be
`H(ek)`. After `vg_mlkem*_keygen`, the Rust takes `h` from the decapsulation
key `dk = dk_PKE ‖ ek ‖ H(ek) ‖ z` (FIPS 203 Algorithm 16), as its bytes
`dk.len() - 64 … dk.len() - 32`, rather than hashing `ek` again:
`keyGenInternal_h` states that those bytes are `H(ek)` for every key that
`ML-KEM.KeyGen_internal(d, z)` gives with a 32-byte `z`, which the seed
`d ‖ z` of `keyGenContract` has.
-/

@[expose] public section

namespace VG.Spec.MlKem

theorem keyGenInternal_h {p : Params} {iters : Nat} {d z ek dk : List Byte}
    (h : keyGenInternal p iters d z = some (ek, dk)) (hz : z.length = 32) :
    (dk.drop (dk.length - 64)).take 32 = H ek := by
  cases hk : kpkeKeyGen p iters d with
  | none => simp [keyGenInternal, hk] at h
  | some kp =>
    obtain ⟨ekPKE, dkPKE⟩ := kp
    simp only [keyGenInternal, hk, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hH : (H ekPKE).length = 32 := Sha3.sha3_256_length _
    have e : dkPKE ++ ekPKE ++ H ekPKE ++ z = (dkPKE ++ ekPKE) ++ (H ekPKE ++ z) := by
      simp only [List.append_assoc]
    have hl : (H ekPKE ++ z).length = 64 := by rw [List.length_append, hH, hz]
    rw [e, List.length_append (as := dkPKE ++ ekPKE), hl, Nat.add_sub_cancel, List.drop_left,
      List.take_left' hH]

end VG.Spec.MlKem
