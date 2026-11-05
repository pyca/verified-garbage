module

public import VerifiedGarbage.Spec.Sha3

/-!
# SHA-3 and SHAKE: the length of the output

**Trusted** (as every file in `Spec/`), though it defines nothing: that
`SHA3-256` gives 32 bytes and `SHAKE256(M, d)` gives `d`, which the
statements about where a key holds a hash (`MlKem/KeyGenH.lean`,
`MlDsa/KeyGenTr.lean`) need.
-/

@[expose] public section

namespace VG.Spec.Sha3

theorem flatMap_lanes_length (L : List Lane) :
    (L.flatMap fun a => (List.range 8).map fun k => a.extractLsb' (8 * k) 8).length =
      8 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
      List.length_cons]
    omega

theorem toBytes_length (A : State) : (toBytes A).length = 200 := by
  rw [toBytes, flatMap_lanes_length, Vector.length_toList]

theorem squeezeBlocks_length {rate : Nat} (hr : rate ≤ 200) :
    ∀ (n : Nat) (S : State), (squeezeBlocks rate S n).length = rate * n
  | 0, _ => rfl
  | n + 1, S => by
    simp only [squeezeBlocks, List.length_append, List.length_take, toBytes_length,
      squeezeBlocks_length hr n]
    rw [Nat.mul_succ]
    omega

theorem squeeze_length {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) (d : Nat) :
    (squeeze rate S d).length = d := by
  rw [squeeze, List.length_take, squeezeBlocks_length hr']
  have h1 := Nat.div_add_mod (d + rate - 1) rate
  have h2 := Nat.mod_lt (d + rate - 1) hr
  omega

theorem sha3_256_length (m : List Byte) : (sha3_256 m).length = 32 :=
  squeeze_length (by decide) (by decide) _ _

theorem shake256_length (m : List Byte) (d : Nat) : (shake256 m d).length = d :=
  squeeze_length (by decide) (by decide) _ _

end VG.Spec.Sha3
