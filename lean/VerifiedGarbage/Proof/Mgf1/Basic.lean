import VerifiedGarbage.Spec.Mgf1

/-!
# MGF1: lengths and masking

A hash function whose digests are `hLen > 0` octets (`Valid`) makes
masks of the length asked for (`mgf1_length`), and masking twice with the
same mask gives the octets back (`xorBytes_xorBytes`).
-/

namespace VG.Proof.Mgf1

open Spec Spec.Mgf1

/-- `H`'s digests are `hLen > 0` octets. -/
def Valid (H : Hash) : Prop := 0 < H.len ∧ ∀ x, (H.hash x).length = H.len

theorem xorBytes_length (a b : List Byte) : (xorBytes a b).length = min a.length b.length :=
  List.length_zipWith

theorem xorBytes_xorBytes : ∀ {a b : List Byte}, a.length ≤ b.length →
    xorBytes (xorBytes a b) b = a
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [xorBytes, List.zipWith_cons_cons, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, List.cons.injEq, true_and]
    exact xorBytes_xorBytes (by simpa using h)

theorem mgf1_length {H : Hash} (hH : Valid H) (seed : List Byte) (maskLen : Nat) :
    (mgf1 H seed maskLen).length = maskLen := by
  obtain ⟨hpos, hlen⟩ := hH
  have hl : ((List.range ((maskLen + H.len - 1) / H.len)).flatMap fun c =>
      H.hash (seed ++ Rsa.i2osp c 4)).length = H.len * ((maskLen + H.len - 1) / H.len) := by
    rw [List.length_flatMap]
    simp only [hlen, List.map_const', List.length_range, List.sum_replicate_nat, Nat.mul_comm]
  have hd := Nat.div_add_mod (maskLen + H.len - 1) H.len
  have hm := Nat.mod_lt (maskLen + H.len - 1) hpos
  simp only [mgf1, List.length_take, hl]
  omega

end VG.Proof.Mgf1
