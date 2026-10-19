module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA's operands in memory, on any target

Bytes apart from every range that changed are kept (`outs_bytes`); a range
that changed at an address `base + out` changed at offset `out` of `base`
(`outside_rebase`); a number whose top words are zero is its low words
(`val32_prefix_of_lt`), as an exponent of `len` bytes is in its
`⌈len / 4⌉` words (`decoded_exponent_fits`).
-/

@[expose] public section

namespace VG.Proof.Dsa

open VG VG.Proof.Mont

theorem outs_bytes {m m' : Mem} {base p : Addr} {len : Nat} {ranges : List (Nat × Nat)}
    (O : Outs base ranges m m') (hl : len ≤ 2 ^ 64)
    (hb : ∀ r ∈ ranges, r.1 + r.2 ≤ 2 ^ 64)
    (apart : ∀ r ∈ ranges, Region.Disjoint ⟨p, len⟩ ⟨off base r.1, r.2⟩) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have hilt := List.mem_range.mp hi
  apply O _
  intro r hr
  have inside : (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base p (by omega) (by omega)
  have outside := apart r hr _ inside
  have H := Offset.lt_iff (p + BitVec.ofNat 64 i) base (hb r hr)
  change ¬ ((p + BitVec.ofNat 64 i - off base r.1).toNat + 1 ≤ r.2) at outside
  change (p + BitVec.ofNat 64 i - off base r.1).toNat < r.2 ↔
    r.1 ≤ ofs base (p + BitVec.ofNat 64 i) ∧ ofs base (p + BitVec.ofNat 64 i) < r.1 + r.2 at H
  omega

theorem outside_rebase {base : Addr} {out len : Nat} {m m' : Mem}
    (h : Outside (off base out) 0 len m m') (hb : out + len ≤ 2 ^ 64) :
    Outside base out len m m' := by
  intro x hx
  apply h x
  have H := Offset.lt_iff x base hb
  change ofs (off base out) x < len ↔ out ≤ ofs base x ∧ ofs base x < out + len at H
  right
  simp only [Nat.zero_add]
  omega

theorem val32_prefix_of_lt {mem : Mem} {base : Addr} {d k n : Nat} (hk : k ≤ n)
    (hlt : val32 mem base d n < 2 ^ (32 * k)) : val32 mem base d k = val32 mem base d n := by
  have H := val32_append mem base d k (n - k)
  rw [Nat.add_sub_of_le hk] at H
  have Hm := congrArg (fun v => v % 2 ^ (32 * k)) H
  rw [Nat.mod_eq_of_lt hlt, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
    Nat.mod_mod, Nat.mod_eq_of_lt (val32_lt mem base d k)] at Hm
  exact Hm.symm

theorem decoded_exponent_fits (mem : Mem) (p : Addr) (len : Nat) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem p len) < 2 ^ (32 * ((len + 3) / 4)) := by
  have H := decodeBE_lt (Spec.Rsa.bytesAt mem p len)
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at H
  have E : 256 ^ len = 2 ^ (8 * len) := by rw [Nat.pow_mul]
  rw [E] at H
  exact Nat.lt_of_lt_of_le H (Nat.pow_le_pow_right (by decide) (by omega))

end VG.Proof.Dsa
