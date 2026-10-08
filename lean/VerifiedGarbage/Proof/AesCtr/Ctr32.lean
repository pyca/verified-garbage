import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesSiv.Ctr32

/-!
# AES-CTR from `vg_aes_ctr32`

Untrusted: everything here is checked by Lean, and nothing depends on a
target. `vg_aes_ctr32` increments only the last 32 bits of its counter block
(`inc₃₂`). Over `k` blocks from a counter block `t` whose last 32 bits,
`lo32 t`, do not wrap around before the last of them (`lo32 t + k ≤ 2³²`),
its counter blocks are CTR's (`counters_eq`): it gives CTR's output on them
(`ctr32_crypt`). It leaves `t + k` (`ctr32_next`), unless the last 32 bits
wrapped around to 0 (`lo32 t + k = 2³²`), when it leaves `t + k − 2³²`
(`ctr32_wrap`), from which a carry into the first 96 bits gives `t + k`.
CTR on blocks split in two is CTR on each, the second from where the first
left the counter (`crypt_append`).
-/

namespace VG.Proof.AesCtr

open VG Spec.Ctr
open VG.Spec.Aes (bytesAt)

/-- The last 32 bits of a counter block, as a big-endian integer. -/
def lo32 (t : List Byte) : Nat := toNat t % 2 ^ 32

theorem toNat_lt {t : List Byte} (ht : t.length = 16) : toNat t < 2 ^ 128 := by
  have := Proof.AesCcm.beVal_lt t
  rw [ht] at this
  show Proof.AesCcm.beVal t < 2 ^ 128
  simpa using this

theorem ofNat_toNat {t : List Byte} (ht : t.length = 16) : ofNat (toNat t) 16 = t := by
  have h := Proof.AesSiv.toBytes_be128 (Spec.Siv.beNat t)
  show Spec.Siv.be128 (Spec.Siv.beNat t) = t
  rw [← h, ← Proof.AesSiv.beNat_eq]
  exact Proof.Cmac.toBytes_ofBytes ht

/-- The counter block after `k` increments: `t + k`, modulo `2¹²⁸`. -/
theorem next_eq {t : List Byte} (ht : t.length = 16) : ∀ k, next t k = ofNat (toNat t + k) 16
  | 0 => (ofNat_toNat ht).symm
  | k + 1 => by
    rw [next_succ, next_eq ht k, inc, toNat_ofNat]
    exact ofNat_congr (by rw [Nat.mod_add_mod, Nat.add_assoc])

theorem counters_add (t : List Byte) : ∀ a b, counters t (a + b) = counters t a ++ counters (next t a) b
  | 0, b => by simp only [Nat.zero_add, counters, List.nil_append]; rfl
  | a + 1, b => by
    rw [Nat.add_right_comm, counters, counters_add (inc t) a b, counters, next_succ']
    rfl

/-- CTR on `xs ++ ys`: on `xs`, then on `ys` from the counter block `xs`
left. -/
theorem crypt_append (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs ys : List (List Byte)) :
    crypt ciph t (xs ++ ys) = crypt ciph t xs ++ crypt ciph (next t xs.length) ys := by
  simp only [crypt, List.length_append, counters_add, List.map_append]
  exact List.zipWith_append (by simp [length_counters])

theorem counters_eq_map (t : List Byte) : ∀ n, counters t n = (List.range n).map (next t)
  | 0 => rfl
  | n + 1 => by rw [counters_succ, counters_eq_map t n, List.range_succ, List.map_append]; rfl

/-- `inc₃₂`'s counter blocks are CTR's while the last 32 bits do not wrap
around. -/
theorem counters_eq {t : List Byte} (ht : t.length = 16) {k : Nat} (hk : lo32 t + k ≤ 2 ^ 32) {i : Nat}
    (hi : i < k) :
    Spec.Gcm.toBytes (Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes t)) = next t i := by
  rw [Proof.AesSiv.repeat_inc32 ht hk i hi, Proof.Cmac.toBytes_ofBytes (Proof.AesSiv.length_be128 _),
    next_eq ht]
  rfl

/-- `vg_aes_ctr32` over `k` blocks from a counter block whose last 32 bits
do not wrap around before the last: CTR's output on them. -/
theorem ctr32_crypt {m m' : Mem} {C D : Addr} {R : Nat} {w : List Byte} {k : Nat}
    (hk : lo32 (bytesAt m C 16) + k ≤ 2 ^ 32)
    (hd : Spec.Gcm.blocksAt m' D k =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) (Spec.Gcm.blockAt m C) (Spec.Gcm.blocksAt m D k)) :
    Spec.Cbc.blocksAt m' D k = crypt (Spec.Cbc.aesWith R w) (bytesAt m C 16) (Spec.Cbc.blocksAt m D k) := by
  have ht : (bytesAt m C 16).length = 16 := Proof.Cmac.bytesAt_length _ _ _
  have e : ∀ m'', Spec.Cbc.blocksAt m'' D k = (Spec.Gcm.blocksAt m'' D k).map Spec.Gcm.toBytes := fun m'' => by
    simp only [Spec.Cbc.blocksAt, Spec.Gcm.blocksAt, List.map_map]
    exact List.map_congr_left fun _ _ => Proof.Cmac.bytesAt_blockAt _ _
  rw [e, e, hd]
  apply List.ext_getElem (by simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, crypt, length_counters, Spec.Gcm.blocksAt])
  intro i h₁ h₂
  have hi : i < k := by simpa [Spec.Gcm.ctr32, Spec.Gcm.keystream, Spec.Gcm.blocksAt] using h₁
  simp only [Spec.Gcm.ctr32, Spec.Gcm.keystream, crypt, List.getElem_map, List.getElem_zipWith, List.getElem_range,
    counters_eq_map, List.length_map, Spec.Gcm.blocksAt]
  rw [← counters_eq ht hk hi, show Spec.Cbc.aesWith R w = Spec.Cmac.aesWith R w from rfl,
    ← Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.toBytes_length _), Proof.Cmac.ofBytes_toBytes]
  refine Proof.Gcm.list_ext (by simp [Spec.Cbc.xor, Proof.Cmac.toBytes_length]) fun j hj => ?_
  simp only [Proof.Cmac.toBytes_length] at hj
  rw [Proof.Aes.toBytes_xor _ _ hj]
  simp [Spec.Cbc.xor, List.getD_eq_getElem?_getD, Proof.Cmac.toBytes_length, hj]
  rfl

/-- The counter block `vg_aes_ctr32` leaves after `k` blocks, when the last
32 bits do not wrap around: CTR's. -/
theorem ctr32_next {m m' : Mem} {C : Addr} {k : Nat} (hk : lo32 (bytesAt m C 16) + k < 2 ^ 32)
    (hc : Spec.Gcm.blockAt m' C = Nat.repeat Spec.Gcm.inc32 k (Spec.Gcm.blockAt m C)) :
    bytesAt m' C 16 = next (bytesAt m C 16) k := by
  rw [Proof.Cmac.bytesAt_blockAt, hc]
  exact counters_eq (Proof.Cmac.bytesAt_length _ _ _) (k := k + 1) (by omega) (by omega)

/-- The counter block `vg_aes_ctr32` leaves after `k` blocks, when the last
32 bits wrap around to 0 at the last: `t + k − 2³²`, which a carry into the
first 96 bits makes CTR's. -/
theorem ctr32_wrap {m m' : Mem} {C : Addr} {k : Nat} (hk : lo32 (bytesAt m C 16) + k = 2 ^ 32)
    (hc : Spec.Gcm.blockAt m' C = Nat.repeat Spec.Gcm.inc32 k (Spec.Gcm.blockAt m C)) :
    bytesAt m' C 16 = ofNat (toNat (bytesAt m C 16) + k - 2 ^ 32) 16 := by
  have ht := Proof.Cmac.bytesAt_length m C 16
  have hb := toNat_lt ht
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by unfold lo32 at hk; omega⟩
  have hj := Proof.AesSiv.repeat_inc32 ht (k := j + 1)
    (by change toNat (bytesAt m C 16) % 2 ^ 32 + (j + 1) ≤ 2 ^ 32; unfold lo32 at hk; omega) j (by omega)
  rw [Proof.Cmac.bytesAt_blockAt, hc, Nat.repeat, show Spec.Gcm.blockAt m C = Spec.Gcm.ofBytes (bytesAt m C 16)
    from rfl, hj, Proof.AesSiv.ofBytes_be128]
  have hl : (toNat (bytesAt m C 16) + j) % 2 ^ 32 + 1 = 2 ^ 32 := by unfold lo32 at hk; omega
  show _ = Spec.Siv.be128 _
  rw [← Proof.AesSiv.toBytes_be128]
  refine congrArg _ (BitVec.eq_of_toNat_eq ?_)
  rw [Proof.AesCcm.toNat_inc32, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show _ = (toNat (bytesAt m C 16) + (j + 1) - 2 ^ 32) % 2 ^ 128
  have e : Spec.Siv.beNat (bytesAt m C 16) = toNat (bytesAt m C 16) := rfl
  rw [e, Nat.mod_eq_of_lt (a := toNat (bytesAt m C 16) + j) (by unfold lo32 at hk; omega), hl, Nat.mod_self]
  omega

end VG.Proof.AesCtr
