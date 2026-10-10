import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Counter
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

/-- CTR on `xs ++ ys`: on `xs`, then on `ys` from the counter block `xs`
left. -/
theorem crypt_append (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs ys : List (List Byte)) :
    crypt ciph t (xs ++ ys) = crypt ciph t xs ++ crypt ciph (next t xs.length) ys := by
  simp only [crypt, List.length_append, counters_add, List.map_append]
  exact List.zipWith_append (by simp [length_counters])

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

/-- The block at `P` plus `d` as two 64-bit words: the reversed words
`rv64 hi` at `P` and `rv64 lo` at `P + 8`, with `lo` the low word plus `d`
and `hi` the high word plus the carry. -/
theorem add_words64 (m : Mem) (P : Addr) (hi lo : BitVec 64) (d : Nat)
    (hlo : lo.toNat = ((rv64 (m.readW (P + BitVec.ofNat 64 8) 64)).toNat + d) % 2 ^ 64)
    (hhi : hi.toNat = ((rv64 (m.readW P 64)).toNat +
      ((rv64 (m.readW (P + BitVec.ofNat 64 8) 64)).toNat + d) / 2 ^ 64) % 2 ^ 64) :
    bytesAt ((m.writeW (P + BitVec.ofNat 64 8) (rv64 lo)).writeW P (rv64 hi)) P 16 =
      ofNat (toNat (bytesAt m P 16) + d) 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, bytesAt_append, bytesAt_append m, bytesAt_writeW_rv64,
    bytesAt_writeW_sep _ _ _ (by decide) (by decide), bytesAt_writeW_rv64,
    show 8 + 8 = (bytesAt m P 8).length + (bytesAt m (P + BitVec.ofNat 64 8) 8).length by simp [bytesAt],
    ofNat_toNat_append_add, bytesAt_rv64 m P, bytesAt_rv64 m (P + BitVec.ofNat 64 8), toNat_ofNat, toNat_ofNat,
    length_ofNat, length_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (BitVec.isLt _)]
  congr 1
  · exact ofNat_congr (by rw [hhi]; simp only [Nat.reducePow]; omega)
  · exact ofNat_congr (by rw [hlo]; simp only [Nat.reducePow]; omega)

theorem blocksAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Cbc.blocksAt m p (a + b) = Spec.Cbc.blocksAt m p a ++ Spec.Cbc.blocksAt m (p + BitVec.ofNat 64 (16 * a)) b := by
  simp only [Spec.Cbc.blocksAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add]

/-- The last 32 bits of the counter block after `k` increments. -/
theorem lo32_next {t : List Byte} (ht : t.length = 16) (k : Nat) : lo32 (next t k) = (toNat t + k) % 2 ^ 32 := by
  rw [lo32, next_eq ht, toNat_ofNat]
  omega

theorem blocksAt_take (m : Mem) (p : Addr) {n k : Nat} (hk : k ≤ n) :
    (Spec.Cbc.blocksAt m p n).take k = Spec.Cbc.blocksAt m p k := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [blocksAt_add, List.take_left' (Proof.AesCbc.length_blocksAt _ _ _)]

theorem blocksAt_drop (m : Mem) (p : Addr) {n k : Nat} (hk : k ≤ n) :
    (Spec.Cbc.blocksAt m p n).drop k = Spec.Cbc.blocksAt m (p + BitVec.ofNat 64 (16 * k)) (n - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [blocksAt_add, List.drop_left' (Proof.AesCbc.length_blocksAt _ _ _), Nat.add_sub_cancel_left]

/-- The blocks after a frame outside them. -/
theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ j < n, ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  simp only [Spec.Cbc.blocksAt]
  exact List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf (hd j (List.mem_range.mp hj)) (by decide)

/-- CTR's output on the first `k + m` blocks, from that on the first `k`, on
the next `m` from the counter block the first `k` leave, and the rest. -/
theorem crypt_step (ciph : Spec.Cbc.Cipher) (t : List Byte) (ys : List (List Byte)) {k m : Nat}
    (hl : k + m ≤ ys.length) :
    crypt ciph t (ys.take k) ++ crypt ciph (next t k) ((ys.drop k).take m) ++ ys.drop (k + m) =
      crypt ciph t (ys.take (k + m)) ++ ys.drop (k + m) := by
  rw [List.take_add, crypt_append, List.length_take, Nat.min_eq_left (by omega)]

theorem next_add (t : List Byte) (a : Nat) : ∀ b, next t (a + b) = next (next t a) b
  | 0 => rfl
  | b + 1 => by rw [← Nat.add_assoc, next_succ, next_add t a b, next_succ]

/-- The counter block after a wrap and the carry: CTR's. -/
theorem carry_next {t : List Byte} (ht : t.length = 16) {k m : Nat} (hw : lo32 (next t k) + m = 2 ^ 32) :
    ofNat (toNat (ofNat (toNat (next t k) + m - 2 ^ 32) 16) + 2 ^ 32) 16 = next t (k + m) := by
  have hn : (next t k).length = 16 := by rw [next_eq ht]; exact length_ofNat _ _
  have hb := toNat_lt hn
  rw [toNat_ofNat, next_add, next_eq hn]
  apply ofNat_congr
  unfold lo32 at hw
  have : 2 ^ 32 ≤ toNat (next t k) + m := by omega
  rw [Nat.mod_eq_of_lt (a := toNat (next t k) + m - 2 ^ 32) (by omega), Nat.sub_add_cancel this]

/-- The blocks split in three: the first `a`, the next `b`, and the rest. -/
theorem blocksAt_three (m : Mem) (p : Addr) {n a b : Nat} (h : a + b ≤ n) :
    Spec.Cbc.blocksAt m p n = Spec.Cbc.blocksAt m p a ++ Spec.Cbc.blocksAt m (p + BitVec.ofNat 64 (16 * a)) b ++
      Spec.Cbc.blocksAt m (p + BitVec.ofNat 64 (16 * (a + b))) (n - (a + b)) := by
  obtain ⟨c, rfl⟩ : ∃ c, n = a + b + c := ⟨n - (a + b), by omega⟩
  rw [blocksAt_add m p (a + b) c, blocksAt_add m p a b, Nat.add_sub_cancel_left]

/-- A 32-bit word is zero when its bytes reversed are. -/
theorem rv32_eq_zero {a : BitVec 32} : rv32 a = 0 ↔ a = 0 := by
  have ha := a.isLt
  have hr := (rv32 a).isLt
  have d0 := rv32_digit a (i := 0) (by decide)
  have d1 := rv32_digit a (i := 1) (by decide)
  have d2 := rv32_digit a (i := 2) (by decide)
  have d3 := rv32_digit a (i := 3) (by decide)
  simp only [Nat.reduceSub, Nat.reducePow, Nat.pow_zero, Nat.div_one] at d0 d1 d2 d3 ha hr
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [h] at d0 d1 d2 d3
    simp at d0 d1 d2 d3 ⊢
    omega
  · rintro rfl
    decide

theorem toNat_eq_of_map {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : toNat a = toNat b := by
  have e : ∀ l : List Byte, toNat l = (l.map (·.toNat)).foldl (fun acc x => 256 * acc + x) 0 := fun l => by
    simp only [toNat, List.foldl_map]
  rw [e, e, h]

/-- Counter blocks whose last four bytes (`Spec.Ctr.ctrLeak`) agree agree in
their last 32 bits. -/
theorem lo32_of_leak {t t' : List Byte} (ht : t.length = 16) (ht' : t'.length = 16)
    (h : (t.drop 12).map (·.toNat) = (t'.drop 12).map (·.toNat)) : lo32 t = lo32 t' := by
  have split : ∀ u : List Byte, u.length = 16 → lo32 u = toNat (u.drop 12) := fun u hu => by
    have hb : toNat (u.drop 12) < 2 ^ 32 := by
      have := Proof.AesCcm.beVal_lt (u.drop 12)
      rw [List.length_drop, hu] at this
      show Proof.AesCcm.beVal (u.drop 12) < 2 ^ 32
      simpa using this
    rw [lo32]
    conv => lhs; rw [← List.take_append_drop 12 u]
    rw [toNat_append, List.length_drop, hu]
    simp only [Nat.reduceSub, Nat.reducePow] at hb ⊢
    omega
  rw [split t ht, split t' ht', toNat_eq_of_map h]

/-- The last 32 bits of the counter block at `Q`, as read and byte-reversed. -/
theorem lo32_bytesAt (m : Mem) (Q : Addr) :
    lo32 (bytesAt m Q 16) = (rv32 (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat := by
  rw [lo32, show (16 : Nat) = 12 + 4 from rfl, bytesAt_append, toNat_append,
    bytesAt_rv32, toNat_ofNat, length_ofNat]
  have := (rv32 (m.readW (Q + BitVec.ofNat 64 12) 32)).isLt
  simp only [Nat.reducePow] at this ⊢
  omega

theorem sub32_toNat (c : BitVec 32) : (0x100000000 - c.setWidth 64 : BitVec 64).toNat = 2 ^ 32 - c.toNat := by
  have hc := c.isLt
  have h1 : (c.setWidth 64).toNat = c.toNat := by simp [BitVec.toNat_setWidth]; omega
  have h2 : (0x100000000 : BitVec 64).toNat = 2 ^ 32 := rfl
  rw [BitVec.toNat_sub, h1, h2]
  omega

end VG.Proof.AesCtr
