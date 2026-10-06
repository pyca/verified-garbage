import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# Multiword arithmetic: octets, words and the RSA specification

Target-independent facts that relate the numbers in the working space to
the octet strings and word lists of the specification (`Spec/Rsa.lean`):
`os2ip` and `modulusValid` of a modulus' bytes (`modulusValid_iff`), the
precomputed values (`publicPrecompute_some`, `pre_of_some`), and the
results the public-key operation writes (`written_of`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum VG.Impl.Bignum.Public

/-! ## Octet strings and the modulus -/

theorem os2ip_foldl (a : Nat) (bs : List Byte) :
    bs.foldl (fun x b => 256 * x + b.toNat) a = a * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
  induction bs generalizing a with
  | nil => simp [Spec.Rsa.os2ip]
  | cons b bs ih =>
    show bs.foldl _ (256 * a + b.toNat) = a * 256 ^ (bs.length + 1) + bs.foldl _ (256 * 0 + b.toNat)
    rw [ih, ih (256 * 0 + b.toNat), Nat.pow_succ, Nat.add_mul, Nat.mul_zero, Nat.zero_add, Nat.mul_assoc,
      Nat.mul_comm (256 ^ bs.length) 256, Nat.add_assoc, Nat.mul_left_comm]

theorem os2ip_cons (b : Byte) (bs : List Byte) :
    Spec.Rsa.os2ip (b :: bs) = b.toNat * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
  show List.foldl (fun x (b : Byte) => 256 * x + b.toNat) (256 * 0 + b.toNat) bs = _
  rw [os2ip_foldl, Nat.mul_zero, Nat.zero_add]

theorem os2ip_lt (bs : List Byte) : Spec.Rsa.os2ip bs < 256 ^ bs.length := by
  rw [← pre_len]; exact pre_lt bs (Nat.le_refl _)

theorem pow256_eq (a : Nat) : (256 : Nat) ^ a = 2 ^ (8 * a) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

theorem pow256_64 : (256 : Nat) ^ 64 = 2 ^ 512 := by
  simpa only [Nat.reduceMul] using pow256_eq 64

theorem modulusValid_nat {n0 r l P k : Nat} (hn0 : n0 < 256) (hr : r < P) (hP : P = 256 ^ (k - 1))
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hodd : (n0 * P + r) % 2 = l % 2) :
    Spec.Rsa.modulusValid (n0 * P + r) k =
      !(decide (n0 < 1) || decide (l % 2 < 1) || decide ((k - 64) * 256 + n0 < 128)) := by
  unfold Spec.Rsa.modulusValid
  by_cases h0 : n0 = 0
  · subst h0
    simp only [Nat.zero_mul, Nat.zero_add, ← hP, show ¬ P ≤ r by omega, decide_false, Bool.and_false,
      show (0 < 1) = True from propext ⟨fun _ => trivial, fun _ => by decide⟩, decide_true, Bool.true_or,
      Bool.not_true]
  have hge : P ≤ n0 * P + r := Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (by omega))
  have hlt : n0 * P + r < 2 ^ 8192 := by
    have h1 : n0 * P + r < 256 * P := by
      have := Nat.mul_le_mul_right P (show n0 + 1 ≤ 256 by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega
    have h2 : 256 * P = 2 ^ (8 * k) := by
      rw [hP, ← pow256_eq, ← Nat.pow_succ']; congr 1; omega
    have h3 := (fun B (hB : 8 * k ≤ B) => Nat.pow_le_pow_right (n := 2) (by decide) hB) 8192 (by omega)
    omega
  have h511 : decide (2 ^ 511 ≤ n0 * P + r) = !decide ((k - 64) * 256 + n0 < 128) := by
    by_cases hk64 : k = 64
    · subst hk64
      have hP' : P = 2 ^ 504 := by
        simpa only [Nat.reduceSub, Nat.reduceMul] using hP.trans (pow256_eq _)
      rw [hP'] at hr ⊢
      rw [show (64 - 64) * 256 + n0 = n0 by omega]
      by_cases h128 : 128 ≤ n0
      · simp only [show 2 ^ 511 ≤ n0 * 2 ^ 504 + r by omega, show ¬ n0 < 128 by omega, decide_true,
          decide_false, Bool.not_false]
      · simp only [show ¬ 2 ^ 511 ≤ n0 * 2 ^ 504 + r by omega, show n0 < 128 by omega, decide_true,
          decide_false, Bool.not_true]
    · have hP' : 2 ^ 512 ≤ P := by
        rw [hP, ← pow256_64]; exact Nat.pow_le_pow_right (by decide) (by omega)
      simp only [show 2 ^ 511 ≤ n0 * P + r by omega, show ¬ (k - 64) * 256 + n0 < 128 by omega, decide_true,
        decide_false, Bool.not_false]
  rw [← hP]
  simp only [h511, show P ≤ n0 * P + r from hge, show n0 * P + r < 2 ^ 8192 from hlt, show ¬ n0 < 1 by omega,
    decide_true, decide_false, Bool.and_true, Bool.false_or, Bool.not_or]
  by_cases hl : l % 2 = 1
  · simp [hl, hodd]
  · simp [show l % 2 = 0 by omega, hodd]

/-- `m` is a valid modulus iff its first byte is not zero, its last byte is
odd, and `256 (k - 64) + m[0] ≥ 128`, for `64 ≤ k ≤ 1024`. -/
theorem modulusValid_iff {nb : List Byte} {k : Nat} (hlen : nb.length = k) (hk : 64 ≤ k) (hk' : k ≤ 1024) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k =
      !(decide ((nb[0]'(by omega)).toNat < 1) || decide ((nb[k - 1]'(by omega)).toNat % 2 < 1) ||
        decide ((k - 64) * 256 + (nb[0]'(by omega)).toNat < 128)) := by
  have hodd : Spec.Rsa.os2ip nb % 2 = (nb[k - 1]'(by omega)).toNat % 2 := by
    have := pre_succ nb (i := k - 1) (by omega)
    rw [show k - 1 + 1 = nb.length by omega, pre_len] at this
    omega
  obtain ⟨b, bs, rfl⟩ : ∃ b bs, nb = b :: bs := by
    cases nb with
    | nil => simp at hlen; omega
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hl : bs.length = k - 1 := by simp at hlen; omega
  rw [os2ip_cons, hl] at hodd ⊢
  have hr := os2ip_lt bs
  rw [hl] at hr
  exact modulusValid_nat b.isLt hr rfl hk hk' hodd

theorem i2osp_zero (k : Nat) : Spec.Rsa.i2osp 0 k = (List.range k).map fun _ => 0 := by
  unfold Spec.Rsa.i2osp
  simp

/-- What a valid modulus gives: odd, above 1, its top word not zero. -/
theorem valid_facts {N k : Nat} (hv : Spec.Rsa.modulusValid N k = true) (hk : 64 ≤ k) :
    N % 2 = 1 ∧ 1 < N ∧ 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ N := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hv
  have h4 := of_decide_eq_true h4
  have hp : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ 256 ^ (k - 1) := by
    rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have h256 : 256 ≤ 256 ^ (k - 1) := by
    have := Nat.pow_le_pow_right (n := 256) (by decide) (show 1 ≤ k - 1 by omega); simpa using this
  exact ⟨beq_iff_eq.mp h1, by omega, Nat.le_trans hp h4⟩

/-! ## Word lists and the precomputed values -/

/-- An address outside the working space is past the `n` bytes of a buffer
outside it, from that buffer's start. -/
theorem le_ofs_of_sep {B op x : Addr} {Z n : Nat} (hsep : ∀ i < n, Z ≤ ofs B (op + BitVec.ofNat 64 i))
    (hx : ofs B x < Z) : n ≤ ofs op x := by
  rcases Nat.lt_or_ge (ofs op x) n with h | h
  · have := hsep (ofs op x) h
    rw [show op + BitVec.ofNat 64 (ofs op x) = x by
      rw [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]] at this
    omega
  · exact h

/-- A word of a number, as `toWords` gives it. -/
theorem word_eq_ofNat (m : Mem) (B : Addr) (ed w : Nat) {q : Nat} (hq : q < w) :
    word m B (ed + 8 * q) = BitVec.ofNat 64 (wv m B ed w / 2 ^ (64 * q)) := by
  apply BitVec.eq_of_toNat_eq
  rw [word_of_wv m B ed w hq, BitVec.toNat_ofNat]

/-- The `2 w` words at `op`: two numbers of `w` words. -/
theorem wordsAt_two {m : Mem} {op : Addr} {w : Nat} {x y : Nat}
    (hx : ∀ i < w, word m op (8 * i) = BitVec.ofNat 64 (x / 2 ^ (64 * i)))
    (hy : ∀ i < w, word m op (8 * w + 8 * i) = BitVec.ofNat 64 (y / 2 ^ (64 * i))) :
    Spec.Rsa.wordsAt m op (2 * w) = Spec.Rsa.toWords x w ++ Spec.Rsa.toWords y w := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, show 2 * w = w + w by omega, List.range_add,
    List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun i hi => hx i (List.mem_range.mp hi)
  · refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply]
    rw [show 8 * (w + i) = 8 * w + 8 * i by omega]
    exact hy i (List.mem_range.mp hi)

/-- The precomputed values of a valid modulus. -/
theorem publicPrecompute_some {nb : List Byte} {k : Nat} (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.toWords (Spec.Rsa.os2ip nb) ((k + 7) / 8) ++
      Spec.Rsa.toWords (2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb) ((k + 7) / 8)) := by
  simp only [Spec.Rsa.publicPrecompute, hnl, hv, ite_true]; rfl

/-- A number from its words. -/
theorem wv_of_words {m : Mem} {p : Addr} {d x : Nat} : ∀ {n : Nat},
    (∀ i < n, (word m p (d + 8 * i)).toNat = x / 2 ^ (64 * i) % 2 ^ 64) → wv m p d n = x % 2 ^ (64 * n)
  | 0, _ => by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | n + 1, h => by
    rw [wv, wv_of_words fun i hi => h i (by omega), h n (by omega), pow64_succ, Nat.mod_mul]

/-- The `2 w` words at `pp`, as two numbers of `w` words. -/
theorem pre_words {m : Mem} {pp : Addr} {w N R : Nat}
    (h : Spec.Rsa.wordsAt m pp (2 * w) = Spec.Rsa.toWords N w ++ Spec.Rsa.toWords R w)
    (hN : N < 2 ^ (64 * w)) (hR : R < 2 ^ (64 * w)) :
    wv m pp 0 w = N ∧ wv m pp (8 * w) w = R := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, show 2 * w = w + w by omega, List.range_add,
    List.map_append, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_eq_of_lt hN]
    refine wv_of_words fun i hi => ?_
    show (m.readW (pp + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
    rw [Nat.zero_add, h1 i (List.mem_range.mpr hi), BitVec.toNat_ofNat]
  · rw [← Nat.mod_eq_of_lt hR]
    refine wv_of_words fun i hi => ?_
    have := h2 i (List.mem_range.mpr hi)
    simp only [Function.comp_apply] at this
    show (m.readW (pp + BitVec.ofNat 64 (8 * w + 8 * i)) 64).toNat = _
    rw [show 8 * w + 8 * i = 8 * (w + i) by omega, this, BitVec.toNat_ofNat]

/-- `pre` holds the values of the valid modulus `nB`. -/
theorem pre_of_some {m : Mem} {pp : Addr} {k : Nat} {nB : List Byte} (hl : nB.length = k) (hk : 64 ≤ k)
    (hpp : Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt m pp (2 * ((k + 7) / 8)))) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true ∧ wv m pp 0 ((k + 7) / 8) = Spec.Rsa.os2ip nB ∧
      wv m pp (8 * ((k + 7) / 8)) ((k + 7) / 8) = 2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nB := by
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true := by
    cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k
    · simp [Spec.Rsa.publicPrecompute, hl, hv] at hpp
    · rfl
  rw [publicPrecompute_some hl hv] at hpp
  have hlt : Spec.Rsa.os2ip nB < 2 ^ (64 * ((k + 7) / 8)) := by
    have := os2ip_lt nB
    rw [hl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have hpos : 0 < Spec.Rsa.os2ip nB := by
    have := (valid_facts hv hk).2.1; omega
  obtain ⟨h1, h2⟩ := pre_words (Option.some.inj hpp).symm hlt (Nat.lt_trans (Nat.mod_lt _ hpos) hlt)
  exact ⟨hv, h1, h2⟩

/-- `wordsAt`'s words determine the numbers they make. -/
theorem wv_of_wordsAt {m m' : Mem} {p : Addr} {n c w : Nat}
    (h : Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt m' p n) (hc : c + w ≤ n) :
    wv m p (8 * c) w = wv m' p (8 * c) w :=
  wv_congr fun i hi => by
    have := congrArg (fun l => l[c + i]?) h
    simp only [Spec.Rsa.wordsAt, List.getElem?_map, List.getElem?_range (show c + i < n by omega),
      Option.map_some, Option.some.injEq] at this
    show m.readW (p + BitVec.ofNat 64 (8 * c + 8 * i)) 64 = m'.readW (p + BitVec.ofNat 64 (8 * c + 8 * i)) 64
    rw [show 8 * c + 8 * i = 8 * (c + i) by omega]
    exact this

/-- `-n⁻¹ mod 2⁶⁴` is unique. -/
theorem minv_unique {n : Nat} {a b : BitVec 64} (hn : n % 2 = 1) (ha : (n * a.toNat + 1) % 2 ^ 64 = 0)
    (hb : (n * b.toNat + 1) % 2 ^ 64 = 0) : a = b := by
  have hc : Nat.Coprime (2 ^ 64) n := VG.Proof.Bignum.coprime_pow2 hn 64
  have h : a.toNat * n % 2 ^ 64 = b.toNat * n % 2 ^ 64 := by
    rw [Nat.mul_comm a.toNat, Nat.mul_comm b.toNat]
    omega
  have he := VG.Proof.Bignum.mont_cancel hc.symm h
  apply BitVec.eq_of_toNat_eq
  simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using he

/-- The leak of `pre` and `e`, as numbers, determines each when `pre`'s
length is the same. -/
theorem leak_eq2 {a c : List (BitVec 64)} {b d : List Byte} (hl : a.length = c.length)
    (h : a.map (·.toNat) ++ b.map (·.toNat) = c.map (·.toNat) ++ d.map (·.toNat)) : a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
  exact ⟨(List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h1,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h2⟩

/-! ## Buffers and the working space -/

theorem contains_scr {B a : Addr} {Z : Nat} (h : ofs B a < Z) : (⟨B, Z⟩ : Region).Contains a 1 := by
  simp only [Region.Contains, ofs] at *; omega

/-- A byte of a region disjoint from the working space is outside it. -/
theorem out_scr {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr} (ha : r.Contains a 1) :
    Z ≤ ofs B a := by
  rcases Nat.lt_or_ge (ofs B a) Z with h | h
  · exact absurd (contains_scr h) (hd a ha)
  · exact h

theorem contains_byte (p : Addr) {i len : Nat} (hi : i < len) (hlen : len ≤ 2 ^ 64) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
  Offset.contains_base p (by omega) (by omega)

/-! ## The results -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem i2osp_zero' (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  rw [i2osp_zero]; simp [List.map_const']

theorem setWidth_flag (c : Bool) : (BitVec.ofNat 64 c.toNat).setWidth 32 = if c then 1 else 0 := by
  cases c <;> rfl

/-- What `code` leaves: the result `r` and flag `c` of `fail` or `main`. -/
theorem written_of {m : Mem} {out : Addr} {k : Nat} {rax : BitVec 64} {nb eb xb : List Byte}
    (hnl : nb.length = k) {r : Nat} {c : Bool}
    (hb : Spec.Rsa.bytesAt m out k = Spec.Rsa.i2osp r k) (hr : rax = BitVec.ofNat 64 c.toNat)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true →
      c = decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb) ∧
      r = if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
        Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % Spec.Rsa.os2ip nb else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = false → c = false ∧ r = 0) :
    Spec.Rsa.written m out k (rax.setWidth 32) (Spec.Rsa.publicOp nb eb xb) := by
  unfold Spec.Rsa.publicOp
  rw [hnl, hr, setWidth_flag]
  cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k
  · obtain ⟨rfl, rfl⟩ := hf hv
    simp only [hv, Bool.false_eq_true, ite_false, Spec.Rsa.written]
    exact ⟨trivial, by rw [hb, i2osp_zero']⟩
  · obtain ⟨rfl, rfl⟩ := hc hv
    by_cases hx : Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb
    · simp only [hv, hx, ite_true, decide_true, Spec.Rsa.encrypt, Option.map_some, Spec.Rsa.written]
      simp only [hx, ite_true] at hb
      exact ⟨trivial, by rw [hb, VG.Proof.Bignum.powMod_eq]⟩
    · simp only [hv, hx, ite_true, ite_false, decide_false, Spec.Rsa.encrypt, Option.map_none,
        Spec.Rsa.written, Bool.false_eq_true]
      simp only [hx, ite_false] at hb
      exact ⟨trivial, by rw [hb, i2osp_zero']⟩

theorem bytesAt_eq (m : Mem) (p : Addr) (k : Nat) :
    Spec.Rsa.bytesAt m p k = (List.range k).map fun i => m (p + BitVec.ofNat 64 i) := rfl

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Bignum
