import VerifiedGarbage.Spec.Rc4
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Table`. -/
section

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

theorem context_ext {a b : Context} (ht : a.table = b.table) (hi : a.i = b.i)
    (hj : a.j = b.j) : a = b := by
  cases a
  cases b
  cases ht
  cases hi
  cases hj
  rfl

theorem get_byte (s : Table) (idx : Byte) : s.getD idx.toNat 0 = s[idx.toNat]'idx.isLt := by
  simp [Vector.getD, Array.getD, idx.isLt]

/-- Read a swapped table, including the case where both indices coincide. -/
theorem swap_get (s : Table) (i j k : Byte) :
    (swap s i j).getD k.toNat 0 =
      if k = j then s.getD i.toNat 0 else if k = i then s.getD j.toNat 0 else s.getD k.toNat 0 := by
  simp only [VG.Proof.Rc4.get_byte, swap, Vector.getElem_set! k.isLt]
  have hij (a b : Byte) : a.toNat = b.toNat ↔ a = b := BitVec.toNat_inj
  simp only [hij, eq_comm]

theorem swap_self (s : Table) (i : Byte) : swap s i i = s := by
  apply Vector.ext
  intro k hk
  simp only [swap, VG.Proof.Rc4.get_byte, Vector.getElem_set! hk]
  by_cases h : i.toNat = k
  · subst k; simp
  · simp only [h, ite_false]

theorem swap_i (s : Table) (i j : Byte) :
    (swap s i j).getD i.toNat 0 = s.getD j.toNat 0 := by
  rw [VG.Proof.Rc4.swap_get]
  by_cases h : i = j
  · subst j; simp
  · simp only [h, ite_false, ite_true]

theorem swap_j (s : Table) (i j : Byte) :
    (swap s i j).getD j.toNat 0 = s.getD i.toNat 0 := by
  rw [VG.Proof.Rc4.swap_get, ite_eq_left rfl]

/-- Swapping leaves the sum of the two selected bytes unchanged. -/
theorem swap_sum (s : Table) (i j : Byte) :
    (swap s i j).getD i.toNat 0 + (swap s i j).getD j.toNat 0 =
      s.getD i.toNat 0 + s.getD j.toNat 0 := by
  rw [VG.Proof.Rc4.swap_i, VG.Proof.Rc4.swap_j, BitVec.add_comm]

/-- The output lookup index can use the two original selected bytes. -/
theorem step_eq (ctx : Context) :
    step ctx =
      let i := ctx.i + 1
      let a := ctx.table.getD i.toNat 0
      let j := ctx.j + a
      let b := ctx.table.getD j.toNat 0
      let s := swap ctx.table i j
      ({ table := s, i, j }, s.getD (a + b).toNat 0) := by
  dsimp only [step]
  rw [VG.Proof.Rc4.swap_sum]

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Memory`. -/
section

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

theorem write_byte (m : Mem) (p x : Addr) (value : Byte) :
    m.write p 1 value x = if x = p then value else m x := by
  unfold Mem.write
  by_cases h : x = p
  · subst x
    simp only [BitVec.sub_self, show (0#64).toNat = 0 from rfl, Nat.zero_lt_succ,
      ite_true, Nat.mul_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp [hk]
  · have hne : ¬(x - p).toNat < 1 := by bv_omega
    simp only [hne, h, ite_false]

/-- A vector store whose bytes equal the old memory is a memory identity. -/
theorem write_read (m : Mem) (p : Addr) (n : Nat) : m.write p n (m.read p n) = m := by
  funext x
  unfold Mem.write
  by_cases h : (x - p).toNat < n
  · rw [ite_eq_left h, Mem.extractLsb'_read _ _ h]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h]

theorem table_get (m : Mem) (p : Addr) (idx : Byte) :
    (contextAt m p).table.getD idx.toNat 0 = m (p + BitVec.ofNat 64 idx.toNat) := by
  rw [VG.Proof.Rc4.get_byte]
  simp only [contextAt, Vector.getElem_ofFn]

theorem table_write (m : Mem) (p : Addr) (idx value : Byte) :
    (contextAt (m.write (p + BitVec.ofNat 64 idx.toNat) 1 value) p).table =
      (contextAt m p).table.set! idx.toNat value := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn, Vector.getElem_set! hk, VG.Proof.Rc4.write_byte]
  have heq : p + BitVec.ofNat 64 k = p + BitVec.ofNat 64 idx.toNat ↔ idx.toNat = k := by
    rw [BitVec.add_right_inj]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega)] at hn
      exact hn.symm
    · intro h; rw [h]
  simp only [heq]

theorem table_swap (m : Mem) (p : Addr) (i j : Byte) :
    (contextAt ((m.write (p + BitVec.ofNat 64 j.toNat) 1
      (m (p + BitVec.ofNat 64 i.toNat))).write (p + BitVec.ofNat 64 i.toNat) 1
        (m (p + BitVec.ofNat 64 j.toNat))) p).table = swap (contextAt m p).table i j := by
  rw [VG.Proof.Rc4.table_write, VG.Proof.Rc4.table_write]
  unfold swap
  rw [VG.Proof.Rc4.table_get, VG.Proof.Rc4.table_get]
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_set! hk]
  by_cases hj : j.toNat = k
  · subst k
    by_cases hi : i.toNat = j.toNat
    · rw [hi]
    · simp only [hi, ite_true, ite_false]
  · by_cases hi : i.toNat = k
    · simp only [hi, hj, ite_true, ite_false]
    · simp only [hi, hj, ite_false]

/-- A write outside the table leaves its abstract permutation unchanged. -/
theorem table_write_sep (m : Mem) (p q : Addr) (value : Byte)
    (h : Mem.Sep p 256 q 1) :
    (contextAt (m.write q 1 value) p).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  apply Mem.write_apply
  exact h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hk)

/-- Scheduling modifies only the 256-byte table. -/
def TableFrame (p : Addr) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 256 → m' x = m x

theorem TableFrame.refl (p : Addr) (m : Mem) : VG.Proof.Rc4.TableFrame p m m := fun _ _ => rfl

theorem TableFrame.trans {p : Addr} {a b c : Mem} (h : VG.Proof.Rc4.TableFrame p a b)
    (k : VG.Proof.Rc4.TableFrame p b c) : VG.Proof.Rc4.TableFrame p a c := fun x hx => (k x hx).trans (h x hx)

theorem swap_frame (m : Mem) (p : Addr) (i j : Byte) :
    VG.Proof.Rc4.TableFrame p m ((m.write (p + BitVec.ofNat 64 j.toNat) 1
      (m (p + BitVec.ofNat 64 i.toNat))).write (p + BitVec.ofNat 64 i.toNat) 1
        (m (p + BitVec.ofNat 64 j.toNat))) := by
  intro x hx
  have hne (idx : Byte) : x ≠ p + BitVec.ofNat 64 idx.toNat := by
    intro he
    apply hx
    rw [he, Mem.sub_ofNat_toNat p (by omega)]
    exact idx.isLt
  rw [VG.Proof.Rc4.write_byte, ite_eq_right (hne _), VG.Proof.Rc4.write_byte, ite_eq_right (hne _)]

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem bytes_get (m : Mem) (p : Addr) (n k : Nat) (hk : k < n) :
    (bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [bytesAt, List.getD, hk]

/-- Any bounded offset access inside an already valid region is valid. -/
theorem region_offset (rs : List Region) (p : Addr) (n d k : Nat)
    (hd : d < 2 ^ 64) (hk : d + k ≤ n) (hp : InRegions rs p n) :
    InRegions rs (p + BitVec.ofNat 64 d) k := by
  obtain ⟨region, hregion, hcontains⟩ := hp
  refine ⟨region, hregion, ?_⟩
  unfold Region.Contains at hcontains ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hmod := Nat.mod_le ((p - region.base).toNat + d) (2 ^ 64)
  omega

/-- Writing the two stream indices completes the abstract context. -/
theorem context_finish (m : Mem) (p : Addr) (i j : Byte) :
    contextAt ((m.write (p + 256#64) 1 i).write (p + 257#64) 1 j) p =
      { table := (contextAt m p).table, i, j } := by
  apply VG.Proof.Rc4.context_ext
  · rw [VG.Proof.Rc4.table_write_sep, VG.Proof.Rc4.table_write_sep]
    · exact Offset.sep_base p (by decide) (by decide)
    · exact Offset.sep_base p (by decide) (by decide)
  · change ((m.write (p + 256#64) 1 i).write (p + 257#64) 1 j) (p + 256#64) = i
    rw [VG.Proof.Rc4.write_byte, ite_eq_right (show p + 256#64 ≠ p + 257#64 by bv_omega),
      VG.Proof.Rc4.write_byte, ite_eq_left rfl]
  · change ((m.write (p + 256#64) 1 i).write (p + 257#64) 1 j) (p + 257#64) = j
    rw [VG.Proof.Rc4.write_byte, ite_eq_left rfl]

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Dword`. -/
section

/-!
# RC4: scanning the table a doubleword at a time

Facts for implementations that visit the 256-byte table as 64 doublewords
at fixed addresses: the masks `sub` and `sbb` make, the bytes of a
doubleword, and a doubleword stored back XORed with a difference in one
byte. (`Qword.lean` has the same for quadwords.)
-/

namespace VG.Proof.Rc4
open VG

/-- `0 - CF`, as `sbb r, r` leaves it after a `sub`. -/
theorem borrow_mask32 (p : Bool) :
    (0#32 - (BitVec.ofBool p).setWidth 32) = if p then BitVec.allOnes 32 else 0#32 := by
  cases p <;> decide

theorem toNat_lt_four (x : BitVec 32) : x.toNat < 4 ↔ x >>> 2 = 0#32 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
  omega

/-- Byte `n` of the table is in doubleword `k` iff `n XOR 4k < 4`. -/
theorem row_hit32 (idx : Byte) {k : Nat} (hk : k < 64) :
    (idx.setWidth 32 ^^^ BitVec.ofNat 32 (4 * k)).toNat < 4 ↔ idx.toNat / 4 = k := by
  rw [VG.Proof.Rc4.toNat_lt_four, BitVec.ushiftRight_xor_distrib, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := idx.isLt
  omega

/-- Byte `n` of the table is byte `j` of its doubleword iff `(n AND 3) XOR j < 1`. -/
theorem lane_hit32 (idx : Byte) {j : Nat} (hj : j < 4) :
    ((idx.setWidth 32 &&& BitVec.ofNat 32 3) ^^^ BitVec.ofNat 32 j).toNat < 1 ↔
      idx.toNat % 4 = j := by
  have h1 : ∀ x : BitVec 32, x.toNat < 1 ↔ x = 0#32 := by
    intro x
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rw [h1, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (3 % 2 ^ 32 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := idx.isLt
  omega

/-- The doubleword holding byte `n` of the table, and the byte's position in it. -/
theorem row_lane32 (p : Addr) (n : Nat) :
    p + BitVec.ofNat 64 (4 * (n / 4)) + BitVec.ofNat 64 (n % 4) = p + BitVec.ofNat 64 n := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]

/-- Byte `L` of a little-endian doubleword, shifted down and masked. -/
theorem dword_byte (m : Mem) (a : Addr) {L : Nat} (hL : L < 4) :
    (m.readW a 32 >>> (8 * L)) &&& BitVec.ofNat 32 255 = (m (a + BitVec.ofNat 64 L)).setWidth 32 := by
  rw [← Mem.extractLsb'_read m a (n := 4) hL]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h255 : (BitVec.ofNat 32 255).getLsbD i = decide (i < 8) := by
    change Nat.testBit 255 i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  simp only [BitVec.getLsbD_and, h255, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', Mem.readW, Nat.reduceDiv]
  by_cases h : i < 8
  · simp [h, show 8 * L + i < 32 by omega, show i < 32 by omega]
  · simp [h]

/-- A doubleword shifted right by a byte more. -/
theorem shr_byte32 (x : BitVec 32) (j : Nat) : (x >>> (8 * j)) >>> 8 = x >>> (8 * (j + 1)) := by
  rw [← BitVec.shiftRight_add]
  rfl

/-- The bytes of a byte shifted left by whole bytes. -/
theorem shl_extract32 (c : Byte) {L e : Nat} (hL : L < 4) (he : e < 4) :
    ((c.setWidth 32) <<< (8 * L)).extractLsb' (8 * e) 8 = if e = L then c else 0#8 := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and, show 8 * e + i < 32 by omega]
  by_cases h : e = L
  · subst h
    simp [show ¬ 8 * e + i < 8 * e by omega, show 8 * e + i - 8 * e = i by omega, hi,
      show i < 32 by omega]
  · by_cases hlt : e < L
    · simp [h, show 8 * e + i < 8 * L by omega]
    · simp [h, show ¬ 8 * e + i < 8 * L by omega, hc _ (show 8 ≤ 8 * e + i - 8 * L by omega)]

/-- Rotating right by 24 is a shift left by a byte, while the top byte is zero. -/
theorem rot_byte32 (c : Byte) {n : Nat} (hn : n < 3) :
    ((c.setWidth 32) <<< (8 * n)).rotateRight 24 = (c.setWidth 32) <<< (8 * (n + 1)) := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    show 24 % 32 = 24 from rfl, show 32 - 24 = 8 from rfl, hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8, show 24 + i < 32 by omega, show ¬ 24 + i < 8 * n by omega,
      show i < 8 * (n + 1) by omega, hc _ (show 8 ≤ 24 + i - 8 * n by omega)]
  · by_cases hlo : i - 8 < 8 * n
    · simp [h8, hlo, show i - 8 < 32 by omega, show i < 8 * (n + 1) by omega]
    · simp [h8, hlo, show i - 8 < 32 by omega, show ¬ i < 8 * (n + 1) by omega,
        show i - 8 - 8 * n = i - 8 * (n + 1) by omega]

/-- Storing back a doubleword XORed with `y` XORs each of its bytes with that of `y`. -/
theorem writeW_xor32 (m : Mem) (a : Addr) (y : BitVec 32) (x : Addr) :
    m.writeW a (m.readW a 32 ^^^ y) x =
      if (x - a).toNat < 4 then m x ^^^ y.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 4 then ((m.readW a 32 ^^^ y).setWidth 32).extractLsb'
    (8 * (x - a).toNat) 8 else m x) = _
  by_cases h : (x - a).toNat < 4
  · rw [ite_eq_left h, ite_eq_left h, BitVec.setWidth_eq, BitVec.extractLsb'_xor]
    congr 1
    change ((m.read a 4).setWidth 32).extractLsb' (8 * (x - a).toNat) 8 = m x
    rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ h, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Storing a doubleword back unchanged. -/
theorem writeW_readW32 (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  have h := VG.Proof.Rc4.writeW_xor32 m a 0#32 x
  rw [BitVec.xor_zero] at h
  rw [h]
  split
  · rw [show (0#32).extractLsb' (8 * (x - a).toNat) 8 = 0#8 by simp, BitVec.xor_zero]
  · rfl

/-- Storing back the doubleword that holds byte `n` of the table at `p`, XORed
with `c` shifted to the byte's position, XORs that byte with `c`. -/
theorem writeW_byte32 (m : Mem) (p : Addr) (n : Nat) (c : Byte) :
    m.writeW (p + BitVec.ofNat 64 (4 * (n / 4)))
      (m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 ^^^ (c.setWidth 32) <<< (8 * (n % 4))) =
    m.write (p + BitVec.ofNat 64 n) 1 (m (p + BitVec.ofNat 64 n) ^^^ c) := by
  funext x
  rw [VG.Proof.Rc4.writeW_xor32, VG.Proof.Rc4.write_byte]
  let q := p + BitVec.ofNat 64 (4 * (n / 4))
  have hq : p + BitVec.ofNat 64 n = q + BitVec.ofNat 64 (n % 4) := (VG.Proof.Rc4.row_lane32 p n).symm
  have hiff : ∀ e < 4, (x - q).toNat = e ↔ x = q + BitVec.ofNat 64 e := by
    intro e he
    constructor
    · intro h
      have h' : x - q = BitVec.ofNat 64 e := by
        apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← h', BitVec.add_comm, BitVec.sub_add_cancel]
    · intro h; rw [h, Mem.sub_ofNat_toNat q (by omega)]
  change (if (x - q).toNat < 4 then m x ^^^ ((c.setWidth 32) <<< (8 * (n % 4))).extractLsb'
    (8 * (x - q).toNat) 8 else m x) = _
  rw [hq]
  by_cases hin : (x - q).toNat < 4
  · rw [ite_eq_left hin, VG.Proof.Rc4.shl_extract32 c (Nat.mod_lt _ (by decide)) hin]
    by_cases he : (x - q).toNat = n % 4
    · rw [ite_eq_left he, ite_eq_left ((hiff _ (Nat.mod_lt _ (by decide))).mp he)]
      rw [(hiff _ (Nat.mod_lt _ (by decide))).mp he]
    · rw [ite_eq_right he, BitVec.xor_zero, ite_eq_right]
      intro hx
      exact he ((hiff _ (Nat.mod_lt _ (by decide))).mpr hx)
  · rw [ite_eq_right hin, ite_eq_right]
    intro hx
    exact hin (by rw [hx, Mem.sub_ofNat_toNat q (by omega)]; exact Nat.mod_lt _ (by decide))

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Identity`. -/
section

/-! # RC4: the identity permutation, stored a byte at a time -/

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- The memory once the first `r` bytes of the table at `p` are the identity. -/
def identityMem (m : Mem) (p : Addr) (r : Nat) : Mem :=
  fun x => if (x - p).toNat < r then BitVec.ofNat 8 (x - p).toNat else m x

theorem identityMem_zero (m : Mem) (p : Addr) : VG.Proof.Rc4.identityMem m p 0 = m := by
  funext x
  simp only [VG.Proof.Rc4.identityMem, Nat.not_lt_zero, ite_false]

theorem identityMem_store (m : Mem) (p : Addr) (r : Nat) (hr : r < 256) :
    (VG.Proof.Rc4.identityMem m p r).write (p + BitVec.ofNat 64 r) 1 (BitVec.ofNat 8 r) =
      VG.Proof.Rc4.identityMem m p (r + 1) := by
  funext x
  rw [VG.Proof.Rc4.write_byte]
  have heq : x = p + BitVec.ofNat 64 r ↔ (x - p).toNat = r := by
    constructor
    · intro h; rw [h, Mem.sub_ofNat_toNat p (by omega)]
    · intro h
      have he : x - p = BitVec.ofNat 64 r := by
        apply BitVec.eq_of_toNat_eq
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← he, BitVec.add_comm, BitVec.sub_add_cancel]
  simp only [VG.Proof.Rc4.identityMem, heq]
  by_cases h : (x - p).toNat = r
  · simp only [h, ite_true, Nat.lt_add_one]
  · by_cases hl : (x - p).toNat < r
    · simp only [h, hl, show (x - p).toNat < r + 1 by omega, ite_true, ite_false]
    · simp only [h, hl, show ¬ (x - p).toNat < r + 1 by omega, ite_false]

theorem identityMem_table (m : Mem) (p : Addr) :
    (contextAt (VG.Proof.Rc4.identityMem m p 256) p).table =
      Vector.ofFn (fun i : Fin 256 => BitVec.ofNat 8 i.val) := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn, VG.Proof.Rc4.identityMem]
  rw [Mem.sub_ofNat_toNat p (by omega), ite_eq_left hk]

theorem identityMem_frame (m : Mem) (p : Addr) (r : Nat) (hr : r ≤ 256) :
    VG.Proof.Rc4.TableFrame p m (VG.Proof.Rc4.identityMem m p r) := by
  intro x hx
  simp only [VG.Proof.Rc4.identityMem, show ¬ (x - p).toNat < r by omega, ite_false]

/-- The key offset after `r`, advanced: back to 0 at the key length. -/
theorem key_next (r len : Nat) (hl : 0 < len) (hlen : len ≤ 256) :
    (if (BitVec.ofNat 64 (r % len) + 1#64).toNat < len then BitVec.ofNat 64 (r % len) + 1#64
      else 0#64) = BitVec.ofNat 64 ((r + 1) % len) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 64 (r % len) + 1#64).toNat = r % len + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len < 2 ^ 64 by omega)]
    change (r % len + 1) % 2 ^ 64 = _
    omega
  rw [ht]
  have ha : (r + 1) % len = (r % len + 1) % len := by
    simp only [Nat.add_mod, Nat.mod_mod]
  by_cases h : r % len + 1 < len
  · rw [ite_eq_left h]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len + 1 < 2 ^ 64 by omega)]
  · rw [ite_eq_right h, ha, show r % len + 1 = len by omega, Nat.mod_self]

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Stream`. -/
section

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

theorem bytes_cons (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1#64) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, BitVec.add_zero]
  congr 1
  apply List.map_congr_left
  intro k hk
  change m (p + BitVec.ofNat 64 (k + 1)) = m (p + 1#64 + BitVec.ofNat 64 k)
  rw [Offset.add_ofNat_succ]
  rfl

/-- The writes of a stream operation stay within its table and data. -/
def StreamFrame (p d : Addr) (n : Nat) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 256 → ¬ (x - d).toNat < n → m' x = m x

theorem stream_frame_step (m : Mem) (p d : Addr) (i j value : Byte) :
    VG.Proof.Rc4.StreamFrame p d 1 m (((m.write (p + BitVec.ofNat 64 j.toNat) 1
      (m (p + BitVec.ofNat 64 i.toNat))).write (p + BitVec.ofNat 64 i.toNat) 1
        (m (p + BitVec.ofNat 64 j.toNat))).write d 1 value) := by
  intro x hp hd
  have hne : x ≠ d := by
    intro he; subst x; exact hd (by simp [BitVec.sub_self])
  rw [VG.Proof.Rc4.write_byte, ite_eq_right hne]
  exact VG.Proof.Rc4.swap_frame m p i j x hp

theorem sep_symm {p q : Addr} {n k : Nat} (h : Mem.Sep p n q k) : Mem.Sep q k p n :=
  fun x hx hy => h x hy hx

theorem sep_tail {p d : Addr} {n : Nat} (_hn : n + 1 < 2 ^ 64)
    (h : Mem.Sep p 256 d (n + 1)) : Mem.Sep p 256 (d + 1#64) n := by
  intro x hp ht
  apply h x hp
  have hh : (⟨d, n + 1⟩ : Region).Contains (d + 1#64) n := by
    change (d + 1#64 - d).toNat + n ≤ n + 1
    rw [Offset.add_sub_cancel_left]
    change 1 + n ≤ n + 1
    omega
  have hb := hh.byte ht
  change (x - d).toNat + 1 ≤ n + 1 at hb
  omega

theorem bytes_write_sep (m : Mem) (d q : Addr) (n : Nat) (value : Byte)
    (hn : n < 2 ^ 64) (h : Mem.Sep d n q 1) :
    bytesAt (m.write q 1 value) d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  exact Mem.write_apply (h _ (by rw [Mem.sub_ofNat_toNat d (by omega)]; exact hk'))

theorem bytes_table_frame (m m' : Mem) (p d : Addr) (n : Nat) (hn : n < 2 ^ 64)
    (h : VG.Proof.Rc4.TableFrame p m m') (hs : Mem.Sep d n p 256) : bytesAt m' d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  exact h _ (hs _ (by rw [Mem.sub_ofNat_toNat d (by omega)]; exact hk'))

theorem stream_frame_trans_tail {m a b : Mem} {p d : Addr} {n : Nat}
    (h : VG.Proof.Rc4.StreamFrame p d 1 m a) (k : VG.Proof.Rc4.StreamFrame p (d + 1#64) n a b) :
    VG.Proof.Rc4.StreamFrame p d (n + 1) m b := by
  intro x hp hd
  have htail : ¬ (x - (d + 1#64)).toNat < n := by
    intro hx
    have hc : (⟨d, n + 1⟩ : Region).Contains (d + 1#64) n := by
      change (d + 1#64 - d).toNat + n ≤ n + 1
      rw [Offset.add_sub_cancel_left]
      change 1 + n ≤ n + 1
      omega
    have hh := hc.byte hx
    change (x - d).toNat + 1 ≤ n + 1 at hh
    omega
  exact (k x hp htail).trans (h x hp (by omega))

theorem stream_head (m m' : Mem) (p d : Addr) (n : Nat) (hn : n + 1 < 2 ^ 64)
    (h : VG.Proof.Rc4.StreamFrame p (d + 1#64) n m m') (hs : Mem.Sep p 256 d (n + 1)) : m' d = m d := by
  have hp : ¬ (d - p).toNat < 256 := by
    intro hh
    exact hs d hh (by simp only [BitVec.sub_self]; change 0 < n + 1; omega)
  apply h d hp
  have hsep : Mem.Sep d 1 (d + 1#64) n := Offset.sep_base d (by decide) (by omega)
  exact hsep d (by simp only [BitVec.sub_self]; decide)

theorem sep_offset_right {d p : Addr} {n k off count : Nat}
    (h : Mem.Sep d n p k) (ho : off < 2 ^ 64) (hc : off + count ≤ k) :
    Mem.Sep d n (p + BitVec.ofNat 64 off) count := by
  intro x hd hx
  apply h x hd
  have hh : (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 off) count :=
    Offset.contains_base p hc ho
  have hb := hh.byte hx
  change (x - p).toNat + 1 ≤ k at hb
  omega

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Iterate`. -/
section

/-!
# The stream, byte by byte

`stepN c n` is the context after `n` steps from `c`, and `ks c n` the `n`-th
keystream byte. `update` XORs the input with these bytes and ends in
`stepN` of its length (`update_bytes`).
-/

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- The context after `n` steps. -/
def stepN (c : Context) : Nat → Context
  | 0 => c
  | n + 1 => (step (VG.Proof.Rc4.stepN c n)).1

/-- Keystream byte `n`. -/
def ks (c : Context) (n : Nat) : Byte := (step (VG.Proof.Rc4.stepN c n)).2

theorem stepN_succ' (c : Context) (n : Nat) : VG.Proof.Rc4.stepN c (n + 1) = VG.Proof.Rc4.stepN (step c).1 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [VG.Proof.Rc4.stepN] at ih ⊢; rw [ih]

theorem ks_succ (c : Context) (n : Nat) : VG.Proof.Rc4.ks c (n + 1) = VG.Proof.Rc4.ks (step c).1 n := by
  simp only [VG.Proof.Rc4.ks, VG.Proof.Rc4.stepN_succ']

theorem update_fst (c : Context) (bs : List Byte) : (update c bs).1 = VG.Proof.Rc4.stepN c bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp only [update, List.length_cons, VG.Proof.Rc4.stepN_succ', ih]

/-- Bytes that are the input XORed with the keystream are `update`'s output. -/
theorem update_bytes (c : Context) (m m' : Mem) (d : Addr) (n : Nat)
    (h : ∀ k < n, m' (d + BitVec.ofNat 64 k) = m (d + BitVec.ofNat 64 k) ^^^ VG.Proof.Rc4.ks c k) :
    bytesAt m' d n = (update c (bytesAt m d n)).2 := by
  induction n generalizing c d with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Rc4.bytes_cons, VG.Proof.Rc4.bytes_cons]
    simp only [update]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih (step c).1 (d + 1#64) fun k hk => by
      have := h (k + 1) (by omega)
      rw [VG.Proof.Rc4.ks_succ] at this
      rw [show d + 1#64 + BitVec.ofNat 64 k = d + BitVec.ofNat 64 (k + 1) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
      exact this]
    rfl

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Qword`. -/
section

/-!
# RC4: scanning the table a quadword at a time

Facts for implementations that visit the 256-byte table as 32 quadwords at
fixed addresses: the masks `sub` and `sbb` make, the bytes of a quadword,
and a quadword stored back XORed with a difference in one byte.
-/

namespace VG.Proof.Rc4
open VG

/-- `0 - CF`, as `sbb r, r` leaves it after a `sub`. -/
theorem borrow_mask (p : Bool) :
    (0#64 - (BitVec.ofBool p).setWidth 64) = if p then BitVec.allOnes 64 else 0#64 := by
  cases p <;> decide

theorem toNat_lt_eight (x : BitVec 64) : x.toNat < 8 ↔ x >>> 3 = 0#64 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
  omega

/-- Byte `n` of the table is in quadword `k` iff `n XOR 8k < 8`. -/
theorem row_hit (idx : Byte) {k : Nat} (hk : k < 32) :
    (idx.setWidth 64 ^^^ BitVec.ofNat 64 (8 * k)).toNat < 8 ↔ idx.toNat / 8 = k := by
  rw [VG.Proof.Rc4.toNat_lt_eight, BitVec.ushiftRight_xor_distrib, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := idx.isLt
  omega

/-- Byte `n` of the table is byte `j` of its quadword iff `(n AND 7) XOR j < 1`. -/
theorem lane_hit (idx : Byte) {j : Nat} (hj : j < 8) :
    ((idx.setWidth 64 &&& BitVec.ofNat 64 7) ^^^ BitVec.ofNat 64 j).toNat < 1 ↔
      idx.toNat % 8 = j := by
  have h1 : ∀ x : BitVec 64, x.toNat < 1 ↔ x = 0#64 := by
    intro x
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rw [h1, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (7 % 2 ^ 64 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := idx.isLt
  omega

/-- The quadword holding byte `n` of the table, and the byte's position in it. -/
theorem row_lane (p : Addr) (n : Nat) :
    p + BitVec.ofNat 64 (8 * (n / 8)) + BitVec.ofNat 64 (n % 8) = p + BitVec.ofNat 64 n := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]

/-- Byte `L` of a little-endian quadword, shifted down and masked. -/
theorem qword_byte (m : Mem) (a : Addr) {L : Nat} (hL : L < 8) :
    (m.readW a 64 >>> (8 * L)) &&& BitVec.ofNat 64 255 = (m (a + BitVec.ofNat 64 L)).setWidth 64 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hL]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h255 : (BitVec.ofNat 64 255).getLsbD i = decide (i < 8) := by
    change Nat.testBit 255 i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  simp only [BitVec.getLsbD_and, h255, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', Mem.readW, Nat.reduceDiv]
  by_cases h : i < 8
  · simp [h, show 8 * L + i < 64 by omega, show i < 64 by omega]
  · simp [h]

/-- A quadword shifted right by a byte more. -/
theorem shr_byte (x : BitVec 64) (j : Nat) : (x >>> (8 * j)) >>> 8 = x >>> (8 * (j + 1)) := by
  rw [← BitVec.shiftRight_add]
  rfl

/-- The bytes of a byte shifted left by whole bytes. -/
theorem shl_extract (c : Byte) {L e : Nat} (hL : L < 8) (he : e < 8) :
    ((c.setWidth 64) <<< (8 * L)).extractLsb' (8 * e) 8 = if e = L then c else 0#8 := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and, show 8 * e + i < 64 by omega]
  by_cases h : e = L
  · subst h
    simp [show ¬ 8 * e + i < 8 * e by omega, show 8 * e + i - 8 * e = i by omega, hi,
      show i < 64 by omega]
  · by_cases hlt : e < L
    · simp [h, show 8 * e + i < 8 * L by omega]
    · simp [h, show ¬ 8 * e + i < 8 * L by omega, hc _ (show 8 ≤ 8 * e + i - 8 * L by omega)]

/-- Rotating right by 56 is a shift left by a byte, while the top byte is zero. -/
theorem rot_byte (c : Byte) {n : Nat} (hn : n < 7) :
    ((c.setWidth 64) <<< (8 * n)).rotateRight 56 = (c.setWidth 64) <<< (8 * (n + 1)) := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    show 56 % 64 = 56 from rfl, show 64 - 56 = 8 from rfl, hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8, show 56 + i < 64 by omega, show ¬ 56 + i < 8 * n by omega,
      show i < 8 * (n + 1) by omega, hc _ (show 8 ≤ 56 + i - 8 * n by omega)]
  · by_cases hlo : i - 8 < 8 * n
    · simp [h8, hlo, show i - 8 < 64 by omega, show i < 8 * (n + 1) by omega]
    · simp [h8, hlo, show i - 8 < 64 by omega, show ¬ i < 8 * (n + 1) by omega,
        show i - 8 - 8 * n = i - 8 * (n + 1) by omega]

/-- Storing back a quadword XORed with `y` XORs each of its bytes with that of `y`. -/
theorem writeW_xor (m : Mem) (a : Addr) (y : BitVec 64) (x : Addr) :
    m.writeW a (m.readW a 64 ^^^ y) x =
      if (x - a).toNat < 8 then m x ^^^ y.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 8 then ((m.readW a 64 ^^^ y).setWidth 64).extractLsb'
    (8 * (x - a).toNat) 8 else m x) = _
  by_cases h : (x - a).toNat < 8
  · rw [ite_eq_left h, ite_eq_left h, BitVec.setWidth_eq, BitVec.extractLsb'_xor]
    congr 1
    change ((m.read a 8).setWidth 64).extractLsb' (8 * (x - a).toNat) 8 = m x
    rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ h, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Storing a quadword back unchanged. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 64) = m := by
  funext x
  have h := VG.Proof.Rc4.writeW_xor m a 0#64 x
  rw [BitVec.xor_zero] at h
  rw [h]
  split
  · rw [show (0#64).extractLsb' (8 * (x - a).toNat) 8 = 0#8 by simp, BitVec.xor_zero]
  · rfl

/-- Storing back the quadword at `q` that holds byte `n` of the table at `p`,
XORed with `c` shifted to the byte's position, XORs that byte with `c`. -/
theorem writeW_byte (m : Mem) (p : Addr) (n : Nat) (c : Byte) :
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ (c.setWidth 64) <<< (8 * (n % 8))) =
    m.write (p + BitVec.ofNat 64 n) 1 (m (p + BitVec.ofNat 64 n) ^^^ c) := by
  funext x
  rw [VG.Proof.Rc4.writeW_xor, VG.Proof.Rc4.write_byte]
  let q := p + BitVec.ofNat 64 (8 * (n / 8))
  have hq : p + BitVec.ofNat 64 n = q + BitVec.ofNat 64 (n % 8) := (VG.Proof.Rc4.row_lane p n).symm
  have hiff : ∀ e < 8, (x - q).toNat = e ↔ x = q + BitVec.ofNat 64 e := by
    intro e he
    constructor
    · intro h
      have h' : x - q = BitVec.ofNat 64 e := by
        apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← h', BitVec.add_comm, BitVec.sub_add_cancel]
    · intro h; rw [h, Mem.sub_ofNat_toNat q (by omega)]
  change (if (x - q).toNat < 8 then m x ^^^ ((c.setWidth 64) <<< (8 * (n % 8))).extractLsb'
    (8 * (x - q).toNat) 8 else m x) = _
  rw [hq]
  by_cases hin : (x - q).toNat < 8
  · rw [ite_eq_left hin, VG.Proof.Rc4.shl_extract c (Nat.mod_lt _ (by decide)) hin]
    by_cases he : (x - q).toNat = n % 8
    · rw [ite_eq_left he, ite_eq_left ((hiff _ (Nat.mod_lt _ (by decide))).mp he)]
      rw [(hiff _ (Nat.mod_lt _ (by decide))).mp he]
    · rw [ite_eq_right he, BitVec.xor_zero, ite_eq_right]
      intro hx
      exact he ((hiff _ (Nat.mod_lt _ (by decide))).mpr hx)
  · rw [ite_eq_right hin, ite_eq_right]
    intro hx
    exact hin (by rw [hx, Mem.sub_ofNat_toNat q (by omega)]; exact Nat.mod_lt _ (by decide))

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Scan32`. -/
section

/-!
# RC4: a doubleword scan of the table, step by step

What the 32-bit implementations (x86, ARMv7) hold after visiting the first
doublewords or lanes of a scan (`gather`, `pick`, `spread`, `scatter`), and
facts about bytes in 32-bit registers and about the memory around the table
that their proofs share.
-/

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

theorem byte32 (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The doubleword holding byte `n`, once doublewords `0, …, k - 1` are visited. -/
def gather (m : Mem) (p : Addr) (n k : Nat) : BitVec 32 :=
  if n / 4 < k then m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 else 0

theorem gather_succ (m : Mem) (p : Addr) (n k : Nat) :
    VG.Proof.Rc4.gather m p n k ||| (if n / 4 = k then m.readW (p + BitVec.ofNat 64 (4 * k)) 32 else 0) =
      VG.Proof.Rc4.gather m p n (k + 1) := by
  unfold VG.Proof.Rc4.gather
  by_cases h0 : n / 4 < k
  · simp [h0, show ¬ n / 4 = k by omega, show n / 4 < k + 1 by omega]
  · by_cases h1 : n / 4 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 4 < k + 1 by omega]

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The doubleword shifted to byte `L`, once bytes `0, …, j - 1` are visited. -/
def pick (q : BitVec 32) (L j : Nat) : BitVec 32 := if L < j then q >>> (8 * L) else 0

theorem pick_succ (q : BitVec 32) (L j : Nat) :
    VG.Proof.Rc4.pick q L j ||| (if L = j then q >>> (8 * j) else 0) = VG.Proof.Rc4.pick q L (j + 1) := by
  unfold VG.Proof.Rc4.pick
  by_cases h0 : L < j
  · simp [h0, show ¬ L = j by omega, show L < j + 1 by omega]
  · by_cases h1 : L = j
    · subst h1; simp
    · simp [h0, h1, show ¬ L < j + 1 by omega]

/-- The difference `c`, once lanes `3, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 32 :=
  if jj ≤ L then (c.setWidth 32) <<< (8 * (L - jj)) else 0

theorem zero_xor' (x : BitVec 32) : (0 : BitVec 32) ^^^ x = x := BitVec.zero_xor
theorem or_zero' (x : BitVec 32) : x ||| (0 : BitVec 32) = x := BitVec.or_zero
theorem zero_or' (x : BitVec 32) : (0 : BitVec 32) ||| x = x := BitVec.zero_or
theorem rot_zero : (0 : BitVec 32).rotateRight 24 = 0 := by decide

theorem spread_succ (c : Byte) {L j : Nat} (hL : L < 4) :
    (VG.Proof.Rc4.spread c L (j + 1)).rotateRight 24 ||| (if L = j then c.setWidth 32 else 0) =
      VG.Proof.Rc4.spread c L j := by
  unfold VG.Proof.Rc4.spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, VG.Proof.Rc4.rot_byte32 c (by omega), ite_eq_right (show ¬ L = j by omega),
      VG.Proof.Rc4.or_zero', ite_eq_left (show j ≤ L by omega), show L - (j + 1) + 1 = L - j by omega]
  · rw [ite_eq_right h1, VG.Proof.Rc4.rot_zero, VG.Proof.Rc4.zero_or']
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega)]

/-- The memory once doublewords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 32) (k : Nat) : Mem :=
  if n / 4 < k then
    m.writeW (p + BitVec.ofNat 64 (4 * (n / 4)))
      (m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 32) (k : Nat) :
    (VG.Proof.Rc4.scatter m p n d k).writeW (p + BitVec.ofNat 64 (4 * k))
      ((if n / 4 = k then d else 0) ^^^
        (VG.Proof.Rc4.scatter m p n d k).readW (p + BitVec.ofNat 64 (4 * k)) 32) = VG.Proof.Rc4.scatter m p n d (k + 1) := by
  unfold VG.Proof.Rc4.scatter
  by_cases h0 : n / 4 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 4 = k by omega), VG.Proof.Rc4.zero_xor', VG.Proof.Rc4.writeW_readW32,
      ite_eq_left (show n / 4 < k + 1 by omega)]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 4 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 4 < k + 1 by omega), BitVec.xor_comm, h1]
    · rw [ite_eq_right h1, VG.Proof.Rc4.zero_xor', VG.Proof.Rc4.writeW_readW32,
        ite_eq_right (show ¬ n / 4 < k + 1 by omega)]

theorem xor_byte32 (a b : Byte) : a.setWidth 32 ^^^ b.setWidth 32 = (a ^^^ b).setWidth 32 := by
  rw [BitVec.setWidth_xor]

theorem writeW_byte8 (m : Mem) (a : Addr) (v : Byte) : m.writeW a v = m.write a 1 v := by
  change m.write a 1 (v.setWidth 8) = _
  rw [BitVec.setWidth_eq]

theorem low_byte32 (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low32 (r : Nat) : (BitVec.ofNat 32 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mask255_32 (x : BitVec 32) : x &&& BitVec.ofNat 32 255 = (x.setWidth 8).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 32 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_add32 (a b : Byte) :
    a.setWidth 32 + b.setWidth 32 &&& BitVec.ofNat 32 255 = (a + b).setWidth 32 := by
  rw [VG.Proof.Rc4.mask255_32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem byte_add3_32 (j a k : Byte) :
    j.setWidth 32 + a.setWidth 32 + k.setWidth 32 &&& BitVec.ofNat 32 255 =
      (j + a + k).setWidth 32 := by
  rw [VG.Proof.Rc4.mask255_32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

/-- A word outside the table is unchanged by writes within the table. -/
theorem table_frame_readW {p a : Addr} {m m' : Mem} (h : VG.Proof.Rc4.TableFrame p m m')
    (hs : Mem.Sep a 4 p 256) : m'.readW a 32 = m.readW a 32 :=
  Mem.readW_congr fun i hi => h _ (hs _ (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi))

/-- The key offset after `r`, advanced: back to 0 at the key length. -/
theorem key_next32 (r len : Nat) (hl : 0 < len) (hlen : len ≤ 256) :
    (if (BitVec.ofNat 32 (r % len) + 1#32).toNat < len then BitVec.ofNat 32 (r % len) + 1#32
      else 0#32) = BitVec.ofNat 32 ((r + 1) % len) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 32 (r % len) + 1#32).toNat = r % len + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len < 2 ^ 32 by omega)]
    change (r % len + 1) % 2 ^ 32 = _
    omega
  rw [ht]
  have ha : (r + 1) % len = (r % len + 1) % len := by
    simp only [Nat.add_mod, Nat.mod_mod]
  by_cases h : r % len + 1 < len
  · rw [ite_eq_left h]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len + 1 < 2 ^ 32 by omega)]
  · rw [ite_eq_right h, ha, show r % len + 1 = len by omega, Nat.mod_self]

theorem byte_inc32 (i : Byte) :
    i.setWidth 32 + BitVec.ofNat 32 1 &&& BitVec.ofNat 32 255 = (i + 1#8).setWidth 32 := by
  have h := VG.Proof.Rc4.byte_add32 i 1#8
  rwa [show (1#8).setWidth 32 = BitVec.ofNat 32 1 from rfl] at h

theorem low_xor32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  rw [VG.Proof.Rc4.xor_byte32, VG.Proof.Rc4.low_byte32]

/-- A word apart from two byte writes. -/
theorem readW_write2 {m : Mem} {a q₁ q₂ : Addr} {v₁ v₂ : Byte} (h₁ : Mem.Sep a 4 q₁ 1)
    (h₂ : Mem.Sep a 4 q₂ 1) : ((m.write q₁ 1 v₁).write q₂ 1 v₂).readW a 32 = m.readW a 32 := by
  simp only [Mem.readW, Nat.reduceDiv]
  rw [Mem.read_write_sep h₂ (by decide), Mem.read_write_sep h₁ (by decide)]

theorem readW_write1 {m : Mem} {a q : Addr} {v : Byte} (h : Mem.Sep a 4 q 1) :
    (m.write q 1 v).readW a 32 = m.readW a 32 := by
  simp only [Mem.readW, Nat.reduceDiv]
  rw [Mem.read_write_sep h (by decide)]

theorem sep_of_sub {R₁ R₂ : Region} (h : R₁.Disjoint R₂) {a b : Addr} {n k : Nat}
    (h₁ : R₁.Contains a n) (h₂ : R₂.Contains b k) : Mem.Sep a n b k :=
  fun x hx hy => h x (h₁.byte hx) (h₂.byte hy)

theorem contains_prefix (p : Addr) {n k : Nat} (h : n ≤ k) : (⟨p, k⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
  exact h

theorem data_ne {D : BitVec 32} {L : BitVec 32} {x k : Nat}
    (hx : x < L.toNat) (hk : k < L.toNat) (hne : x ≠ k) :
    D.setWidth 64 + BitVec.ofNat 64 x ≠ D.setWidth 64 + BitVec.ofNat 64 k := by
  intro h
  have h' := congrArg (fun y => (y - D.setWidth 64).toNat) h
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  exact hne h'

/-- The context is unchanged by writes outside its 258 bytes. -/
theorem contextAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 258⟩ r) : contextAt m' p = contextAt m p := by
  have e (i : Nat) (hi : i < 258) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
    hf.bytes (R := ⟨p, 258⟩) hd (show (258 : Nat) ≤ 2 ^ 64 by decide) hi
  apply VG.Proof.Rc4.context_ext
  · apply Vector.ext
    intro k hk
    simp only [contextAt, Vector.getElem_ofFn]
    exact e k (by omega)
  · exact e 256 (by decide)
  · exact e 257 (by decide)

theorem frame_of_table {p : Addr} {m m' : Mem} (h : VG.Proof.Rc4.TableFrame p m m') :
    Frame [⟨p, 258⟩] m m' := fun x hx =>
  h x fun hlt => hx ⟨p, 258⟩ List.mem_cons_self (by simp only [Region.Contains]; omega)

theorem frame_finish {p : Addr} {m m' : Mem} (h : Frame [⟨p, 258⟩] m m') (a b : Byte) :
    Frame [⟨p, 258⟩] m ((m'.write (p + 256#64) 1 a).write (p + 257#64) 1 b) :=
  (h.write List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).write
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

/-- The low word of a 64-bit return value. -/
theorem ret_low (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt,
    Nat.shiftLeft_eq]
  have := b.isLt
  omega

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Schedule`. -/
section

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- A proof-oriented view of the specification's sequential scheduling loop. -/
def scheduleRound (key : List Byte) (st : Table × Byte) (i : Nat) : Table × Byte :=
  let j := st.2 + st.1.getD i 0 + key.getD (i % key.length) 0
  (swap st.1 (BitVec.ofNat 8 i) j, j)

def schedulePrefix (key : List Byte) (r : Nat) : Table × Byte :=
  (List.range r).foldl (VG.Proof.Rc4.scheduleRound key)
    (Vector.ofFn (fun i => BitVec.ofNat 8 i.val), 0)

theorem schedule_zero (key : List Byte) :
    VG.Proof.Rc4.schedulePrefix key 0 = (Vector.ofFn (fun i => BitVec.ofNat 8 i.val), 0) := rfl

theorem schedule_succ (key : List Byte) (r : Nat) :
    VG.Proof.Rc4.schedulePrefix key (r + 1) = VG.Proof.Rc4.scheduleRound key (VG.Proof.Rc4.schedulePrefix key r) r := by
  unfold VG.Proof.Rc4.schedulePrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem keySchedule_eq (key : List Byte) : keySchedule key = (VG.Proof.Rc4.schedulePrefix key 256).1 := by
  unfold keySchedule VG.Proof.Rc4.schedulePrefix VG.Proof.Rc4.scheduleRound
  simp only [List.forIn_pure_yield_eq_foldl]
  rfl

end VG.Proof.Rc4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.Update`. -/
section

/-! # RC4: the stream, one byte more at a time -/

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- `update` over one more byte: the PRGA step after the context the others leave. -/
theorem update_snoc (c : Context) (xs : List Byte) (x : Byte) :
    update c (xs ++ [x]) =
      ((step (update c xs).1).1, (update c xs).2 ++ [x ^^^ (step (update c xs).1).2]) := by
  induction xs generalizing c with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.cons_append, update, ih]

theorem bytes_snoc (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = bytesAt m p n ++ [m (p + BitVec.ofNat 64 n)] := by
  simp only [bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- A write outside the table leaves its abstract permutation unchanged. -/
theorem table_write_sep' (m : Mem) (p q : Addr) {n : Nat} (v : BitVec (8 * n))
    (h : Mem.Sep p 256 q n) :
    (contextAt (m.write q n v) p).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  apply Mem.write_apply
  exact h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hk)

theorem bytes_frame (m m' : Mem) (d : Addr) (n : Nat)
    (h : ∀ k < n, m' (d + BitVec.ofNat 64 k) = m (d + BitVec.ofNat 64 k)) :
    bytesAt m' d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro k hk
  exact h k (List.mem_range.mp hk)

end VG.Proof.Rc4

end
