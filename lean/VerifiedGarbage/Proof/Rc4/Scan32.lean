import VerifiedGarbage.Proof.Rc4.Dword

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
    gather m p n k ||| (if n / 4 = k then m.readW (p + BitVec.ofNat 64 (4 * k)) 32 else 0) =
      gather m p n (k + 1) := by
  unfold gather
  by_cases h0 : n / 4 < k
  · simp [h0, show ¬ n / 4 = k by omega_arith, show n / 4 < k + 1 by omega_arith]
  · by_cases h1 : n / 4 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 4 < k + 1 by omega_arith]

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The doubleword shifted to byte `L`, once bytes `0, …, j - 1` are visited. -/
def pick (q : BitVec 32) (L j : Nat) : BitVec 32 := if L < j then q >>> (8 * L) else 0

theorem pick_succ (q : BitVec 32) (L j : Nat) :
    pick q L j ||| (if L = j then q >>> (8 * j) else 0) = pick q L (j + 1) := by
  unfold pick
  by_cases h0 : L < j
  · simp [h0, show ¬ L = j by omega_arith, show L < j + 1 by omega_arith]
  · by_cases h1 : L = j
    · subst h1; simp
    · simp [h0, h1, show ¬ L < j + 1 by omega_arith]

/-- The difference `c`, once lanes `3, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 32 :=
  if jj ≤ L then (c.setWidth 32) <<< (8 * (L - jj)) else 0

theorem zero_xor' (x : BitVec 32) : (0 : BitVec 32) ^^^ x = x := BitVec.zero_xor
theorem or_zero' (x : BitVec 32) : x ||| (0 : BitVec 32) = x := BitVec.or_zero
theorem zero_or' (x : BitVec 32) : (0 : BitVec 32) ||| x = x := BitVec.zero_or
theorem rot_zero : (0 : BitVec 32).rotateRight 24 = 0 := by decide

theorem spread_succ (c : Byte) {L j : Nat} (hL : L < 4) :
    (spread c L (j + 1)).rotateRight 24 ||| (if L = j then c.setWidth 32 else 0) =
      spread c L j := by
  unfold spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, rot_byte32 c (by omega_arith), ite_eq_right (show ¬ L = j by omega_arith),
      or_zero', ite_eq_left (show j ≤ L by omega_arith), show L - (j + 1) + 1 = L - j by omega_arith]
  · rw [ite_eq_right h1, rot_zero, zero_or']
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega_arith), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega_arith)]

/-- The memory once doublewords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 32) (k : Nat) : Mem :=
  if n / 4 < k then
    m.writeW (p + BitVec.ofNat 64 (4 * (n / 4)))
      (m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 32) (k : Nat) :
    (scatter m p n d k).writeW (p + BitVec.ofNat 64 (4 * k))
      ((if n / 4 = k then d else 0) ^^^
        (scatter m p n d k).readW (p + BitVec.ofNat 64 (4 * k)) 32) = scatter m p n d (k + 1) := by
  unfold scatter
  by_cases h0 : n / 4 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 4 = k by omega_arith), zero_xor', writeW_readW32,
      ite_eq_left (show n / 4 < k + 1 by omega_arith)]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 4 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 4 < k + 1 by omega_arith), BitVec.xor_comm, h1]
    · rw [ite_eq_right h1, zero_xor', writeW_readW32,
        ite_eq_right (show ¬ n / 4 < k + 1 by omega_arith)]

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
  omega_arith

theorem mask255_32 (x : BitVec 32) : x &&& BitVec.ofNat 32 255 = (x.setWidth 8).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 32 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem byte_add32 (a b : Byte) :
    a.setWidth 32 + b.setWidth 32 &&& BitVec.ofNat 32 255 = (a + b).setWidth 32 := by
  rw [mask255_32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_arith

theorem byte_add3_32 (j a k : Byte) :
    j.setWidth 32 + a.setWidth 32 + k.setWidth 32 &&& BitVec.ofNat 32 255 =
      (j + a + k).setWidth 32 := by
  rw [mask255_32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_arith

/-- A word outside the table is unchanged by writes within the table. -/
theorem table_frame_readW {p a : Addr} {m m' : Mem} (h : TableFrame p m m')
    (hs : Mem.Sep a 4 p 256) : m'.readW a 32 = m.readW a 32 :=
  Mem.readW_congr fun i hi => h _ (hs _ (by rw [Mem.sub_ofNat_toNat a (by omega_arith)]; exact hi))

/-- The key offset after `r`, advanced: back to 0 at the key length. -/
theorem key_next32 (r len : Nat) (hl : 0 < len) (hlen : len ≤ 256) :
    (if (BitVec.ofNat 32 (r % len) + 1#32).toNat < len then BitVec.ofNat 32 (r % len) + 1#32
      else 0#32) = BitVec.ofNat 32 ((r + 1) % len) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 32 (r % len) + 1#32).toNat = r % len + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len < 2 ^ 32 by omega_arith)]
    change (r % len + 1) % 2 ^ 32 = _
    omega_arith
  rw [ht]
  have ha : (r + 1) % len = (r % len + 1) % len := by
    simp only [Nat.add_mod, Nat.mod_mod]
  by_cases h : r % len + 1 < len
  · rw [ite_eq_left h]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len + 1 < 2 ^ 32 by omega_arith)]
  · rw [ite_eq_right h, ha, show r % len + 1 = len by omega_arith, Nat.mod_self]

theorem byte_inc32 (i : Byte) :
    i.setWidth 32 + BitVec.ofNat 32 1 &&& BitVec.ofNat 32 255 = (i + 1#8).setWidth 32 := by
  have h := byte_add32 i 1#8
  rwa [show (1#8).setWidth 32 = BitVec.ofNat 32 1 from rfl] at h

theorem low_xor32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  rw [xor_byte32, low_byte32]

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
  rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)] at h'
  exact hne h'

/-- The context is unchanged by writes outside its 258 bytes. -/
theorem contextAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 258⟩ r) : contextAt m' p = contextAt m p := by
  have e (i : Nat) (hi : i < 258) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
    hf.bytes (R := ⟨p, 258⟩) hd (show (258 : Nat) ≤ 2 ^ 64 by decide) hi
  apply context_ext
  · apply Vector.ext
    intro k hk
    simp only [contextAt, Vector.getElem_ofFn]
    exact e k (by omega_arith)
  · exact e 256 (by decide)
  · exact e 257 (by decide)

theorem frame_of_table {p : Addr} {m m' : Mem} (h : TableFrame p m m') :
    Frame [⟨p, 258⟩] m m' := fun x hx =>
  h x fun hlt => hx ⟨p, 258⟩ List.mem_cons_self (by simp only [Region.Contains]; omega_arith)

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
  omega_arith

end VG.Proof.Rc4
