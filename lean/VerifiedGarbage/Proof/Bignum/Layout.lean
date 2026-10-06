import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Multiword arithmetic: the working space's layout

Target-independent facts about the working space of the RSA code
(`Impl/Bignum/Layout.lean`): its header (`Hdr`: `w`, `-m⁻¹ mod 2⁶⁴` and the
arrays' bases) and its eight arrays of `w + 2` words (`slot w j`), and the
memory that the pieces of code change: only some arrays (`Arrays`), only
some byte ranges (`Frm`, and the ranges each piece changes), only within the
working space (`InScr`), or not the header slots that hold the arguments
(`Fixed`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum VG.Impl.Bignum.Public

/-! ## The arrays and the header -/

/-- The offset of array `j`. -/
def slot (w j : Nat) : Nat := hdrBytes + j * (8 * (w + 2))

theorem slot_sep {w j k : Nat} (h : j ≠ k) :
    slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := by
  unfold slot
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · right
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show k + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

theorem slot_le {w j : Nat} (h : j < 8) : slot w j + 8 * (w + 2) ≤ slot w 8 := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 8 by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem hdr_lt_slot (w j : Nat) {i : Nat} (hi : i < 32) : 8 * i + 8 ≤ slot w j := by
  unfold slot hdrBytes; omega

/-- The header: `w`, `-m⁻¹` and the arrays' bases. -/
structure Hdr (m : Mem) (B : Addr) (w : Nat) (minv : BitVec 64) : Prop where
  hw : word m B (8 * sW) = BitVec.ofNat 64 w
  hminv : word m B (8 * sMinv) = minv
  harr : ∀ j < 8, word m B (8 * sArr j) = off B (slot w j)

/-! ## Memory that changes only in some arrays or ranges -/

/-- Memory that changes only in the arrays `js`. -/
def Arrays (B : Addr) (w : Nat) (js : List Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ j ∈ js, ofs B x < slot w j ∨ slot w j + 8 * (w + 2) ≤ ofs B x) → m' x = m x

theorem Arrays.of_outside {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} {j : Nat} (hj : j ∈ js)
    {o n : Nat} (h : Outside B o n m m') (ho : slot w j ≤ o) (hn : o + n ≤ slot w j + 8 * (w + 2)) :
    Arrays B w js m m' := fun x hx => h x (by have := hx j hj; omega)

theorem Arrays.trans {B : Addr} {w : Nat} {js : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Arrays B w js m₁ m₂) (h₂ : Arrays B w js m₂ m₃) : Arrays B w js m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Arrays.mono {B : Addr} {w : Nat} {js js' : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hs : ∀ j ∈ js, j ∈ js') : Arrays B w js' m m' := fun x hx => h x fun j hj => hx j (hs j hj)

theorem Arrays.word_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {d : Nat} (hd : ∀ j ∈ js, d + 8 ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun j hj => by
    have := hd j hj; rw [ofs_off B (by omega)]; omega).symm).symm

theorem Arrays.wv_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {d k : Nat} (hd : ∀ j ∈ js, d + 8 * k ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d)
    (hd' : d + 8 * k ≤ 2 ^ 64) : wv m' B d k = wv m B d k :=
  wv_congr fun i hi => h.word_eq (fun j hj => by have := hd j hj; omega) (by omega)

theorem Arrays.hdr {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {minv : BitVec 64} (hH : Hdr m B w minv) : Hdr m' B w minv := by
  have hh : ∀ i < 32, word m' B (8 * i) = word m B (8 * i) := fun i hi =>
    h.word_eq (fun j _ => Or.inl (hdr_lt_slot w j hi)) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- Memory that changes only in the byte ranges `rs` (offsets and lengths
from `B`). -/
def Frm (B : Addr) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) → m' x = m x

theorem Frm.refl (B : Addr) (rs : List (Nat × Nat)) (m : Mem) : Frm B rs m m := fun _ _ => rfl

theorem Frm.trans {B : Addr} {rs : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : Frm B rs m₁ m₂)
    (h₂ : Frm B rs m₂ m₃) : Frm B rs m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Frm.mono {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hs : ∀ r ∈ rs, r ∈ rs') : Frm B rs' m m' := fun x hx => h x fun r hr => hx r (hs r hr)

theorem Frm.of_outside {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {o n : Nat} (h : Outside B o n m m')
    (hr : (o, n) ∈ rs) : Frm B rs m m' := fun x hx => h x (hx _ hr)

theorem Frm.of_arrays {B : Addr} {w : Nat} {js : List Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Arrays B w js m m') (hr : ∀ j ∈ js, (slot w j, 8 * (w + 2)) ∈ rs) : Frm B rs m m' :=
  fun x hx => h x fun j hj => hx _ (hr j hj)

theorem Frm.word_eq {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun r hr => by
    have := hd r hr; rw [ofs_off B (by omega)]; omega).symm).symm

theorem Frm.wv_eq {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {d k : Nat}
    (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    wv m' B d k = wv m B d k :=
  wv_congr fun i hi => h.word_eq (fun r hr => by have := hd r hr; omega) (by omega)

/-- The header, after a store to a slot of the functions' own (`sFn`). -/
theorem Hdr.store {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv) {i : Nat}
    (hi : 16 ≤ i) (hi' : i < 32) (v : BitVec 64) : Hdr (m.writeW (off B (8 * i)) v) B w minv := by
  have hh : ∀ k < 16, word (m.writeW (off B (8 * i)) v) B (8 * k) = word m B (8 * k) := fun k hk =>
    (writeW_outside m B v (by omega)).word (by omega) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-! ## Memory within the working space, and the arguments in the header -/

/-- Memory that changes only in the working space. -/
def InScr (B : Addr) (Z : Nat) (m m' : Mem) : Prop := ∀ x, Z ≤ ofs B x → m' x = m x

theorem InScr.refl (B : Addr) (Z : Nat) (m : Mem) : InScr B Z m m := fun _ _ => rfl

theorem InScr.trans {B : Addr} {Z : Nat} {m₁ m₂ m₃ : Mem} (h₁ : InScr B Z m₁ m₂) (h₂ : InScr B Z m₂ m₃) :
    InScr B Z m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem InScr.of_outside {B : Addr} {Z o n : Nat} {m m' : Mem} (h : Outside B o n m m') (hZ : o + n ≤ Z) :
    InScr B Z m m' := fun x hx => h x (Or.inr (by omega))

theorem InScr.of_frm {B : Addr} {Z : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : InScr B Z m m' :=
  fun x hx => h x fun r hr => Or.inr (by have := hZ r hr; omega)

theorem InScr.of_arrays {B : Addr} {Z w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hZ : slot w 8 ≤ Z) (hjs : ∀ j ∈ js, j < 8) : InScr B Z m m' :=
  fun x hx => h x fun j hj => Or.inr (by have := slot_le (w := w) (hjs j hj); omega)

/-- The header slots read on exit and by the setup: the saved registers and
the arguments. -/
def Fixed (B : Addr) (m m' : Mem) : Prop :=
  ∀ i, i < 6 ∨ (16 ≤ i ∧ i < 22) → word m' B (8 * i) = word m B (8 * i)

theorem Fixed.refl (B : Addr) (m : Mem) : Fixed B m m := fun _ _ => rfl

theorem Fixed.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Fixed B m₁ m₂) (h₂ : Fixed B m₂ m₃) :
    Fixed B m₁ m₃ := fun i hi => (h₂ i hi).trans (h₁ i hi)

theorem Fixed.of_outside {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m')
    (ho : 8 * 22 ≤ o ∨ (8 * 6 ≤ o ∧ o + n ≤ 8 * 16)) : Fixed B m m' :=
  fun _ hi => h.word (by omega) (by omega)

theorem Fixed.of_frm {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (ho : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16)) : Fixed B m m' :=
  fun _ hi => h.word_eq (fun r hr => by have := ho r hr; omega) (by omega)

theorem Fixed.of_arrays {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') :
    Fixed B m m' :=
  fun i hi => h.word_eq (fun j _ => Or.inl (by have := hdr_lt_slot w j (show i < 32 by omega); omega))
    (by omega)

theorem Fixed.store (m : Mem) (B : Addr) {i : Nat} (v : BitVec 64) (hi : 6 ≤ i) (hi' : i < 32)
    (hi'' : i < 16 ∨ 22 ≤ i) : Fixed B m (m.writeW (off B (8 * i)) v) :=
  Fixed.of_outside (writeW_outside m B v (by omega)) (by omega)

/-! ## What the pieces of the public-key operations change -/

/-- What the loads change. -/
def loadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (slot w aX, 8 * (w + 2))]

theorem Frm.of_arrays1 {B : Addr} {w j : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Arrays B w [j] m m')
    (hr : (slot w j, 8 * (w + 2)) ∈ rs) : Frm B rs m m' :=
  Frm.of_arrays h fun _ hj => (List.mem_singleton.mp hj) ▸ hr

/-- What the setup changes. -/
def setupRanges (w : Nat) : List (Nat × Nat) :=
  loadRanges w ++ [(8 * sMinv, 8), (8 * sMask, 8), (slot w aOne, 8 * (w + 2))]

/-- What a bit of the exponentiation changes: arrays and header slots. -/
def bitRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (8 * sV, 8),
    (8 * sBit, 8)]

/-- What the exponentiation changes: also the byte index. -/
def expRanges (w : Nat) : List (Nat × Nat) := (8 * sI, 8) :: bitRanges w

/-- An array that `Arrays` does not list keeps its value. -/
theorem Arrays.wv_of_not_mem {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {j : Nat} (hj : j < 8) (hn : j ∉ js) (hZ : B.toNat + slot w 8 ≤ 2 ^ 64) :
    wv m' B (slot w j) w = wv m B (slot w j) w :=
  h.wv_eq (fun k hk => by
    have := slot_sep (w := w) (show j ≠ k from fun e => hn (e ▸ hk)); omega)
    (by have := slot_le (w := w) hj; omega)

theorem Arrays.word0_of_not_mem {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {j : Nat} (hj : j < 8) (hn : j ∉ js) (hZ : B.toNat + slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) :
    word m' B (slot w j) = word m B (slot w j) :=
  h.word_eq (fun k hk => by
    have := slot_sep (w := w) (show j ≠ k from fun e => hn (e ▸ hk)); omega)
    (by have := slot_le (w := w) hj; omega)

theorem Arrays.hslot {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {i : Nat}
    (hi : i < 32) : word m' B (8 * i) = word m B (8 * i) :=
  h.word_eq (fun j _ => Or.inl (hdr_lt_slot w j hi)) (by omega)

theorem bit_step {v tb : Nat} (htb : tb < 8) :
    2 * (v / 2 ^ (8 - tb)) + v * 2 ^ tb / 128 % 2 = v / 2 ^ (7 - tb) := by
  have h1 : v * 2 ^ tb / 128 = v / 2 ^ (7 - tb) := by
    rw [show (128 : Nat) = 2 ^ tb * 2 ^ (7 - tb) by rw [← Nat.pow_add, show tb + (7 - tb) = 7 by omega],
      Nat.mul_comm v, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
  rw [h1, show 8 - tb = (7 - tb) + 1 by omega, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- A store to a header slot keeps the arrays. -/
theorem hdrStore_wv (m : Mem) (B : Addr) {w i j : Nat} (v : BitVec 64) (hi : i < 32) (hj : j < 8)
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    wv (m.writeW (off B (8 * i)) v) B (slot w j) w = wv m B (slot w j) w :=
  (writeW_outside m B v (by omega)).wv (by have := hdr_lt_slot w j hi; omega)
    (by have := slot_le (w := w) hj; omega)

theorem hdrStore_word (m : Mem) (B : Addr) {w i j : Nat} (v : BitVec 64) (hi : i < 32) (hj : j < 8)
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    word (m.writeW (off B (8 * i)) v) B (slot w j) = word m B (slot w j) :=
  (writeW_outside m B v (by omega)).word (by have := hdr_lt_slot w j hi; omega)
    (by have := slot_le (w := w) hj; omega)

/-- Another header slot. -/
theorem hdrStore_hdr (m : Mem) (B : Addr) {i k : Nat} (v : BitVec 64) (hi : i < 32) (hk : k < 32)
    (hik : i ≠ k) : word (m.writeW (off B (8 * i)) v) B (8 * k) = word m B (8 * k) :=
  (writeW_outside m B v (by omega)).word (by omega) (by omega)

theorem expRanges_le (w : Nat) : ∀ r ∈ expRanges w, r.1 + r.2 ≤ slot w 8 := by
  have h := hdr_lt_slot w 0 (i := sBit) (by decide)
  have h1 := slot_le (w := w) (show aAcc < 8 by decide)
  have h2 := slot_le (w := w) (show aTmp < 8 by decide)
  have h3 := slot_le (w := w) (show aY < 8 by decide)
  have h4 : slot w 0 ≤ slot w aAcc := by unfold slot; omega
  simp only [expRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sI, sV, sBit, sFn] at * <;> omega

theorem bitRanges_sub (w : Nat) : ∀ r ∈ bitRanges w, r ∈ expRanges w :=
  fun _ hr => List.mem_cons_of_mem _ hr

/-- A header slot that a bit of the exponentiation does not change. -/
theorem bitRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ sV) (h2 : k ≠ sBit) :
    ∀ r ∈ bitRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have h := hdr_lt_slot w aAcc hk
  have h' := hdr_lt_slot w aTmp hk
  have h'' := hdr_lt_slot w aY hk
  simp only [bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [sV, sBit, sFn] at * <;> omega

theorem expRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ sI) (h1 : k ≠ sV) (h2 : k ≠ sBit) :
    ∀ r ∈ expRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [sI, sFn] at *; omega
  · exact bitRanges_hdr w hk h1 h2 r hr

/-- What `R² mod m` changes. -/
def r2Ranges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aR2, 8 * (w + 2)), (8 * sCnt, 8)]

/-- The start, `2^(b - 1)` for the bit length `b` of the odd `N`, is below
it. -/
theorem start_lt {N T L w : Nat} (hw : 2 ≤ w) (hodd : N % 2 = 1)
    (hT : N = N % 2 ^ (64 * (w - 1)) + 2 ^ (64 * (w - 1)) * T) (hL : 2 ^ L ≤ T) :
    2 ^ L * 2 ^ (64 * (w - 1)) < N := by
  have h1 : 2 ^ L * 2 ^ (64 * (w - 1)) ≤ 2 ^ (64 * (w - 1)) * T := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hL
  rcases Nat.lt_or_ge (2 ^ L * 2 ^ (64 * (w - 1))) N with h | h
  · exact h
  · exfalso
    have he : N = 2 ^ L * 2 ^ (64 * (w - 1)) := by omega
    have : 2 ^ L * 2 ^ (64 * (w - 1)) % 2 = 0 := by
      rw [show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]
    omega

theorem r2Ranges_arr (w : Nat) {j : Nat} (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    ∀ r ∈ r2Ranges w, slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  have := hdr_lt_slot w j (show sCnt < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> omega

theorem r2Ranges_hdr (w : Nat) {i : Nat} (hi : i < 32) (h : i ≠ sCnt) :
    ∀ r ∈ r2Ranges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  have := hdr_lt_slot w aAcc hi
  have := hdr_lt_slot w aTmp hi
  have := hdr_lt_slot w aR2 hi
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCnt, sFn] at * <;> omega

theorem r2Ranges_le (w : Nat) : ∀ r ∈ r2Ranges w, r.1 + r.2 ≤ slot w 8 := by
  have := slot_le (w := w) (show aAcc < 8 by decide)
  have := slot_le (w := w) (show aTmp < 8 by decide)
  have := slot_le (w := w) (show aR2 < 8 by decide)
  have := hdr_lt_slot w 0 (show sCnt < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> omega

theorem Frm.r2_wv {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (r2Ranges w) m m')
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    wv m' B (slot w j) w = wv m B (slot w j) w :=
  h.wv_eq (fun r hr => by have := r2Ranges_arr w h1 h2 h3 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem Frm.r2_word {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (r2Ranges w) m m')
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    word m' B (slot w j) = word m B (slot w j) :=
  h.word_eq (fun r hr => by have := r2Ranges_arr w h1 h2 h3 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem pow_r2 {L w : Nat} (hL : L < 64) (hw : 1 ≤ w) :
    2 ^ (64 - L + w) * (2 ^ L * 2 ^ (64 * (w - 1))) = 2 ^ w * 2 ^ (64 * w) := by
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega

theorem setupRanges_le (w : Nat) : ∀ r ∈ setupRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  have := slot_le (w := w) (show aX < 8 by decide)
  have := slot_le (w := w) (show aOne < 8 by decide)
  simp only [setupRanges, loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv, sMask, sFn] at * <;> omega

theorem setupRanges_fixed (w : Nat) :
    ∀ r ∈ setupRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have h1 : slot w 0 ≤ slot w aN := by unfold slot; omega
  have h2 : slot w 0 ≤ slot w aX := by unfold slot; omega
  have h3 : slot w 0 ≤ slot w aOne := by unfold slot; omega
  simp only [setupRanges, loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv, sMask, sFn] at * <;> omega

theorem r2Ranges_fixed (w : Nat) : ∀ r ∈ r2Ranges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aR2 (show 31 < 32 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCnt, sFn] at * <;> omega

/-- What the load changes. -/
def pcLoadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (8 * sMinv, 8)]

theorem pcLoadRanges_fixed (w : Nat) :
    ∀ r ∈ pcLoadRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h1 : slot w 0 ≤ slot w aN := by unfold slot; omega
  simp only [pcLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv] at * <;> omega

theorem pcLoadRanges_le (w : Nat) : ∀ r ∈ pcLoadRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  simp only [pcLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv] at * <;> omega

/-- What a bit of the exponentiation changes: also whether it started. -/
def pBitRanges (w : Nat) : List (Nat × Nat) := (8 * sStarted, 8) :: bitRanges w

/-- What `start` changes. -/
def startRanges (w : Nat) : List (Nat × Nat) := [(slot w aY, 8 * (w + 2)), (8 * sStarted, 8)]

theorem startRanges_sub (w : Nat) : ∀ r ∈ startRanges w, r ∈ pBitRanges w := by
  simp [startRanges, pBitRanges, bitRanges]

/-! ## The exponentiation from precomputed values -/

/-- `Y` after the prefix `E` of `e`: unused, and not started, while `E = 0`;
started, and `x^E R` modulo `N`, after. -/
def YSt (m : Mem) (B : Addr) (w N x E : Nat) : Prop :=
  (E = 0 ∧ word m B (8 * sStarted) = 0) ∨
    (E ≠ 0 ∧ word m B (8 * sStarted) = 1 ∧
      ∃ Y, wv m B (slot w aY) w = Y ∧ Y < N ∧ Y % N = x ^ E * 2 ^ (64 * w) % N)

theorem YSt.started {m : Mem} {B : Addr} {w N x E : Nat} (h : YSt m B w N x E) :
    word m B (8 * sStarted) = if E = 0 then 0 else 1 := by
  rcases h with ⟨h0, hs⟩ | ⟨h0, hs, -⟩
  · rw [hs]; simp [h0]
  · rw [hs]; simp [h0]

theorem started_test (E : Nat) :
    ((if E = 0 then (0 : BitVec 64) else 1) &&& (if E = 0 then (0 : BitVec 64) else 1) == 0) =
      decide (E = 0) := by
  by_cases h : E = 0 <;> simp [h]

/-- `YSt` in memory with the same `Y` and the same flag. -/
theorem YSt.congr {m m' : Mem} {B : Addr} {w N x E : Nat} (h : YSt m B w N x E)
    (hs : word m' B (8 * sStarted) = word m B (8 * sStarted)) (hy : wv m' B (slot w aY) w = wv m B (slot w aY) w) :
    YSt m' B w N x E := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1, Y, h2, h3, h4⟩
  · exact .inl ⟨h0, hs.trans h1⟩
  · exact .inr ⟨h0, hs.trans h1, Y, hy.trans h2, h3, h4⟩

theorem pBitRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ sV) (h2 : k ≠ sBit) (h3 : k ≠ sStarted) :
    ∀ r ∈ pBitRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [sStarted, sFn] at *; omega
  · exact bitRanges_hdr w hk h1 h2 r hr

/-- What the exponentiation changes: also the byte index. -/
def pExpRanges (w : Nat) : List (Nat × Nat) := (8 * sI, 8) :: pBitRanges w

theorem pExpRanges_le (w : Nat) : ∀ r ∈ pExpRanges w, r.1 + r.2 ≤ slot w 8 := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot w 0 (i := sI) (by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot w 0 (i := sStarted) (by decide); have := slot_le (w := w) (show 0 < 8 by decide)
    omega
  · exact expRanges_le w r (List.mem_cons_of_mem _ hr)

theorem pExpRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ sI) (h1 : k ≠ sV) (h2 : k ≠ sBit)
    (h3 : k ≠ sStarted) : ∀ r ∈ pExpRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [sI, sFn] at *; omega
  · exact pBitRanges_hdr w hk h1 h2 h3 r hr

theorem pBitRanges_sub (w : Nat) : ∀ r ∈ pBitRanges w, r ∈ pExpRanges w :=
  fun _ hr => List.mem_cons_of_mem _ hr

/-- What `finish` changes. -/
def finRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]


/-- What the load changes. -/
def pdLoadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (slot w aR2, 8 * (w + 2))]

theorem pdLoadRanges_le (w : Nat) : ∀ r ∈ pdLoadRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  have := slot_le (w := w) (show aR2 < 8 by decide)
  simp only [pdLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr] at * <;> omega

theorem pdLoadRanges_fixed (w : Nat) :
    ∀ r ∈ pdLoadRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h1 : slot w 0 ≤ slot w aN := by unfold slot; omega
  have h2 : slot w 0 ≤ slot w aR2 := by unfold slot; omega
  simp only [pdLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr] at * <;> omega

/-- What `rest` changes. -/
def pdAll (w : Nat) : List (Nat × Nat) :=
  [(slot w aX, 8 * (w + 2)), (8 * sMinv, 8), (8 * sMask, 8), (slot w aOne, 8 * (w + 2)),
    (slot w aXm, 8 * (w + 2))] ++ pExpRanges w

theorem pdAll_le (w : Nat) : ∀ r ∈ pdAll w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have := slot_le (w := w) (show aX < 8 by decide)
  have := slot_le (w := w) (show aOne < 8 by decide)
  have := slot_le (w := w) (show aXm < 8 by decide)
  have := slot_le (w := w) (show aAcc < 8 by decide)
  have := slot_le (w := w) (show aTmp < 8 by decide)
  have := slot_le (w := w) (show aY < 8 by decide)
  simp only [pdAll, pExpRanges, pBitRanges, bitRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sMinv, sMask, sI, sV, sBit, sStarted, sFn] at * <;> omega

theorem pdAll_fixed (w : Nat) : ∀ r ∈ pdAll w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aX (show 31 < 32 by decide)
  have := hdr_lt_slot w aOne (show 31 < 32 by decide)
  have := hdr_lt_slot w aXm (show 31 < 32 by decide)
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aY (show 31 < 32 by decide)
  simp only [pdAll, pExpRanges, pBitRanges, bitRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sMinv, sMask, sI, sV, sBit, sStarted, sFn] at * <;> omega

/-! ## The checks of precomputed values -/

/-- The checks pass for the values of a valid modulus. -/
theorem checks_true {m : Mem} {B : Addr} {w N : Nat} (hw : 1 ≤ w) (hN : wv m B (slot w aN) w = N)
    (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) (hRN : wv m B (slot w aR2) w < N) :
    (decide ((word m B (slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (slot w aR2) w < wv m B (slot w aN) w) &&
      decide (word m B (slot w aN + 8 * (w - 1)) ≠ 0)) = true := by
  have h1 : (word m B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide), hN, hodd]
  have h3 : word m B (slot w aN + 8 * (w - 1)) ≠ 0 := by
    intro h0
    have h := word_of_wv m B (slot w aN) w (q := w - 1) (by omega)
    rw [h0, hN, show (0 : BitVec 64).toNat = 0 from rfl] at h
    have hlt := wv_lt m B (slot w aN) w
    rw [hN] at hlt
    have hp : 0 < 2 ^ (64 * (w - 1)) := Nat.two_pow_pos _
    have hq : N / 2 ^ (64 * (w - 1)) < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul hp, ← Nat.pow_add, show 64 + 64 * (w - 1) = 64 * w by omega]; exact hlt
    have hq1 : 1 ≤ N / 2 ^ (64 * (w - 1)) := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    rw [Nat.mod_eq_of_lt hq] at h
    omega
  rw [hN]
  simp only [h1, hRN, decide_true, Bool.and_true, Bool.true_and, decide_eq_true_eq]
  exact h3

/-- What values that pass the checks give: an odd `N > 1`, and `R < N`. -/
theorem checks_facts {m : Mem} {B : Addr} {w : Nat} (hw : 2 ≤ w)
    (h : (decide ((word m B (slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (slot w aR2) w < wv m B (slot w aN) w) &&
      decide (word m B (slot w aN + 8 * (w - 1)) ≠ 0)) = true) :
    wv m B (slot w aN) w % 2 = 1 ∧ 1 < wv m B (slot w aN) w ∧ wv m B (slot w aR2) w < wv m B (slot w aN) w := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), wv_mod64 _ _ _ (by omega)]; exact h1, ?_, h2⟩
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h3
  have ht : (word m B (slot (v + 1) aN + 8 * v)).toNat ≠ 0 := fun h0 => h3 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  have hp : 1 < 2 ^ (64 * v) := Nat.one_lt_two_pow (by omega)
  rw [wv]
  have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * (word m B (slot (v + 1) aN + 8 * v)).toNat :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The checks' result, from the numbers in the arrays. -/
def chkv (w N R : Nat) : Bool :=
  decide (N % 2 = 1) && decide (R < N) && decide (N / 2 ^ (64 * (w - 1)) % 2 ^ 64 ≠ 0)

theorem chk_eq {m : Mem} {B : Addr} {w : Nat} (hw : 1 ≤ w) :
    (decide ((word m B (slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (slot w aR2) w < wv m B (slot w aN) w) &&
      decide (word m B (slot w aN + 8 * (w - 1)) ≠ 0)) =
      chkv w (wv m B (slot w aN) w) (wv m B (slot w aR2) w) := by
  have h1 : (word m B (slot w aN)).toNat % 2 = wv m B (slot w aN) w % 2 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide)]
  have h3 : word m B (slot w aN + 8 * (w - 1)) ≠ 0 ↔ wv m B (slot w aN) w / 2 ^ (64 * (w - 1)) % 2 ^ 64 ≠ 0 := by
    rw [← word_of_wv m B _ w (q := w - 1) (by omega)]
    exact ⟨fun h h0 => h (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)), fun h h0 => h (by rw [h0]; rfl)⟩
  unfold chkv
  rw [h1, decide_eq_decide.mpr h3]

end VG.Proof.Bignum
