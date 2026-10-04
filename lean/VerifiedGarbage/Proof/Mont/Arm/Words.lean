import VerifiedGarbage.Impl.Mont.Arm
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr

/-!
# Montgomery arithmetic on 32-bit ARM: words and digits in the working space

The working space is `size` bytes at `base`, whose low 32 bits `r12` holds
(`Scr`), below `2³²` and at most 4096 bytes, so that every offset in it is an
immediate offset of `ldr` and `str`. Its numbers are read as 32-bit words
(`w32`, `val32`, as on x86), whose halves are 16-bit digits (`pdig`); the
accumulator holds one digit a word (`dval`, `Digs`). The loads and stores
through `r12`, or through `r0` and `r1`, which the multiplication moves by 4
bytes a row (`Scr.ea_at`), and what changes (`Rest`, from X25519's proofs).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd)

/-! ## The working space -/

/-- The working space: `r12` holds its base `base`, it is the start of a
writable region (which may be longer), it lies below `2³²`, and offsets in it
are below 4096. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  wb : State.addr (s.gpr .r12) = base
  wr : ∃ len, size ≤ len ∧ len ≤ 2 ^ 32 ∧ (⟨base, len⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32
  small : size ≤ 4096

theorem Scr.wb_toNat {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    (s.gpr .r12).toNat = base.toNat := by
  rw [← hs.wb, VG.Proof.X25519.Arm.addr_toNat]

/-- `[r12 + d]`. -/
theorem Scr.ea {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d < size) : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = off base d := by
  rw [VG.Arm.addr_add (by have := hs.nowrap; have := hs.wb_toNat; omega), hs.wb]

/-- `[r + d]`, with `r` at `4i` bytes into the working space. -/
theorem Scr.ea_at {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r : Reg} {i d : Nat}
    (hp : s.gpr r = s.gpr .r12 + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 d) = off base (4 * i + d) := by
  rw [hp, Offset.add_add]
  exact hs.ea hd

theorem Scr.contains {base : Addr} {size d n : Nat} (hn : base.toNat + size ≤ 2 ^ 32) (h : d + n ≤ size) :
    (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions (s.rd ++ s.wr) (off base d) n :=
  have ⟨_, hl, hl', hR⟩ := hs.wr
  ⟨_, List.mem_append_right _ hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Scr.write {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions s.wr (off base d) n :=
  have ⟨_, hl, hl', hR⟩ := hs.wr
  ⟨_, hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Scr.off_lt {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d < size) : d < 4096 := by have := hs.small; omega

theorem Scr.of_rest {rs : List Reg} {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : Rest rs s s') (hr : .r12 ∉ rs) : Scr s' base size :=
  ⟨by rw [h.gpr _ hr]; exact hs.wb, h.wr ▸ hs.wr, hs.nowrap, hs.small⟩

/-! ## Digits -/

/-- Digit `h` (0: low, 1: high) of a word. -/
abbrev hdig (w h : Nat) : Nat := w / 2 ^ (16 * h) % 2 ^ 16

/-- Digit `j` of the number at `base + d`: half `j % 2` of its word `j / 2`. -/
abbrev pdig (m : Mem) (base : Addr) (d j : Nat) : Nat := hdig (w32 m base (d + 4 * (j / 2))) (j % 2)

/-- The `k` words at `base + d` as digits of a little-endian number. -/
def dval (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => dval m base d k + w32 m base (d + 4 * k) * 2 ^ (16 * k)

/-- The low `j` digits of the number at `base + d`. -/
def pval (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => pval m base d j + pdig m base d j * 2 ^ (16 * j)

/-- Each of the `k` words at `base + d` is a digit. -/
def Digs (m : Mem) (base : Addr) (d k : Nat) : Prop := ∀ j < k, w32 m base (d + 4 * j) < 2 ^ 16

theorem pow16_succ (k : Nat) : 2 ^ (16 * (k + 1)) = 2 ^ 16 * 2 ^ (16 * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem dval_lt {m : Mem} {base : Addr} {d : Nat} : ∀ {k : Nat}, Digs m base d k → dval m base d k < 2 ^ (16 * k)
  | 0, _ => by simp [dval]
  | k + 1, h => by
    have hk := h k (by omega)
    have ih := dval_lt (k := k) fun j hj => h j (by omega)
    rw [dval, pow16_succ]
    have : w32 m base (d + 4 * k) * 2 ^ (16 * k) ≤ (2 ^ 16 - 1) * 2 ^ (16 * k) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.sub_mul, Nat.one_mul] at this
    omega

/-- A word is its two digits. -/
theorem word_digits (w : Nat) (hw : w < 2 ^ 32) : w = hdig w 0 + hdig w 1 * 2 ^ 16 := by
  simp only [hdig, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one]
  omega

/-- `2k` digits are `k` words. -/
theorem pval_words (m : Mem) (base : Addr) (d : Nat) : ∀ k, pval m base d (2 * k) = val32 m base d k
  | 0 => rfl
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, pval, pval, pval_words m base d k, val32_append m base d k 1]
    have hw := word_digits (w32 m base (d + 4 * k)) (BitVec.isLt _)
    simp only [pdig, show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k) % 2 = 0 by omega, val32, Nat.mul_zero, Nat.add_zero,
      show 16 * (2 * k + 1) = 32 * k + 16 by omega, show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
    generalize hdig (w32 m base (d + 4 * k)) 0 = lo at *
    generalize hdig (w32 m base (d + 4 * k)) 1 = hi at *
    generalize w32 m base (d + 4 * k) = w at *
    subst hw
    grind

theorem hdig_lt (w h : Nat) : hdig w h < 2 ^ 16 := Nat.mod_lt _ (by decide)

theorem dval_append (m : Mem) (base : Addr) (d j : Nat) : ∀ k,
    dval m base d (j + k) = dval m base d j + 2 ^ (16 * j) * dval m base (d + 4 * j) k
  | 0 => by simp only [dval, Nat.add_zero, Nat.mul_zero]
  | k + 1 => by
    rw [← Nat.add_assoc, dval, dval_append m base d j k, dval, show d + 4 * (j + k) = d + 4 * j + 4 * k by omega,
      show 16 * (j + k) = 16 * j + 16 * k by omega, Nat.pow_add, Nat.mul_add, Nat.add_assoc]
    grind

theorem dval_congr {m m' : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m' base (d + 4 * j) = w32 m base (d + 4 * j)) → dval m' base d k = dval m base d k
  | 0, _ => rfl
  | k + 1, h => by rw [dval, dval, dval_congr fun j hj => h j (by omega), h k (by omega)]

theorem _root_.VG.Proof.Mont.Outside.dval {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 4 * k ≤ o ∨ o + n ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) :
    dval m' base d k = dval m base d k :=
  dval_congr fun j hj => h.w32 (by omega) (by omega)

theorem _root_.VG.Proof.Mont.Outside.digs {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 4 * k ≤ o ∨ o + n ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) (hs : Digs m base d k) :
    Digs m' base d k := fun j hj => by rw [h.w32 (by omega) (by omega)]; exact hs j hj

theorem _root_.VG.Proof.Mont.Outside.pdig {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d j : Nat} (hd : d + 4 * (j / 2) + 4 ≤ o ∨ o + n ≤ d + 4 * (j / 2)) (hd' : d + 4 * (j / 2) + 4 ≤ 2 ^ 64) :
    pdig m' base d j = pdig m base d j := by
  show hdig (w32 m' base (d + 4 * (j / 2))) (j % 2) = hdig (w32 m base (d + 4 * (j / 2))) (j % 2)
  rw [h.w32 (by omega) (by omega)]

theorem _root_.VG.Proof.Mont.Outside.pval {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d W : Nat} (hd : d + 4 * W ≤ o ∨ o + n ≤ d) (hd' : d + 4 * W ≤ 2 ^ 64) :
    ∀ {k : Nat}, k ≤ 2 * W → pval m' base d k = pval m base d k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [VG.Proof.Mont.Arm.pval, VG.Proof.Mont.Arm.pval, h.pval hd hd' (by omega), h.pdig (by omega) (by omega)]

theorem Digs.mono {m : Mem} {base : Addr} {d k k' : Nat} (h : Digs m base d k) (hk : k' ≤ k) : Digs m base d k' :=
  fun j hj => h j (by omega)

theorem Digs.shift {m : Mem} {base : Addr} {d j k : Nat} (h : Digs m base d (j + k)) : Digs m base (d + 4 * j) k :=
  fun l hl => by rw [show d + 4 * j + 4 * l = d + 4 * (j + l) by omega]; exact h _ (by omega)

theorem pval_lt (m : Mem) (base : Addr) (d : Nat) : ∀ k, pval m base d k < 2 ^ (16 * k)
  | 0 => by simp [pval]
  | k + 1 => by
    have ih := pval_lt m base d k
    have hd : pdig m base d k < 2 ^ 16 := hdig_lt _ _
    rw [pval, pow16_succ]
    have : pdig m base d k * 2 ^ (16 * k) ≤ (2 ^ 16 - 1) * 2 ^ (16 * k) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.sub_mul, Nat.one_mul] at this
    omega

end VG.Proof.Mont.Arm
