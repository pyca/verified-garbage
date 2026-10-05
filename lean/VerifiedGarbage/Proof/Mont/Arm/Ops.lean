import VerifiedGarbage.Impl.Mont.Arm
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.Arm.Words`. -/
section

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

theorem Scr.wb_toNat {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) :
    (s.gpr .r12).toNat = base.toNat := by
  rw [← hs.wb, VG.Proof.X25519.Arm.addr_toNat]

/-- `[r12 + d]`. -/
theorem Scr.ea {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {d : Nat}
    (hd : d < size) : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = off base d := by
  rw [VG.Arm.addr_add (by have := hs.nowrap; have := hs.wb_toNat; omega), hs.wb]

/-- `[r + d]`, with `r` at `4i` bytes into the working space. -/
theorem Scr.ea_at {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {r : Reg} {i d : Nat}
    (hp : s.gpr r = s.gpr .r12 + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 d) = off base (4 * i + d) := by
  rw [hp, Offset.add_add]
  exact hs.ea hd

theorem Scr.contains {base : Addr} {size d n : Nat} (hn : base.toNat + size ≤ 2 ^ 32) (h : d + n ≤ size) :
    (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions (s.rd ++ s.wr) (off base d) n :=
  have ⟨_, hl, hl', hR⟩ := hs.wr
  ⟨_, List.mem_append_right _ hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Scr.write {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions s.wr (off base d) n :=
  have ⟨_, hl, hl', hR⟩ := hs.wr
  ⟨_, hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Scr.off_lt {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {d : Nat}
    (hd : d < size) : d < 4096 := by have := hs.small; omega

theorem Scr.of_rest {rs : List Reg} {s s' : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size)
    (h : Rest rs s s') (hr : .r12 ∉ rs) : VG.Proof.Mont.Arm.Scr s' base size :=
  ⟨by rw [h.gpr _ hr]; exact hs.wb, h.wr ▸ hs.wr, hs.nowrap, hs.small⟩

/-! ## Digits -/

/-- Digit `h` (0: low, 1: high) of a word. -/
abbrev hdig (w h : Nat) : Nat := w / 2 ^ (16 * h) % 2 ^ 16

/-- Digit `j` of the number at `base + d`: half `j % 2` of its word `j / 2`. -/
abbrev pdig (m : Mem) (base : Addr) (d j : Nat) : Nat := VG.Proof.Mont.Arm.hdig (w32 m base (d + 4 * (j / 2))) (j % 2)

/-- The `k` words at `base + d` as digits of a little-endian number. -/
def dval (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => VG.Proof.Mont.Arm.dval m base d k + w32 m base (d + 4 * k) * 2 ^ (16 * k)

/-- The low `j` digits of the number at `base + d`. -/
def pval (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => VG.Proof.Mont.Arm.pval m base d j + VG.Proof.Mont.Arm.pdig m base d j * 2 ^ (16 * j)

/-- Each of the `k` words at `base + d` is a digit. -/
def Digs (m : Mem) (base : Addr) (d k : Nat) : Prop := ∀ j < k, w32 m base (d + 4 * j) < 2 ^ 16

theorem pow16_succ (k : Nat) : 2 ^ (16 * (k + 1)) = 2 ^ 16 * 2 ^ (16 * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem dval_lt {m : Mem} {base : Addr} {d : Nat} : ∀ {k : Nat}, VG.Proof.Mont.Arm.Digs m base d k → VG.Proof.Mont.Arm.dval m base d k < 2 ^ (16 * k)
  | 0, _ => by simp [VG.Proof.Mont.Arm.dval]
  | k + 1, h => by
    have hk := h k (by omega)
    have ih := VG.Proof.Mont.Arm.dval_lt (k := k) fun j hj => h j (by omega)
    rw [VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.pow16_succ]
    have : w32 m base (d + 4 * k) * 2 ^ (16 * k) ≤ (2 ^ 16 - 1) * 2 ^ (16 * k) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.sub_mul, Nat.one_mul] at this
    omega

/-- A word is its two digits. -/
theorem word_digits (w : Nat) (hw : w < 2 ^ 32) : w = VG.Proof.Mont.Arm.hdig w 0 + VG.Proof.Mont.Arm.hdig w 1 * 2 ^ 16 := by
  simp only [VG.Proof.Mont.Arm.hdig, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one]
  omega

/-- `2k` digits are `k` words. -/
theorem pval_words (m : Mem) (base : Addr) (d : Nat) : ∀ k, VG.Proof.Mont.Arm.pval m base d (2 * k) = val32 m base d k
  | 0 => rfl
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, VG.Proof.Mont.Arm.pval, VG.Proof.Mont.Arm.pval, VG.Proof.Mont.Arm.pval_words m base d k, val32_append m base d k 1]
    have hw := VG.Proof.Mont.Arm.word_digits (w32 m base (d + 4 * k)) (BitVec.isLt _)
    simp only [VG.Proof.Mont.Arm.pdig, show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k) % 2 = 0 by omega, val32, Nat.mul_zero, Nat.add_zero,
      show 16 * (2 * k + 1) = 32 * k + 16 by omega, show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
    generalize VG.Proof.Mont.Arm.hdig (w32 m base (d + 4 * k)) 0 = lo at *
    generalize VG.Proof.Mont.Arm.hdig (w32 m base (d + 4 * k)) 1 = hi at *
    generalize w32 m base (d + 4 * k) = w at *
    subst hw
    grind

theorem hdig_lt (w h : Nat) : VG.Proof.Mont.Arm.hdig w h < 2 ^ 16 := Nat.mod_lt _ (by decide)

theorem dval_append (m : Mem) (base : Addr) (d j : Nat) : ∀ k,
    VG.Proof.Mont.Arm.dval m base d (j + k) = VG.Proof.Mont.Arm.dval m base d j + 2 ^ (16 * j) * VG.Proof.Mont.Arm.dval m base (d + 4 * j) k
  | 0 => by simp only [VG.Proof.Mont.Arm.dval, Nat.add_zero, Nat.mul_zero]
  | k + 1 => by
    rw [← Nat.add_assoc, VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval_append m base d j k, VG.Proof.Mont.Arm.dval, show d + 4 * (j + k) = d + 4 * j + 4 * k by omega,
      show 16 * (j + k) = 16 * j + 16 * k by omega, Nat.pow_add, Nat.mul_add, Nat.add_assoc]
    grind

theorem dval_congr {m m' : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m' base (d + 4 * j) = w32 m base (d + 4 * j)) → VG.Proof.Mont.Arm.dval m' base d k = VG.Proof.Mont.Arm.dval m base d k
  | 0, _ => rfl
  | k + 1, h => by rw [VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval_congr fun j hj => h j (by omega), h k (by omega)]

theorem _root_.VG.Proof.Mont.Outside.dval {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 4 * k ≤ o ∨ o + n ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) :
    VG.Proof.Mont.Arm.dval m' base d k = VG.Proof.Mont.Arm.dval m base d k :=
  VG.Proof.Mont.Arm.dval_congr fun j hj => h.w32 (by omega) (by omega)

theorem _root_.VG.Proof.Mont.Outside.digs {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 4 * k ≤ o ∨ o + n ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) (hs : VG.Proof.Mont.Arm.Digs m base d k) :
    VG.Proof.Mont.Arm.Digs m' base d k := fun j hj => by rw [h.w32 (by omega) (by omega)]; exact hs j hj

theorem _root_.VG.Proof.Mont.Outside.pdig {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d j : Nat} (hd : d + 4 * (j / 2) + 4 ≤ o ∨ o + n ≤ d + 4 * (j / 2)) (hd' : d + 4 * (j / 2) + 4 ≤ 2 ^ 64) :
    VG.Proof.Mont.Arm.pdig m' base d j = VG.Proof.Mont.Arm.pdig m base d j := by
  show VG.Proof.Mont.Arm.hdig (w32 m' base (d + 4 * (j / 2))) (j % 2) = VG.Proof.Mont.Arm.hdig (w32 m base (d + 4 * (j / 2))) (j % 2)
  rw [h.w32 (by omega) (by omega)]

theorem _root_.VG.Proof.Mont.Outside.pval {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d W : Nat} (hd : d + 4 * W ≤ o ∨ o + n ≤ d) (hd' : d + 4 * W ≤ 2 ^ 64) :
    ∀ {k : Nat}, k ≤ 2 * W → VG.Proof.Mont.Arm.pval m' base d k = VG.Proof.Mont.Arm.pval m base d k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [VG.Proof.Mont.Arm.pval, VG.Proof.Mont.Arm.pval, h.pval hd hd' (by omega), h.pdig (by omega) (by omega)]

theorem Digs.mono {m : Mem} {base : Addr} {d k k' : Nat} (h : VG.Proof.Mont.Arm.Digs m base d k) (hk : k' ≤ k) : VG.Proof.Mont.Arm.Digs m base d k' :=
  fun j hj => h j (by omega)

theorem Digs.shift {m : Mem} {base : Addr} {d j k : Nat} (h : VG.Proof.Mont.Arm.Digs m base d (j + k)) : VG.Proof.Mont.Arm.Digs m base (d + 4 * j) k :=
  fun l hl => by rw [show d + 4 * j + 4 * l = d + 4 * (j + l) by omega]; exact h _ (by omega)

theorem pval_lt (m : Mem) (base : Addr) (d : Nat) : ∀ k, VG.Proof.Mont.Arm.pval m base d k < 2 ^ (16 * k)
  | 0 => by simp [VG.Proof.Mont.Arm.pval]
  | k + 1 => by
    have ih := VG.Proof.Mont.Arm.pval_lt m base d k
    have hd : VG.Proof.Mont.Arm.pdig m base d k < 2 ^ 16 := VG.Proof.Mont.Arm.hdig_lt _ _
    rw [VG.Proof.Mont.Arm.pval, VG.Proof.Mont.Arm.pow16_succ]
    have : VG.Proof.Mont.Arm.pdig m base d k * 2 ^ (16 * k) ≤ (2 ^ 16 - 1) * 2 ^ (16 * k) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.sub_mul, Nat.one_mul] at this
    omega

end VG.Proof.Mont.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.Arm.Step`. -/
section

/-!
# Montgomery arithmetic on 32-bit ARM: a multiply-accumulate step

`mulStep acc src j` adds `r2 · d_j` and the carry `r3` to the digit of the
accumulator at `[r0 + acc + 4j]`, for digit `j` of the number at
`[r12 + src]`, and leaves the carry in `r3` (`mulStep_ok`): with every
operand below `2¹⁶`, `x = u d + t + c` is below `2³²`; its low half is
stored and its high half is the carry. `carryUp` adds the carry into the
digits `D` and `D + 1` (`carryUp_ok`).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul op2_reg op2_lsr op2_lsl
  op2_imm dpVal toNat_add_lt toNat_shr)

/-- A step's sum is below `2³²`. -/
theorem step_lt {u d t c : Nat} (hu : u < 2 ^ 16) (hd : d < 2 ^ 16) (ht : t < 2 ^ 16) (hc : c < 2 ^ 16) :
    u * d + t + c < 2 ^ 32 := by
  have : u * d ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem toNat_and_r6 {x m : BitVec 32} (hm : m = VG.Proof.X25519.Arm.mask16) : (x &&& m).toNat = x.toNat % 2 ^ 16 := by
  subst hm; exact VG.Proof.X25519.Arm.toNat_and_mask16 x

/-- `d = ` digit `h` of `w`. -/
theorem wp_half {s : State} {is : List Instr} {Q : State → Prop} {d w : Reg} {h : Nat} (hh : h < 2)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 32 (VG.Proof.Mont.Arm.hdig (s.gpr w).toNat h)) → WP isa (.block is) s' Q) :
    WP isa (.block (half d w h :: is)) s Q := by
  obtain rfl | rfl : h = 0 ∨ h = 1 := by omega
  · refine wp_dp (op2_reg s .r6) fun s' u => k s' ?_
    have e : dpVal .and (s.gpr w) (s.gpr .r6) = BitVec.ofNat 32 (VG.Proof.Mont.Arm.hdig (s.gpr w).toNat 0) := by
      apply BitVec.eq_of_toNat_eq
      rw [dpVal, VG.Proof.Mont.Arm.toNat_and_r6 h6, BitVec.toNat_ofNat]
      simp only [VG.Proof.Mont.Arm.hdig, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      omega
    exact e ▸ u
  · refine wp_mov (op2_lsr (by decide)) fun s' u => k s' ?_
    have e : s.gpr w >>> 16 = BitVec.ofNat 32 (VG.Proof.Mont.Arm.hdig (s.gpr w).toNat 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_shr, BitVec.toNat_ofNat]
      have := (s.gpr w).isLt
      simp only [VG.Proof.Mont.Arm.hdig, Nat.mul_one]
      omega
    exact e ▸ u

/-- `r7 = ` digit `j` of the number at `[r12 + src]`. -/
theorem digitAt_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {src j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hd : src + 4 * (j / 2) + 4 ≤ size) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .r7 (BitVec.ofNat 32 (VG.Proof.Mont.Arm.pdig s.mem base src j)) → WP isa (.block is) s' Q) :
    WP isa (.block (digitAt src j ++ is)) s Q := by
  simp only [digitAt, List.cons_append, List.nil_append]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hd) fun s₁ u₁ => ?_
  refine VG.Proof.Mont.Arm.wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => k s₂ ?_
  rw [u₁.gpr] at u₂
  exact ⟨u₂.gpr, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩

/-- `[r0 + acc + 4j] += r2 · d_j + r3`, the carry to `r3`. -/
theorem mulStep_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc src i j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hsrc : src + 4 * (j / 2) + 4 ≤ size) (ht : 4 * i + (acc + 4 * j) + 4 ≤ size)
    (hu : (s.gpr .r2).toNat < 2 ^ 16) (hc : (s.gpr .r3).toNat < 2 ^ 16)
    (htd : w32 s.mem base (4 * i + (acc + 4 * j)) < 2 ^ 16) :
    WP isa (.block (mulStep acc src j)) s fun u =>
      u.mem = s.mem.writeW (off base (4 * i + (acc + 4 * j))) (BitVec.ofNat 32
        (((s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src j + w32 s.mem base (4 * i + (acc + 4 * j)) +
          (s.gpr .r3).toNat) % 2 ^ 16)) ∧
      (u.gpr .r3).toNat = ((s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src j +
          w32 s.mem base (4 * i + (acc + 4 * j)) + (s.gpr .r3).toNat) / 2 ^ 16 ∧
      Rest [.r3, .r5, .r7] s u := by
  simp only [mulStep]
  refine VG.Proof.Mont.Arm.digitAt_ok hs h6 hsrc fun s₁ u₁ => ?_
  refine wp_mul fun s₂ u₂ => ?_
  have hs₂ : VG.Proof.Mont.Arm.Scr s₂ base size := hs.of_rest ((u₁.rest (ws := [.r7]) (by simp)).trans (u₂.rest (by simp)))
    (by decide)
  have hp₂ : s₂.gpr .r0 = s₂.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact hp
  refine wp_ldr (hs.off_lt (by omega)) (hs₂.ea_at hp₂ (by omega)) (hs₂.read ht) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  have hs₆ : VG.Proof.Mont.Arm.Scr s₆ base size := hs₂.of_rest (((u₃.rest (ws := [.r5, .r7]) (by simp)).trans
    (u₄.rest (by simp))).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))) (by decide)
  have hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    exact hp₂
  refine wp_str (hs.off_lt (by omega)) (hs₆.ea_at hp₆ (by omega)) (hs₆.write ht) fun s₇ m₇ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₈ u₈ => WP.block_nil ?_
  -- The values along the way.
  have m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
  have r2₁ : s₁.gpr .r2 = s.gpr .r2 := u₁.other _ (by decide)
  have r3₄ : s₄.gpr .r3 = s.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r6₅ : s₅.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]; exact h6
  have r7₃ : s₃.gpr .r7 = s₂.gpr .r7 := u₃.other _ (by decide)
  have r7₄ : s₄.gpr .r7 = s₃.gpr .r7 := u₄.other _ (by decide)
  have r5₄ : s₄.gpr .r5 = s₃.gpr .r5 + s₃.gpr .r7 := u₄.gpr
  have r5₅ : s₅.gpr .r5 = s₄.gpr .r5 + s₄.gpr .r3 := u₅.gpr
  have r5₆ : s₆.gpr .r5 = s₅.gpr .r5 := u₆.other _ (by decide)
  have r7₆ : s₆.gpr .r7 = s₅.gpr .r5 &&& s₅.gpr .r6 := u₆.gpr
  have r5₃ : s₃.gpr .r5 = s₂.mem.readW (off base (4 * i + (acc + 4 * j))) 32 := u₃.gpr
  have r7₂ : s₂.gpr .r7 = s₁.gpr .r2 * s₁.gpr .r7 := u₂.gpr
  have hd : VG.Proof.Mont.Arm.pdig s.mem base src j < 2 ^ 16 := VG.Proof.Mont.Arm.hdig_lt _ _
  have hx := VG.Proof.Mont.Arm.step_lt hu hd htd hc
  have hr7 : (s₂.gpr .r7).toNat = (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src j := by
    rw [r7₂, r2₁, u₁.gpr, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := VG.Proof.Mont.Arm.pdig _ _ _ _) (by omega),
      Nat.mod_eq_of_lt (by have := Nat.mul_le_mul (Nat.le_of_lt_succ hu) (Nat.le_of_lt_succ hd); omega)]
  have e3 : (s₃.gpr .r5).toNat = w32 s.mem base (4 * i + (acc + 4 * j)) := by rw [r5₃, m₂]
  have e7 : (s₃.gpr .r7).toNat = (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src j := by rw [r7₃, hr7]
  have a1 : (s₄.gpr .r5).toNat = w32 s.mem base (4 * i + (acc + 4 * j)) +
      (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src j := by
    rw [r5₄, toNat_add_lt (by rw [e3, e7]; omega), e3, e7]
  have hr5 : (s₅.gpr .r5).toNat = (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src j +
      w32 s.mem base (4 * i + (acc + 4 * j)) + (s.gpr .r3).toNat := by
    rw [r5₅, toNat_add_lt (by rw [a1, r3₄]; omega), a1, r3₄]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [u₈.mem, m₇.mem, m₆, r7₆, r6₅]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X25519.Arm.toNat_and_mask16, BitVec.toNat_ofNat, hr5]
    omega
  · rw [u₈.gpr, toNat_shr, m₇.gpr, r5₆, hr5]
  · refine (((u₁.rest (ws := [.r3, .r5, .r7]) (by simp)).trans (u₂.rest (by simp))).trans
      ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
      (((u₅.rest (by simp)).trans (u₆.rest (by simp))).trans ((m₇.rest _).trans (u₈.rest (by simp))))

end VG.Proof.Mont.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.Arm.Row`. -/
section

/-!
# Montgomery arithmetic on 32-bit ARM: a row of the multiplication

`mulRow acc src D` adds `r2 · [src]` (its `D` digits) to the window of the
accumulator at `[r0 + acc]`, `r0 = r12 + 4i` (`w = 4i + acc` from the base),
which holds digits: the `D` steps leave the carry in `r3` (`steps_ok`), which
`carryUp` adds to digits `D` and `D + 1` (`carryUp_ok`), so that the window's
`D + 2` digits hold the sum when it fits them (`mulRow_ok`).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul op2_reg op2_lsr op2_lsl
  op2_imm dpVal toNat_add_lt toNat_shr)

/-- The first `k` steps of a row. -/
def steps (acc src k : Nat) : List Instr := (List.range k).flatMap (mulStep acc src)

theorem steps_succ (acc src k : Nat) : VG.Proof.Mont.Arm.steps acc src (k + 1) = VG.Proof.Mont.Arm.steps acc src k ++ mulStep acc src k := by
  simp only [VG.Proof.Mont.Arm.steps, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The window's low `k` digits `+= r2 · [src] + r3`, the carry to `r3`. -/
theorem steps_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc src i w W : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hsrc : src + 4 * W ≤ size)
    (hu : (s.gpr .r2).toNat < 2 ^ 16) (hc : (s.gpr .r3).toNat < 2 ^ 16) :
    ∀ {k : Nat}, k ≤ 2 * W → w + 4 * k ≤ size → (src + 4 * W ≤ w ∨ w + 4 * k ≤ src) → VG.Proof.Mont.Arm.Digs s.mem base w k →
    WP isa (.block (VG.Proof.Mont.Arm.steps acc src k)) s fun u =>
      Outside base w (4 * k) s.mem u.mem ∧
      VG.Proof.Mont.Arm.dval u.mem base w k + 2 ^ (16 * k) * (u.gpr .r3).toNat =
        VG.Proof.Mont.Arm.dval s.mem base w k + (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pval s.mem base src k + (s.gpr .r3).toNat ∧
      (u.gpr .r3).toNat < 2 ^ 16 ∧ VG.Proof.Mont.Arm.Digs u.mem base w k ∧ Rest [.r3, .r5, .r7] s u
  | 0, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by simp only [VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.pval, Nat.mul_zero,
      Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero], hc, fun _ h => absurd h (Nat.not_lt_zero _),
      Rest.refl _ _⟩
  | k + 1, hk, hwk, hsep, hd => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.Arm.steps_succ]
    refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.steps_ok hs h6 hp hw hsrc hu hc (k := k) (by omega) (by omega)
      (by omega) (hd.mono (by omega))) fun s₁ ⟨O₁, V₁, C₁, D₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    have h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁.gpr _ (by decide)]; exact h6
    have hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
      rw [K₁.gpr _ (by decide), K₁.gpr _ (by decide)]; exact hp
    have e : 4 * i + (acc + 4 * k) = w + 4 * k := by omega
    have tk : w32 s₁.mem base (w + 4 * k) = w32 s.mem base (w + 4 * k) := O₁.w32 (by omega) (by omega)
    have tkd : w32 s₁.mem base (4 * i + (acc + 4 * k)) < 2 ^ 16 := by rw [e, tk]; exact hd k (by omega)
    refine WP.mono (VG.Proof.Mont.Arm.mulStep_ok hs₁ h6₁ hp₁ (j := k) (by omega) (by omega)
      (by rw [K₁.gpr _ (by decide)]; exact hu) C₁ tkd) fun u ⟨m₂, b₂, K₂⟩ => ?_
    rw [e] at m₂ b₂
    have r2₁ : s₁.gpr .r2 = s.gpr .r2 := K₁.gpr _ (by decide)
    have dk : VG.Proof.Mont.Arm.pdig s₁.mem base src k = VG.Proof.Mont.Arm.pdig s.mem base src k := O₁.pdig (by omega) (by omega)
    rw [r2₁, dk, tk] at m₂ b₂
    have W := writeW32_outside s₁.mem base (d := w + 4 * k)
      (BitVec.ofNat 32 (((s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src k + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r3).toNat) % 2 ^ 16)) (by omega)
    rw [← m₂] at W
    have hlow : VG.Proof.Mont.Arm.dval u.mem base w k = VG.Proof.Mont.Arm.dval s₁.mem base w k := W.dval (by omega) (by omega)
    have htop : w32 u.mem base (w + 4 * k) = ((s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src k +
        w32 s.mem base (w + 4 * k) + (s₁.gpr .r3).toNat) % 2 ^ 16 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]; omega
    have hdk := VG.Proof.Mont.Arm.hdig_lt (w32 s.mem base (src + 4 * (k / 2))) (k % 2)
    have hx := VG.Proof.Mont.Arm.step_lt (d := VG.Proof.Mont.Arm.pdig s.mem base src k) hu hdk (hd k (by omega)) C₁
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, ?_, ?_,
      K₁.trans K₂⟩
    · rw [VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.pval, hlow, htop, b₂, VG.Proof.Mont.Arm.pow16_succ]
      generalize hxd : (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pdig s.mem base src k + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r3).toNat = x at *
      have hx' := Nat.div_add_mod x (2 ^ 16)
      generalize 2 ^ (16 * k) = P at *
      grind
    · rw [b₂]; omega
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [W.w32 (by omega) (by omega)]; exact D₁ j hj
      · rw [htop]; exact Nat.mod_lt _ (by decide)

/-- The carry `r3` added to the window's digits `D` and `D + 1`, when the
sum fits them. -/
theorem carryUp_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc i w D : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hD : w + 4 * D + 8 ≤ size) (hd : VG.Proof.Mont.Arm.Digs s.mem base (w + 4 * D) 2)
    (hlt : VG.Proof.Mont.Arm.dval s.mem base (w + 4 * D) 2 + (s.gpr .r3).toNat < 2 ^ 32) :
    WP isa (.block (carryUp acc D)) s fun u =>
      Outside base (w + 4 * D) 8 s.mem u.mem ∧
      VG.Proof.Mont.Arm.dval u.mem base (w + 4 * D) 2 = VG.Proof.Mont.Arm.dval s.mem base (w + 4 * D) 2 + (s.gpr .r3).toNat ∧
      VG.Proof.Mont.Arm.Digs u.mem base (w + 4 * D) 2 ∧ Rest [.r5, .r7] s u := by
  have hn := hs.nowrap
  have e₀ : 4 * i + (acc + 4 * D) = w + 4 * D := by omega
  have e₁ : 4 * i + (acc + 4 * D + 4) = w + 4 * D + 4 := by omega
  have d0 := hd 0 (by omega)
  have d1 := hd 1 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at d0 d1
  simp only [VG.Proof.Mont.Arm.dval, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.pow_zero] at hlt ⊢
  simp only [carryUp]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea_at hp (d := acc + 4 * D) (by omega)) (hs.read (by omega))
    fun s₁ u₁ => ?_
  refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have K₃ : Rest [.r5, .r7] s s₃ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
  have hs₃ := hs.of_rest K₃ (by decide)
  have hp₃ : s₃.gpr .r0 = s₃.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₃.gpr _ (by decide), K₃.gpr _ (by decide)]; exact hp
  refine wp_str (hs.off_lt (by omega)) (hs₃.ea_at hp₃ (d := acc + 4 * D) (by omega)) (hs₃.write (by omega))
    fun s₄ m₄ => ?_
  have K₄ : Rest [.r5, .r7] s s₄ := K₃.trans (m₄.rest _)
  have hs₄ := hs.of_rest K₄ (by decide)
  have hp₄ : s₄.gpr .r0 = s₄.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₄.gpr _ (by decide), K₄.gpr _ (by decide)]; exact hp
  refine wp_ldr (hs.off_lt (by omega)) (hs₄.ea_at hp₄ (d := acc + 4 * D + 4) (by omega)) (hs₄.read (by omega))
    fun s₅ u₅ => ?_
  refine wp_dp (op2_lsr (by decide)) fun s₆ u₆ => ?_
  have K₆ : Rest [.r5, .r7] s s₆ := K₄.trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  have hs₆ := hs.of_rest K₆ (by decide)
  have hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.gpr _ (by decide), K₆.gpr _ (by decide)]; exact hp
  refine wp_str (hs.off_lt (by omega)) (hs₆.ea_at hp₆ (d := acc + 4 * D + 4) (by omega)) (hs₆.write (by omega))
    fun s₇ m₇ => WP.block_nil ?_
  rw [e₀] at m₄
  rw [e₁] at u₅ m₇
  -- The values.
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have a1 : (s₁.gpr .r5).toNat = w32 s.mem base (w + 4 * D) := by rw [u₁.gpr, e₀]
  have b1 : s₁.gpr .r3 = s.gpr .r3 := u₁.other _ (by decide)
  have r5₂ : (s₂.gpr .r5).toNat = w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat := by
    rw [u₂.gpr, dpVal, toNat_add_lt (by rw [a1, b1]; omega), a1, b1]
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  have r7₃ : (s₃.gpr .r7).toNat = (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) % 2 ^ 16 := by
    rw [u₃.gpr, dpVal, VG.Proof.Mont.Arm.toNat_and_r6 h6₂, r5₂]
  have hhi : w32 s₄.mem base (w + 4 * D + 4) = w32 s.mem base (w + 4 * D + 4) := by
    rw [m₄.mem, m₃]; exact w32_write_ne hn (by omega) (by omega) (by omega) _
  have a5 : (s₅.gpr .r7).toNat = w32 s.mem base (w + 4 * D + 4) := by rw [u₅.gpr]; exact hhi
  have b5 : s₅.gpr .r5 = s₂.gpr .r5 := by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide)]
  have r7₆ : (s₆.gpr .r7).toNat = w32 s.mem base (w + 4 * D + 4) +
      (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) / 2 ^ 16 := by
    rw [u₆.gpr, dpVal, toNat_add_lt (by rw [a5, toNat_shr, b5, r5₂]; omega), a5, toNat_shr, b5, r5₂]
  have W₀ := writeW32_outside s.mem base (d := w + 4 * D) (s₃.gpr .r7) (by omega)
  have W₁ := writeW32_outside (s.mem.writeW (off base (w + 4 * D)) (s₃.gpr .r7)) base
    (d := w + 4 * D + 4) (s₆.gpr .r7) (by omega)
  rw [m₆, m₄.mem, m₃] at m₇
  rw [← m₇.mem] at W₁
  have v0 : w32 s₇.mem base (w + 4 * D) = (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) % 2 ^ 16 := by
    rw [m₇.mem, w32_write_ne hn (by omega) (by omega) (by omega), w32_write_self, r7₃]
  have v1 : w32 s₇.mem base (w + 4 * D + 4) = w32 s.mem base (w + 4 * D + 4) +
      (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) / 2 ^ 16 := by
    rw [m₇.mem, w32_write_self, r7₆]
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega)), ?_, ?_,
    K₆.trans (m₇.rest _)⟩
  · rw [v0, v1]; omega
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp only [Nat.mul_zero, Nat.add_zero]; rw [v0]; exact Nat.mod_lt _ (by decide)
    · simp only [Nat.mul_one]; rw [v1]; omega

/-- The window `+= r2 · [src]` (`D ≤ 2W` digits of its `W` words), when the
sum fits the window's `D + 2` digits. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc src i w W D : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hsrc : src + 4 * W ≤ size) (hDW : D ≤ 2 * W) (hwD : w + 4 * D + 8 ≤ size)
    (hsep : src + 4 * W ≤ w ∨ w + 4 * D + 8 ≤ src) (hu : (s.gpr .r2).toNat < 2 ^ 16)
    (hd : VG.Proof.Mont.Arm.Digs s.mem base w (D + 2))
    (hlt : VG.Proof.Mont.Arm.dval s.mem base w (D + 2) + (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pval s.mem base src D < 2 ^ (16 * (D + 2))) :
    WP isa (.block (mulRow acc src D)) s fun u =>
      Outside base w (4 * D + 8) s.mem u.mem ∧
      VG.Proof.Mont.Arm.dval u.mem base w (D + 2) = VG.Proof.Mont.Arm.dval s.mem base w (D + 2) + (s.gpr .r2).toNat * VG.Proof.Mont.Arm.pval s.mem base src D ∧
      VG.Proof.Mont.Arm.Digs u.mem base w (D + 2) ∧ Rest [.r3, .r5, .r7] s u := by
  have hn := hs.nowrap
  simp only [mulRow, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₀ u₀ => ?_
  have K₀ : Rest [.r3, .r5, .r7] s s₀ := u₀.rest (by simp)
  have hs₀ := hs.of_rest K₀ (by decide)
  have h6₀ : s₀.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₀.gpr _ (by decide)]; exact h6
  have hp₀ : s₀.gpr .r0 = s₀.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₀.gpr _ (by decide), K₀.gpr _ (by decide)]; exact hp
  have z : (s₀.gpr .r3).toNat = 0 := by rw [u₀.gpr]; rfl
  have hu₀ : (s₀.gpr .r2).toNat < 2 ^ 16 := by rw [K₀.gpr _ (by decide)]; exact hu
  rw [← u₀.mem] at hd hlt
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.steps_ok hs₀ h6₀ hp₀ hw hsrc hu₀ (by rw [z]; decide) (k := D) hDW
    (by omega) (by omega) (hd.mono (by omega))) fun s₁ ⟨O₁, V₁, C₁, D₁, K₁⟩ => ?_
  have K₀₁ := K₀.trans K₁
  have hs₁ := hs.of_rest K₀₁ (by decide)
  have h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₀₁.gpr _ (by decide)]; exact h6
  have hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₀₁.gpr _ (by decide), K₀₁.gpr _ (by decide)]; exact hp
  rw [z, Nat.add_zero, u₀.other _ (by decide)] at V₁
  have hhi : VG.Proof.Mont.Arm.dval s₁.mem base (w + 4 * D) 2 = VG.Proof.Mont.Arm.dval s₀.mem base (w + 4 * D) 2 := O₁.dval (by omega) (by omega)
  have hsplit : VG.Proof.Mont.Arm.dval s₀.mem base w (D + 2) = VG.Proof.Mont.Arm.dval s₀.mem base w D + 2 ^ (16 * D) * VG.Proof.Mont.Arm.dval s₀.mem base (w + 4 * D) 2 :=
    VG.Proof.Mont.Arm.dval_append _ _ _ _ _
  have hP : 0 < 2 ^ (16 * D) := Nat.two_pow_pos _
  have hlt₁ : VG.Proof.Mont.Arm.dval s₁.mem base (w + 4 * D) 2 + (s₁.gpr .r3).toNat < 2 ^ 32 := by
    rw [hhi]
    rw [hsplit, show 16 * (D + 2) = 16 * D + 32 by omega, Nat.pow_add] at hlt
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (16 * D)) ?_
    rw [Nat.mul_add]
    have := VG.Proof.Mont.Arm.dval_lt D₁
    omega
  have hd₁ : VG.Proof.Mont.Arm.Digs s₁.mem base (w + 4 * D) 2 := O₁.digs (by omega) (by omega) hd.shift
  refine WP.mono (VG.Proof.Mont.Arm.carryUp_ok hs₁ h6₁ hp₁ hw (by omega) hd₁ hlt₁) fun u ⟨O₂, V₂, D₂, K₂⟩ =>
    ⟨?_, ?_, ?_, K₀₁.trans (K₂.mono (by simp))⟩
  · rw [u₀.mem] at O₁; exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))
  · rw [VG.Proof.Mont.Arm.dval_append, V₂, O₂.dval (d := w) (k := D) (by omega) (by omega), hhi, ← u₀.mem, hsplit, Nat.mul_add]
    omega
  · intro j hj
    by_cases hjD : j < D
    · rw [O₂.w32 (by omega) (by omega)]; exact D₁ j hjD
    · have := D₂ (j - D) (by omega)
      rwa [show w + 4 * D + 4 * (j - D) = w + 4 * j by omega] at this

end VG.Proof.Mont.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.Arm.Loop`. -/
section

/-!
# Montgomery arithmetic on 32-bit ARM: the loop of the multiplication

A digit's row (`digitRow`), at `r0 = r12 + 4i`, adds `u [b]` and then `q m`
to the window of `D + 2` digits at `acc + 4i`, which holds `T < 2m` (the
digit above it being zero): `q = t₀ m' mod 2¹⁶` makes the sum's low digit
zero, so the window one digit up holds `(T + u B + q m) / 2¹⁶`, below `2m`
again (`digitRow_ok`). An iteration of the loop (`row`) does the rows of
the two digits of a word of `[a]` (`row_ok`); `Z` is whether it was the last.
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul wp_movw wp_subs op2_reg op2_lsr
  op2_lsl op2_imm dpVal toNat_add_lt toNat_shr)

/-- The registers the arithmetic changes. -/
def clob : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9]

/-- `t₀ + (t₀ m' mod 2¹⁶) m ≡ 0 (mod 2¹⁶)` when `m m' ≡ -1`. -/
theorem mont_low16 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 16 = 0) :
    (t0 + t0 * minv % 2 ^ 16 * m) % 2 ^ 16 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 16), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2¹⁶`. -/
theorem minv16_inv {M : Mod} {m : Nat} (h : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0 := by
  rw [minv16, BitVec.toNat_setWidth, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * M.minv.toNat + 1) (show 2 ^ 16 ∣ 2 ^ 64 from ⟨2 ^ 48, by decide⟩), h]

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T u B q m : Nat} (hT : T < 2 * m) (hu : u < 2 ^ 16) (hB : B < m) (hq : q < 2 ^ 16) :
    T + u * B + q * m < 2 ^ 16 * (2 * m) := by
  have h1 : u * B ≤ (2 ^ 16 - 1) * B := Nat.mul_le_mul_right _ (by omega)
  have h2 : q * m ≤ (2 ^ 16 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The low digit of a window of digits. -/
theorem dval_low {m : Mem} {base : Addr} {d k : Nat} (h : VG.Proof.Mont.Arm.Digs m base d (k + 1)) :
    VG.Proof.Mont.Arm.dval m base d (k + 1) % 2 ^ 16 = w32 m base d := by
  rw [show k + 1 = 1 + k by omega, VG.Proof.Mont.Arm.dval_append, show VG.Proof.Mont.Arm.dval m base d 1 = w32 m base d by
    simp [VG.Proof.Mont.Arm.dval], Nat.mul_comm, show 16 * 1 = 16 by rfl, Nat.add_mul_mod_self_right]
  have := h 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at this
  exact Nat.mod_eq_of_lt this

/-- The window one digit up, when the low digit is zero and the digit above
the window is zero. -/
theorem dval_shift {m : Mem} {base : Addr} {d k : Nat} (h0 : w32 m base d = 0) (htop : w32 m base (d + 4 * (k + 1)) = 0) :
    2 ^ 16 * VG.Proof.Mont.Arm.dval m base (d + 4) (k + 1) = VG.Proof.Mont.Arm.dval m base d (k + 1) := by
  rw [show k + 1 = 1 + k by omega, VG.Proof.Mont.Arm.dval_append m base d 1 k, show VG.Proof.Mont.Arm.dval m base d 1 = w32 m base d by simp [VG.Proof.Mont.Arm.dval], h0,
    Nat.zero_add, show 1 + k = k + 1 by omega, VG.Proof.Mont.Arm.dval, show d + 4 + 4 * k = d + 4 * (k + 1) by omega, htop,
    show 16 * 1 = 16 by rfl]
  simp

/-- A pointer moved up a word. -/
theorem ptr_succ (e : BitVec 32) (i : Nat) :
    e + BitVec.ofNat 32 (4 * i) + 4 = e + BitVec.ofNat 32 (4 * (i + 1)) := by
  rw [BitVec.add_assoc]
  refine congrArg (e + ·) ?_
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega

/-- What a digit's row needs of the layout: `[b]` and the modulus (`W`
words, `D = 2W` digits) apart from the window and the digit above it. -/
structure RowLay (W size w b mo : Nat) : Prop where
  b_le : b + 4 * W ≤ size
  mo_le : mo + 4 * W ≤ size
  w_le : w + 4 * (2 * W + 3) ≤ size
  sb : b + 4 * W ≤ w ∨ w + 4 * (2 * W + 3) ≤ b
  smo : mo + 4 * W ≤ w ∨ w + 4 * (2 * W + 3) ≤ mo

/-- A digit's row: from the window `T < 2m` at `w = acc + 4i` (the digit
above it zero), the window one digit up holds `(T + u B + q m) / 2¹⁶`. -/
theorem digitRow_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {W D acc b h i w m : Nat}
    (hW : words M = W) (hD : digits M = D) (hDW : D = 2 * W) (hL : VG.Proof.Mont.Arm.RowLay W size w b M.mo)
    (hh : h < 2) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) (hd : VG.Proof.Mont.Arm.Digs s.mem base w (D + 2))
    (hT : VG.Proof.Mont.Arm.dval s.mem base w (D + 2) < 2 * m) (htop : w32 s.mem base (w + 4 * (D + 2)) = 0) :
    WP isa (.block (digitRow M acc b h)) s fun u =>
      u.gpr .r0 = u.gpr .r12 + BitVec.ofNat 32 (4 * (i + 1)) ∧
      Outside base w (4 * (D + 2)) s.mem u.mem ∧ VG.Proof.Mont.Arm.Digs u.mem base (w + 4) (D + 2) ∧
      (∃ q, q < 2 ^ 16 ∧ 2 ^ 16 * VG.Proof.Mont.Arm.dval u.mem base (w + 4) (D + 2) =
        VG.Proof.Mont.Arm.dval s.mem base w (D + 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat h * val32 s.mem base b W + q * m) ∧
      Rest [.r0, .r2, .r3, .r5, .r7] s u := by
  have hn := hs.nowrap
  obtain ⟨hb_le, hmo_le, hw_le, hsb, hsmo⟩ := hL
  subst hDW
  have hm0 : m < 2 ^ (16 * (2 * W)) := by
    rw [← hm, show 16 * (2 * W) = 32 * W by omega]; exact val32_lt _ _ _ _
  simp only [digitRow, hD, List.cons_append, List.nil_append, List.append_assoc]
  refine VG.Proof.Mont.Arm.wp_half hh h6 fun s₁ u₁ => ?_
  have K₁ : Rest [.r2, .r3, .r5, .r7] s s₁ := u₁.rest (by simp)
  have hs₁ := hs.of_rest K₁ (by decide)
  have h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁.gpr _ (by decide)]; exact h6
  have hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  have hU := VG.Proof.Mont.Arm.hdig_lt (s.gpr .r8).toNat h
  have hu₁ : (s₁.gpr .r2).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat h := by
    rw [u₁.gpr, BitVec.toNat_ofNat]; omega
  rw [← u₁.mem] at hm hB hd hT htop
  have hBp : VG.Proof.Mont.Arm.pval s₁.mem base b (2 * W) = val32 s₁.mem base b W := VG.Proof.Mont.Arm.pval_words _ _ _ _
  have hlt₁ : VG.Proof.Mont.Arm.dval s₁.mem base w (2 * W + 2) + (s₁.gpr .r2).toNat * VG.Proof.Mont.Arm.pval s₁.mem base b (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hBp, hu₁, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega, Nat.pow_add]
    have : VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat h * val32 s₁.mem base b W ≤ (2 ^ 16 - 1) * m :=
      Nat.mul_le_mul (by omega) (by omega)
    have : (2 ^ 16 - 1) * m + 2 * m < 2 ^ (16 * (2 * W)) * 2 ^ 32 := by
      have : (2 ^ 16 + 1) * m < (2 ^ 16 + 1) * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega)
      omega
    omega
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.mulRow_ok hs₁ h6₁ hp₁ hw hb_le (D := 2 * W) (Nat.le_refl _) (by omega)
    (by omega) (by rw [hu₁]; exact hU) hd hlt₁) fun s₂ ⟨O₂, V₂, D₂, K₂⟩ => ?_
  have K₁₂ := K₁.trans (K₂.mono (by simp))
  have hs₂ := hs.of_rest K₁₂ (by decide)
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁₂.gpr _ (by decide)]; exact h6
  have hp₂ : s₂.gpr .r0 = s₂.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₁₂.gpr _ (by decide), K₁₂.gpr _ (by decide)]; exact hp
  rw [hBp, hu₁] at V₂
  -- q
  refine wp_ldr (hs.off_lt (by omega)) (hs₂.ea_at hp₂ (d := acc) (by omega)) (hs₂.read (by omega))
    fun s₃ u₃ => ?_
  refine wp_movw fun s₄ u₄ => ?_
  refine wp_mul fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  have K₆ : Rest [.r2, .r3, .r5, .r7] s₂ s₆ :=
    ((u₃.rest (by simp)).trans (u₄.rest (by simp))).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  have K₁₆ := K₁₂.trans K₆
  have hs₆ := hs.of_rest K₁₆ (by decide)
  have h6₆ : s₆.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁₆.gpr _ (by decide)]; exact h6
  have hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.gpr _ (by decide), K₆.gpr _ (by decide)]; exact hp₂
  have m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have ht0 : w32 s₂.mem base w = (VG.Proof.Mont.Arm.dval s₁.mem base w (2 * W + 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat h *
      val32 s₁.mem base b W) % 2 ^ 16 := by
    rw [← V₂, VG.Proof.Mont.Arm.dval_low D₂]
  have hq : (s₆.gpr .r2).toNat = w32 s₂.mem base w * (minv16 M).toNat % 2 ^ 16 := by
    have h6₅ : s₅.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]; exact h6₂
    have hmv : (minv16 M).toNat % 2 ^ 32 = (minv16 M).toNat :=
      Nat.mod_eq_of_lt (Nat.lt_trans (minv16 M).isLt (by decide))
    rw [u₆.gpr, dpVal, VG.Proof.Mont.Arm.toNat_and_r6 h6₅, u₅.gpr, BitVec.toNat_mul, u₄.gpr, u₄.other _ (by decide), u₃.gpr,
      BitVec.toNat_setWidth, hmv, Nat.mod_mod_of_dvd _ (show 2 ^ 16 ∣ 2 ^ 32 from ⟨2 ^ 16, by decide⟩), ← hw]
  have hq16 : (s₆.gpr .r2).toNat < 2 ^ 16 := by rw [hq]; exact Nat.mod_lt _ (by decide)
  rw [← m₆] at D₂ V₂ O₂
  have hmo₆ : val32 s₆.mem base M.mo W = m := by
    rw [O₂.val32 (by omega) (by omega)]; exact hm
  have hMp : VG.Proof.Mont.Arm.pval s₆.mem base M.mo (2 * W) = m := by rw [VG.Proof.Mont.Arm.pval_words, hmo₆]
  have hlt₂ : VG.Proof.Mont.Arm.dval s₆.mem base w (2 * W + 2) + (s₆.gpr .r2).toNat * VG.Proof.Mont.Arm.pval s₆.mem base M.mo (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hMp, V₂, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega, Nat.pow_add]
    have hb1 : val32 s₁.mem base b W < m := hB
    have := VG.Proof.Mont.Arm.row_lt hT hU hb1 hq16
    have : 2 ^ 16 * (2 * m) < 2 ^ (16 * (2 * W)) * 2 ^ 32 := by
      have : 2 * 2 ^ 16 * m < 2 * 2 ^ 16 * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega)
      omega
    omega
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.mulRow_ok hs₆ h6₆ hp₆ hw hmo_le (D := 2 * W) (Nat.le_refl _) (by omega)
    (by omega) hq16 D₂ hlt₂) fun s₇ ⟨O₇, V₇, D₇, K₇⟩ => ?_
  have K₁₇ := K₁₆.trans (K₇.mono (by simp))
  refine wp_dp (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  rw [hMp, V₂] at V₇
  have m₈ : s₈.mem = s₇.mem := u₈.mem
  -- The window's low digit is zero, and the one above it too.
  generalize hT1 : VG.Proof.Mont.Arm.dval s₁.mem base w (2 * W + 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat h * val32 s₁.mem base b W = T1 at *
  generalize hqv : (s₆.gpr .r2).toNat = q at *
  have hz : w32 s₇.mem base w = 0 := by
    rw [← VG.Proof.Mont.Arm.dval_low D₇, V₇, show (T1 + q * m) % 2 ^ 16 = (T1 % 2 ^ 16 + q * m) % 2 ^ 16 by omega, hq, ← ht0]
    exact VG.Proof.Mont.Arm.mont_low16 _ _ _ hinv
  have htop' : w32 s₇.mem base (w + 4 * (2 * W + 2)) = 0 := by
    rw [O₇.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega)]; exact htop
  have hsh := VG.Proof.Mont.Arm.dval_shift hz htop'
  refine ⟨?_, ?_, ?_, ⟨q, hq16, ?_⟩, ?_⟩
  · rw [u₈.gpr, dpVal, u₈.other _ (by decide), K₇.gpr _ (by decide), K₇.gpr _ (by decide), hp₆]
    exact VG.Proof.Mont.Arm.ptr_succ _ _
  · rw [m₈, ← u₁.mem]
    exact (O₂.mono (Nat.le_refl _) (by omega)).trans (O₇.mono (Nat.le_refl _) (by omega))
  · intro j hj
    rw [m₈]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [show w + 4 + 4 * j = w + 4 * (j + 1) by omega]; exact D₇ (j + 1) (by omega)
    · rw [show w + 4 + 4 * (2 * W + 1) = w + 4 * (2 * W + 2) by omega, htop']; decide
  · rw [m₈, hsh, V₇, ← hT1, ← u₁.mem]
  · exact ((((K₁.trans (K₂.mono (by simp))).trans K₆).trans (K₇.mono (by simp))).mono
      (ws' := [.r0, .r2, .r3, .r5, .r7]) (by simp)).trans (u₈.rest (by simp))

/-! ## The loop -/

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus (`W`
words) in the working space and apart from the accumulator (`2D + 2 = 4W + 2`
digits at `acc`). -/
structure MulLay (W size acc a b mo : Nat) : Prop where
  acc_le : acc + 4 * (4 * W + 2) ≤ size
  a_le : a + 4 * W ≤ size
  b_le : b + 4 * W ≤ size
  mo_le : mo + 4 * W ≤ size
  sa : a + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ a
  sb : b + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ b
  smo : mo + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ mo

/-- The invariant of the loop, before the iteration for word `k` of `[a]`:
the window of `D + 2` digits at `acc + 8k` holds `T < 2m` with
`2^(32 k) T ≡ A B`, for the low `2k` digits `A` of `[a]`; the digits above
it are zero; `r0`, `r1` point to the window and to word `k`, and `r9` counts
the words left. -/
structure LoopInv (base : Addr) (W acc a b m k : Nat) (s t : State) : Prop where
  r0 : t.gpr .r0 = t.gpr .r12 + BitVec.ofNat 32 (4 * (2 * k))
  r1 : t.gpr .r1 = t.gpr .r12 + BitVec.ofNat 32 (4 * k)
  r9 : t.gpr .r9 = BitVec.ofNat 32 (W - k)
  r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16
  out : Outside base acc (4 * (4 * W + 2)) s.mem t.mem
  rest : Rest VG.Proof.Mont.Arm.clob s t
  digs : VG.Proof.Mont.Arm.Digs t.mem base (acc + 4 * (2 * k)) (2 * W + 2)
  zeros : ∀ l, 2 * k + 2 * W + 2 ≤ l → l < 4 * W + 2 → w32 t.mem base (acc + 4 * l) = 0
  lt : VG.Proof.Mont.Arm.dval t.mem base (acc + 4 * (2 * k)) (2 * W + 2) < 2 * m
  cong : ∃ U, 2 ^ (32 * k) * VG.Proof.Mont.Arm.dval t.mem base (acc + 4 * (2 * k)) (2 * W + 2) =
    VG.Proof.Mont.Arm.pval s.mem base a (2 * k) * val32 s.mem base b W + U * m

/-- The count of the loop, one less. -/
theorem cnt_dec {W k : Nat} (hk : k < W) (hW : W < 2 ^ 32) :
    BitVec.ofNat 32 (W - k) - 1 = BitVec.ofNat 32 (W - (k + 1)) := by
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, BitVec.toNat_ofNat]; omega), h1, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

/-- The congruence of the loop, two digits on. -/
theorem cong_step {P T T' T'' A B m U u0 u1 q0 q1 : Nat} (h0 : P * T = A * B + U * m)
    (h1 : 2 ^ 16 * T' = T + u0 * B + q0 * m) (h2 : 2 ^ 16 * T'' = T' + u1 * B + q1 * m) :
    P * 2 ^ 32 * T'' = (A + u0 * P + u1 * (P * 2 ^ 16)) * B + (U + q0 * P + q1 * (P * 2 ^ 16)) * m := by
  have e1 : P * 2 ^ 32 * T'' = P * (2 ^ 16 * T') + P * 2 ^ 16 * (u1 * B + q1 * m) := by
    rw [show P * 2 ^ 32 * T'' = P * 2 ^ 16 * (2 ^ 16 * T'') by grind, h2]; grind
  have e2 : P * (2 ^ 16 * T') = A * B + U * m + P * u0 * B + P * q0 * m := by
    rw [h1, Nat.mul_add, Nat.mul_add, h0]; grind
  rw [e1, e2]; grind

/-- An iteration of the loop: the rows of the two digits of word `k`. -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {W acc a b m k : Nat}
    (hW : words M = W) (hD : digits M = 2 * W) (hL : VG.Proof.Mont.Arm.MulLay W size acc a b M.mo) (hk : k < W)
    (hW32 : W < 2 ^ 31)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {t : State} (I : VG.Proof.Mont.Arm.LoopInv base W acc a b m k s t) :
    WP isa (.block (row M acc a b)) t fun u =>
      VG.Proof.Mont.Arm.LoopInv base W acc a b m (k + 1) s u ∧ u.z = decide (k + 1 = W) := by
  have hn := hs.nowrap
  obtain ⟨acc_le, a_le, b_le, mo_le, sa, sb, smo⟩ := hL
  have ht := hs.of_rest I.rest (by decide)
  have hmt : val32 t.mem base M.mo W = m := by rw [I.out.val32 (by omega) (by omega), hm]
  have hbt : val32 t.mem base b W = val32 s.mem base b W := I.out.val32 (by omega) (by omega)
  have hat : w32 t.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) := I.out.w32 (by omega) (by omega)
  simp only [row, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldr (hs.off_lt (by omega)) (ht.ea_at I.r1 (d := a) (by omega)) (ht.read (by omega)) fun t₁ u₁ => ?_
  have K₁ : Rest VG.Proof.Mont.Arm.clob t t₁ := u₁.rest (by simp [VG.Proof.Mont.Arm.clob])
  have ht₁ := ht.of_rest K₁ (by decide)
  have r8₁ : (t₁.gpr .r8).toNat = w32 s.mem base (a + 4 * k) := by
    rw [u₁.gpr, ← hat, show 4 * k + a = a + 4 * k by omega]
  have m₁ : t₁.mem = t.mem := u₁.mem
  have L₀ : VG.Proof.Mont.Arm.RowLay W size (acc + 4 * (2 * k)) b M.mo := ⟨b_le, mo_le, by omega, by omega, by omega⟩
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.digitRow_ok ht₁ hW hD rfl L₀ (h := 0) (i := 2 * k) (by decide)
    (by rw [u₁.other _ (by decide)]; exact I.r6) (by rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact I.r0)
    (by omega) (by rw [m₁, hmt]) hinv (by rw [m₁, hbt]; exact hB) (by rw [m₁]; exact I.digs) (by rw [m₁]; exact I.lt)
    (by rw [m₁, show acc + 4 * (2 * k) + 4 * (2 * W + 2) = acc + 4 * (2 * k + 2 * W + 2) by omega];
        exact I.zeros _ (Nat.le_refl _) (by omega))) fun t₂ ⟨p₂, O₂, D₂, ⟨q₀, hq₀, V₂⟩, K₂⟩ => ?_
  have K₁₂ : Rest VG.Proof.Mont.Arm.clob t t₂ := K₁.trans (K₂.mono (by simp [VG.Proof.Mont.Arm.clob]))
  have ht₂ := ht.of_rest K₁₂ (by decide)
  rw [m₁] at O₂ V₂
  have hmt₂ : val32 t₂.mem base M.mo W = m := by rw [O₂.val32 (by omega) (by omega), hmt]
  have hbt₂ : val32 t₂.mem base b W = val32 s.mem base b W := by rw [O₂.val32 (by omega) (by omega), hbt]
  rw [r8₁, hbt] at V₂
  have hU0 := VG.Proof.Mont.Arm.hdig_lt (w32 s.mem base (a + 4 * k)) 0
  have hT' : VG.Proof.Mont.Arm.dval t₂.mem base (acc + 4 * (2 * k) + 4) (2 * W + 2) < 2 * m := by
    have := VG.Proof.Mont.Arm.row_lt I.lt hU0 hB hq₀
    omega
  have L₁ : VG.Proof.Mont.Arm.RowLay W size (acc + 4 * (2 * k) + 4) b M.mo := ⟨b_le, mo_le, by omega, by omega, by omega⟩
  have r8₂ : t₂.gpr .r8 = t₁.gpr .r8 := K₂.gpr _ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.digitRow_ok ht₂ hW hD rfl L₁ (h := 1) (i := 2 * k + 1) (by decide)
    (by rw [K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact I.r6) p₂ (by omega) hmt₂ hinv
    (by rw [hbt₂]; exact hB) D₂ hT'
    (by rw [O₂.w32 (by omega) (by omega), show acc + 4 * (2 * k) + 4 + 4 * (2 * W + 2) =
        acc + 4 * (2 * k + 2 * W + 3) by omega]; exact I.zeros _ (by omega) (by omega)))
    fun t₃ ⟨p₃, O₃, D₃, ⟨q₁, hq₁, V₃⟩, K₃⟩ => ?_
  rw [r8₂, r8₁, hbt₂] at V₃
  refine wp_dp (op2_imm (by decide)) fun t₄ u₄ => ?_
  refine wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have m₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  have r9₄ : t₄.gpr .r9 = BitVec.ofNat 32 (W - k) := by
    rw [u₄.other _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact I.r9
  have hU1 := VG.Proof.Mont.Arm.hdig_lt (w32 s.mem base (a + 4 * k)) 1
  have hT'' : VG.Proof.Mont.Arm.dval t₃.mem base (acc + 4 * (2 * k) + 4 + 4) (2 * W + 2) < 2 * m := by
    have := VG.Proof.Mont.Arm.row_lt hT' hU1 hB hq₁
    omega
  have e8 : acc + 4 * (2 * (k + 1)) = acc + 4 * (2 * k) + 4 + 4 := by omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), p₃]
    congr 2
  · rw [u₅.other _ (by decide), u₄.gpr, dpVal, u₅.other _ (by decide), u₄.other _ (by decide),
      K₃.gpr _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide), K₂.gpr _ (by decide), u₁.other _ (by decide),
      u₁.other _ (by decide), I.r1]
    exact VG.Proof.Mont.Arm.ptr_succ _ _
  · rw [u₅.gpr, r9₄]; exact VG.Proof.Mont.Arm.cnt_dec hk (by omega)
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide),
      u₁.other _ (by decide)]; exact I.r6
  · rw [m₅]
    exact I.out.trans ((O₂.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega)))
  · exact (I.rest.trans K₁₂).trans ((K₃.mono (by simp [VG.Proof.Mont.Arm.clob])).trans
      ((u₄.rest (by simp [VG.Proof.Mont.Arm.clob])).trans (u₅.rest (by simp [VG.Proof.Mont.Arm.clob]))))
  · rw [m₅, e8]; exact D₃
  · intro l hl1 hl2
    rw [m₅, O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega)]
    exact I.zeros l (by omega) hl2
  · rw [m₅, e8]; exact hT''
  · obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + q₀ * 2 ^ (32 * k) + q₁ * (2 ^ (32 * k) * 2 ^ 16), ?_⟩
    have hc := VG.Proof.Mont.Arm.cong_step hU V₂ V₃
    rw [m₅, e8, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add,
      show 2 * (k + 1) = 2 * k + 1 + 1 by omega, VG.Proof.Mont.Arm.pval, VG.Proof.Mont.Arm.pval, hc]
    simp only [VG.Proof.Mont.Arm.pdig, show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k) % 2 = 0 by omega,
      show 16 * (2 * k + 1) = 32 * k + 16 by omega, show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
  · rw [z₅, r9₄, VG.Proof.Mont.Arm.cnt_dec hk (by omega), VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]
    omega

/-- The loop of `mul`: from the invariant at word 0 to the invariant at `W`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {W acc a b m : Nat}
    (hW : words M = W) (hD : digits M = 2 * W) (hL : VG.Proof.Mont.Arm.MulLay W size acc a b M.mo) (hW0 : 0 < W) (hW32 : W < 2 ^ 31)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {t : State} (h0 : VG.Proof.Mont.Arm.LoopInv base W acc a b m 0 s t) :
    WP isa (.loop (.block (row M acc a b)) .ne) t fun u => VG.Proof.Mont.Arm.LoopInv base W acc a b m W s u := by
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = W - k ∧ k < W ∧ VG.Proof.Mont.Arm.LoopInv base W acc a b m k s t') ?_ W t ⟨0, rfl, hW0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (VG.Proof.Mont.Arm.row_ok hs hW hD hL hk hW32 hm hinv hB I) fun u ⟨I', hz⟩ => ?_
  by_cases hk1 : k + 1 = W
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hk1]; rfl, hk1 ▸ I'⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hk1]; rfl, W - (k + 1), by omega,
      k + 1, rfl, by omega, I'⟩

end VG.Proof.Mont.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.Arm.Csub`. -/
section

/-!
# Montgomery arithmetic on 32-bit ARM: the conditional subtraction

`csub M src o` reduces the number `V < 2m` at `[src]` (`D` digits and a top
digit, 0 or 1) modulo `m` into `[o]` (`csub_ok`): the digits of `X - m`, for
the low `D` digits `X`, each `x_j + (2¹⁶ - 1 - m_j)` plus the carry from 1,
are packed into `[tmp]` with the carry out (`diffs_ok`), which plus the top
digit is 1 exactly when `V ≥ m`; its negation is the mask that selects
`V - m` or `V`, packed, into `[o]` (`sels_ok`).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul wp_movw wp_subs op2_reg op2_lsr
  op2_lsl op2_imm dpVal toNat_add_lt toNat_shr toNat_shl)

/-- Two digits packed into a word. -/
theorem pack_toNat (x y : BitVec 32) (hx : x.toNat < 2 ^ 16) :
    (x ||| y <<< 16).toNat = x.toNat + y.toNat % 2 ^ 16 * 2 ^ 16 := by
  rw [BitVec.toNat_or, toNat_shl]
  have e : y.toNat * 2 ^ 16 % 2 ^ 32 = (y.toNat % 2 ^ 16) <<< 16 := by rw [Nat.shiftLeft_eq]; omega
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

theorem toNat_mask16 : (VG.Proof.X25519.Arm.mask16).toNat = 2 ^ 16 - 1 := rfl

/-- Digit `j` of `[src] - m`: `r5 = x_j + (2¹⁶ - 1 - m_j) + c`, its carry to
`r3`, with `r7` the word of `m`. -/
theorem diffDigit_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {src j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hj : src + 4 * j + 4 ≤ size)
    (hx : w32 s.mem base (src + 4 * j) < 2 ^ 16) (hc : (s.gpr .r3).toNat ≤ 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, (u.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2)) +
        (s.gpr .r3).toNat →
      (u.gpr .r3).toNat = (u.gpr .r5).toNat / 2 ^ 16 → u.mem = s.mem → Rest [.r3, .r4, .r5] s u →
      WP isa (.block is) u Q) :
    WP isa (.block (diffDigit src j ++ is)) s Q := by
  simp only [diffDigit, List.cons_append, List.nil_append]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hj) fun s₁ u₁ => ?_
  refine VG.Proof.Mont.Arm.wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  have hd : VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) < 2 ^ 16 := VG.Proof.Mont.Arm.hdig_lt _ _
  have a1 : (s₁.gpr .r5).toNat = w32 s.mem base (src + 4 * j) := by rw [u₁.gpr]
  have a2r5 : s₂.gpr .r5 = s₁.gpr .r5 := u₂.other _ (by decide)
  have a2r4 : (s₂.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega
  have a2r6 : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  have a3 : (s₃.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [a2r5, a1, a2r6, VG.Proof.Mont.Arm.toNat_mask16]; omega), a2r5, a1, a2r6, VG.Proof.Mont.Arm.toNat_mask16]
  have a3r4 : s₃.gpr .r4 = s₂.gpr .r4 := u₃.other _ (by decide)
  have a4 : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2)) := by
    rw [u₄.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by rw [a3, a3r4, a2r4]; omega), a3, a3r4, a2r4]
    omega
  have a4r3 : s₄.gpr .r3 = s.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have a5 : (s₅.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2)) +
      (s.gpr .r3).toNat := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [a4, a4r3]; omega), a4, a4r3]
  refine k s₆ (by rw [u₆.other _ (by decide), a5]) (by rw [u₆.gpr, toNat_shr, u₆.other _ (by decide)])
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) ?_
  exact (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp))))))

/-- Word `k` of `[src] - m`, packed into `[tmp]`: with `c` the carry in and
`x₀`, `x₁` the digits, `[tmp + 4k] + 2³² c' + m_k = x₀ + 2¹⁶ x₁ + 2³² - 1 + c`. -/
theorem diffWord_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {src k : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hsrc : src + 4 * (2 * k + 1) + 4 ≤ size)
    (hmo : M.mo + 4 * k + 4 ≤ size) (htmp : M.tmp + 4 * k + 4 ≤ size)
    (hx0 : w32 s.mem base (src + 4 * (2 * k)) < 2 ^ 16) (hx1 : w32 s.mem base (src + 4 * (2 * k + 1)) < 2 ^ 16)
    (hc : (s.gpr .r3).toNat ≤ 1) :
    WP isa (.block (diffWord M src k)) s fun u =>
      Outside base (M.tmp + 4 * k) 4 s.mem u.mem ∧ (u.gpr .r3).toNat ≤ 1 ∧
      w32 u.mem base (M.tmp + 4 * k) + 2 ^ 32 * (u.gpr .r3).toNat + w32 s.mem base (M.mo + 4 * k) =
        w32 s.mem base (src + 4 * (2 * k)) + 2 ^ 16 * w32 s.mem base (src + 4 * (2 * k + 1)) + (2 ^ 32 - 1) +
          (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8] s u := by
  have hn := hs.nowrap
  simp only [diffWord, List.cons_append, List.append_assoc]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hmo) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r7]) (by simp)) (by decide)
  refine VG.Proof.Mont.Arm.diffDigit_ok hs₁ (j := 2 * k) (by rw [u₁.other _ (by decide)]; exact h6) (by omega)
    (by rw [u₁.mem]; exact hx0) (by rw [u₁.other _ (by decide)]; exact hc) fun s₂ v₂ c₂ m₂ K₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have K₃ : Rest [.r3, .r4, .r5, .r7, .r8] s s₃ :=
    ((u₁.rest (by simp)).trans (K₂.mono (by simp))).trans (u₃.rest (by simp))
  have hs₃ := hs.of_rest K₃ (by decide)
  have hv0 : (s₂.gpr .r5).toNat < 2 ^ 17 := by
    have h1 : w32 s₁.mem base (src + 4 * (2 * k)) < 2 ^ 16 := by rw [u₁.mem]; exact hx0
    have h2 : (s₁.gpr .r3).toNat ≤ 1 := by rw [u₁.other _ (by decide)]; exact hc
    rw [v₂]; omega
  refine VG.Proof.Mont.Arm.diffDigit_ok hs₃ (j := 2 * k + 1) (by rw [K₃.gpr _ (by decide)]; exact h6) (by omega)
    (by rw [u₃.mem, m₂, u₁.mem]; exact hx1) (by rw [u₃.other _ (by decide), c₂]; omega)
    fun s₄ v₄ c₄ m₄ K₄ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s₅ u₅ => ?_
  have K₅ : Rest [.r3, .r4, .r5, .r7, .r8] s s₅ := (K₃.trans (K₄.mono (by simp))).trans (u₅.rest (by simp))
  have hs₅ := hs.of_rest K₅ (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs₅.ea (by omega)) (hs₅.write htmp) fun s₆ m₆ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, m₄, u₃.mem, m₂, u₁.mem]
  have r7₃ : s₃.gpr .r7 = s₁.gpr .r7 := by rw [u₃.other _ (by decide), K₂.gpr _ (by decide)]
  have hr7 : (s₁.gpr .r7).toNat = w32 s.mem base (M.mo + 4 * k) := by rw [u₁.gpr]
  have hm := VG.Proof.Mont.Arm.word_digits (w32 s.mem base (M.mo + 4 * k)) (BitVec.isLt _)
  have hd0 := VG.Proof.Mont.Arm.hdig_lt (w32 s.mem base (M.mo + 4 * k)) 0
  have hd1 := VG.Proof.Mont.Arm.hdig_lt (w32 s.mem base (M.mo + 4 * k)) 1
  have e0 : (s₂.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * k)) +
      (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (w32 s.mem base (M.mo + 4 * k)) 0) + (s.gpr .r3).toNat := by
    rw [v₂, hr7, u₁.mem, u₁.other _ (by decide), show 2 * k % 2 = 0 by omega]
  have e1 : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * k + 1)) +
      (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (w32 s.mem base (M.mo + 4 * k)) 1) + (s₂.gpr .r5).toNat / 2 ^ 16 := by
    rw [v₄, r7₃, hr7, u₃.mem, m₂, u₁.mem, u₃.other _ (by decide), c₂, show (2 * k + 1) % 2 = 1 by omega]
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact h6
  have r8₄ : (s₄.gpr .r8).toNat = (s₂.gpr .r5).toNat % 2 ^ 16 := by
    rw [K₄.gpr _ (by decide), u₃.gpr, dpVal, VG.Proof.Mont.Arm.toNat_and_r6 h6₂]
  have hw : (s₅.gpr .r8).toNat = (s₂.gpr .r5).toNat % 2 ^ 16 + (s₄.gpr .r5).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [u₅.gpr, dpVal, VG.Proof.Mont.Arm.pack_toNat _ _ (by rw [r8₄]; omega), r8₄]
  have r3₆ : (s₆.gpr .r3).toNat = (s₄.gpr .r5).toNat / 2 ^ 16 := by rw [m₆.gpr, u₅.other _ (by decide), c₄]
  refine ⟨?_, ?_, ?_, K₅.trans (m₆.rest _)⟩
  · rw [m₆.mem, m₅]; exact writeW32_outside _ _ _ (by omega)
  · rw [r3₆, e1]; omega
  · rw [m₆.mem, m₅, w32_write_self, hw, r3₆, e0, e1]
    rw [e0] at e1
    omega

/-- The first `k` words of `[src] - m`. -/
def diffK (M : Mod) (src k : Nat) : List Instr := (List.range k).flatMap (diffWord M src)

theorem diffK_succ (M : Mod) (src k : Nat) : VG.Proof.Mont.Arm.diffK M src (k + 1) = VG.Proof.Mont.Arm.diffK M src k ++ diffWord M src k := by
  simp only [VG.Proof.Mont.Arm.diffK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The first `k` words of `[src] - m` into `[tmp]`, from the carry `c`:
`[tmp] + 2^(32k) c' + m_k + 1 = X_k + 2^(32k) + c`, for the low `2k` digits
`X_k` and words `m_k`. -/
theorem diffK_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {src : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (s.gpr .r3).toNat ≤ 1) :
    ∀ {k : Nat}, src + 4 * (2 * k) ≤ size → M.mo + 4 * k ≤ size → M.tmp + 4 * k ≤ size →
    (M.tmp + 4 * k ≤ src ∨ src + 4 * (2 * k) ≤ M.tmp) → (M.tmp + 4 * k ≤ M.mo ∨ M.mo + 4 * k ≤ M.tmp) →
    VG.Proof.Mont.Arm.Digs s.mem base src (2 * k) →
    WP isa (.block (VG.Proof.Mont.Arm.diffK M src k)) s fun u =>
      Outside base M.tmp (4 * k) s.mem u.mem ∧ (u.gpr .r3).toNat ≤ 1 ∧
      val32 u.mem base M.tmp k + 2 ^ (32 * k) * (u.gpr .r3).toNat + val32 s.mem base M.mo k + 1 =
        VG.Proof.Mont.Arm.dval s.mem base src (2 * k) + 2 ^ (32 * k) + (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8] s u
  | 0, _, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, hc,
      by simp only [val32, VG.Proof.Mont.Arm.dval, Nat.mul_zero, Nat.pow_zero]; omega, Rest.refl _ _⟩
  | k + 1, hsrc, hmo, htmp, hts, htm, hd => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.Arm.diffK_succ]
    refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.diffK_ok hs h6 hc (k := k) (by omega) (by omega) (by omega) (by omega)
      (by omega) (hd.mono (by omega))) fun s₁ ⟨O₁, C₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    have x0 : w32 s₁.mem base (src + 4 * (2 * k)) = w32 s.mem base (src + 4 * (2 * k)) := O₁.w32 (by omega) (by omega)
    have x1 : w32 s₁.mem base (src + 4 * (2 * k + 1)) = w32 s.mem base (src + 4 * (2 * k + 1)) :=
      O₁.w32 (by omega) (by omega)
    have mk : w32 s₁.mem base (M.mo + 4 * k) = w32 s.mem base (M.mo + 4 * k) := O₁.w32 (by omega) (by omega)
    refine WP.mono (VG.Proof.Mont.Arm.diffWord_ok hs₁ (k := k) (by rw [K₁.gpr _ (by decide)]; exact h6) (by omega) (by omega)
      (by omega) (by rw [x0]; exact hd _ (by omega)) (by rw [x1]; exact hd _ (by omega)) C₁)
      fun u ⟨O₂, C₂, V₂, K₂⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), C₂, ?_,
        K₁.trans K₂⟩
    rw [x0, x1, mk] at V₂
    have hlow : val32 u.mem base M.tmp k = val32 s₁.mem base M.tmp k := O₂.val32 (by omega) (by omega)
    rw [val32_append _ _ _ k 1, val32_append _ _ _ k 1, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval,
      hlow, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, show 16 * (2 * k + 1) = 32 * k + 16 by omega,
      show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
    simp only [val32, Nat.mul_zero, Nat.add_zero]
    generalize 2 ^ (32 * k) = P at *
    grind

/-- `x ^ ((t ^ x) & mask)`: `t` under the mask of all ones, `x` under 0. -/
theorem select_val (x t : BitVec 32) (b : Bool) :
    x ^^^ ((t ^^^ x) &&& (if b then BitVec.allOnes 32 else 0)) = if b then t else x := by
  cases b
  · simp
  · ext i hi
    simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_allOnes, ite_true, Bool.and_true]
    cases x[i] <;> cases t[i] <;> rfl

/-- Word `k` of `[o]`: of `[tmp]` under the mask, else the packed digits. -/
theorem selWord_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {src o k : Nat}
    (b : Bool) (h3 : s.gpr .r3 = if b then BitVec.allOnes 32 else 0)
    (hsrc : src + 8 * k + 8 ≤ size) (htmp : M.tmp + 4 * k + 4 ≤ size) (ho : o + 4 * k + 4 ≤ size)
    (hx0 : w32 s.mem base (src + 8 * k) < 2 ^ 16) (hx1 : w32 s.mem base (src + 8 * k + 4) < 2 ^ 16) :
    WP isa (.block (selWord M src o k)) s fun u =>
      Outside base (o + 4 * k) 4 s.mem u.mem ∧
      w32 u.mem base (o + 4 * k) = (if b then w32 s.mem base (M.tmp + 4 * k) else
        w32 s.mem base (src + 8 * k) + 2 ^ 16 * w32 s.mem base (src + 8 * k + 4)) ∧
      Rest [.r5, .r7] s u := by
  have hn := hs.nowrap
  simp only [selWord]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (by omega)) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r5, .r7]) (by simp)) (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.read (by omega)) fun s₂ u₂ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s₃ u₃ => ?_
  have K₃ : Rest [.r5, .r7] s s₃ := ((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))
  have hs₃ := hs.of_rest K₃ (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs₃.ea (by omega)) (hs₃.read (by omega)) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  have K₇ : Rest [.r5, .r7] s s₇ := K₃.trans (((u₄.rest (by simp)).trans (u₅.rest (by simp))).trans
    ((u₆.rest (by simp)).trans (u₇.rest (by simp))))
  have hs₇ := hs.of_rest K₇ (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs₇.ea (by omega)) (hs₇.write (by omega)) fun s₈ m₈ => WP.block_nil ?_
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  -- r5 = x₀ | x₁ << 16
  have r5₃ : s₃.gpr .r5 = s.mem.readW (off base (src + 8 * k)) 32 |||
      s.mem.readW (off base (src + 8 * k + 4)) 32 <<< 16 := by
    rw [u₃.gpr, dpVal, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  have r7₄ : s₄.gpr .r7 = s.mem.readW (off base (M.tmp + 4 * k)) 32 := by rw [u₄.gpr, m₃]
  have r5₆ : s₆.gpr .r5 = s₃.gpr .r5 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]
  have r3₅ : s₅.gpr .r3 = s.gpr .r3 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), K₃.gpr _ (by decide)]
  have r7₆ : s₆.gpr .r7 = (s₄.gpr .r7 ^^^ s₃.gpr .r5) &&& s.gpr .r3 := by
    rw [u₆.gpr, dpVal, u₅.gpr, dpVal, u₄.other .r5 (by decide), r3₅]
  have r5₇ : s₇.gpr .r5 = s₃.gpr .r5 ^^^ ((s₄.gpr .r7 ^^^ s₃.gpr .r5) &&& s.gpr .r3) := by
    rw [u₇.gpr, dpVal, r5₆, r7₆]
  refine ⟨?_, ?_, K₇.trans (m₈.rest _)⟩
  · rw [m₈.mem, m₇]; exact writeW32_outside _ _ _ (by omega)
  · rw [m₈.mem, m₇, w32_write_self, r5₇, h3, VG.Proof.Mont.Arm.select_val]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      have e0 : w32 s.mem base (src + 8 * k) = (s.mem.readW (off base (src + 8 * k)) 32).toNat := rfl
      have e1 : w32 s.mem base (src + 8 * k + 4) = (s.mem.readW (off base (src + 8 * k + 4)) 32).toNat := rfl
      rw [e0] at hx0; rw [e1] at hx1
      rw [r5₃, VG.Proof.Mont.Arm.pack_toNat _ _ hx0, e0, e1, Nat.mod_eq_of_lt hx1]; omega
    · simp only [ite_true]; rw [r7₄]

/-- The first `k` words of the selection. -/
def selK (M : Mod) (src o k : Nat) : List Instr := (List.range k).flatMap (selWord M src o)

theorem selK_succ (M : Mod) (src o k : Nat) : VG.Proof.Mont.Arm.selK M src o (k + 1) = VG.Proof.Mont.Arm.selK M src o k ++ selWord M src o k := by
  simp only [VG.Proof.Mont.Arm.selK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The first `k` words of `[o]`: of `[tmp]` under the mask, else the digits
of `[src]`, packed. -/
theorem selK_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {src o : Nat}
    (b : Bool) (h3 : s.gpr .r3 = if b then BitVec.allOnes 32 else 0) :
    ∀ {k : Nat}, src + 8 * k ≤ size → M.tmp + 4 * k ≤ size → o + 4 * k ≤ size →
    (o + 4 * k ≤ src ∨ src + 8 * k ≤ o) → (o + 4 * k ≤ M.tmp ∨ M.tmp + 4 * k ≤ o) →
    VG.Proof.Mont.Arm.Digs s.mem base src (2 * k) →
    WP isa (.block (VG.Proof.Mont.Arm.selK M src o k)) s fun u =>
      Outside base o (4 * k) s.mem u.mem ∧
      val32 u.mem base o k = (if b then val32 s.mem base M.tmp k else VG.Proof.Mont.Arm.dval s.mem base src (2 * k)) ∧
      Rest [.r5, .r7] s u
  | 0, _, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by cases b <;> rfl, Rest.refl _ _⟩
  | k + 1, hsrc, htmp, ho, hos, hot, hd => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.Arm.selK_succ]
    refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.selK_ok hs b h3 (k := k) (by omega) (by omega) (by omega) (by omega)
      (by omega) (hd.mono (by omega))) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    have x0 : w32 s₁.mem base (src + 8 * k) = w32 s.mem base (src + 4 * (2 * k)) := by
      rw [O₁.w32 (by omega) (by omega)]; congr 1; omega
    have x1 : w32 s₁.mem base (src + 8 * k + 4) = w32 s.mem base (src + 4 * (2 * k + 1)) := by
      rw [O₁.w32 (by omega) (by omega)]; congr 1; omega
    have tk : w32 s₁.mem base (M.tmp + 4 * k) = w32 s.mem base (M.tmp + 4 * k) := O₁.w32 (by omega) (by omega)
    refine WP.mono (VG.Proof.Mont.Arm.selWord_ok hs₁ (k := k) b (by rw [K₁.gpr _ (by decide)]; exact h3) (by omega) (by omega)
      (by omega) (by rw [x0]; exact hd _ (by omega)) (by rw [x1]; exact hd _ (by omega)))
      fun u ⟨O₂, V₂, K₂⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), ?_,
        K₁.trans K₂⟩
    rw [x0, x1, tk] at V₂
    have hlow : val32 u.mem base o k = val32 s₁.mem base o k := O₂.val32 (by omega) (by omega)
    rw [val32_append _ _ _ k 1, hlow, V₁, val32_append _ _ _ k 1, show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
      VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval, show 16 * (2 * k + 1) = 32 * k + 16 by omega, show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
    simp only [val32, Nat.mul_zero, Nat.add_zero]
    rw [V₂]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; grind
    · simp only [ite_true]

/-- The result of the conditional subtraction, from the difference's carry
`c` and the top digit `t`. -/
theorem csub_arith {X t T c m P : Nat} (hP : m < P) (hm : 0 < m) (hV : X + P * t < 2 * m) (ht : t ≤ 1)
    (hc : c ≤ 1) (hT : T < P) (hdiff : T + P * c + m = X + P) :
    c + t ≤ 1 ∧ (if c + t = 1 then T else X) = (X + P * t) % m := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
  all_goals obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
  all_goals simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at hV hdiff ⊢
  · exact ⟨by omega, by rw [Nat.mod_eq_of_lt (by omega)]; rfl⟩
  · refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [ite_true]; omega
  · refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [ite_true]; omega
  · omega

/-- `[o] = V mod m` for the number `V < 2m` at `[src]` (`D = 2W` digits and
the top digit), through `[tmp]`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {W src o m : Nat}
    (hW : words M = W) (hD : digits M = 2 * W) (hsrc : src + 4 * (2 * W + 1) ≤ size) (ho : o + 4 * W ≤ size)
    (htmp : M.tmp + 4 * W ≤ size) (hmo : M.mo + 4 * W ≤ size)
    (hts : M.tmp + 4 * W ≤ src ∨ src + 4 * (2 * W + 1) ≤ M.tmp) (htm : M.tmp + 4 * W ≤ M.mo ∨ M.mo + 4 * W ≤ M.tmp)
    (hos : o + 4 * W ≤ src ∨ src + 4 * (2 * W + 1) ≤ o) (hot : o + 4 * W ≤ M.tmp ∨ M.tmp + 4 * W ≤ o)
    (hm : val32 s.mem base M.mo W = m) (hm0 : 0 < m) (hd : VG.Proof.Mont.Arm.Digs s.mem base src (2 * W + 1))
    (hV : VG.Proof.Mont.Arm.dval s.mem base src (2 * W + 1) < 2 * m) :
    WP isa (.block (csub M src o)) s fun u =>
      Outs base [(M.tmp, 4 * W), (o, 4 * W)] s.mem u.mem ∧
      val32 u.mem base o W = VG.Proof.Mont.Arm.dval s.mem base src (2 * W + 1) % m ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8] s u := by
  have hn := hs.nowrap
  simp only [csub, hW, hD, List.cons_append, List.nil_append, List.append_assoc]
  rw [show (List.range W).flatMap (diffWord M src) = VG.Proof.Mont.Arm.diffK M src W from rfl,
    show (List.range W).flatMap (selWord M src o) = VG.Proof.Mont.Arm.selK M src o W from rfl]
  refine wp_movw fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have K₂ : Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have hs₂ := hs.of_rest K₂ (by decide)
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [u₂.other _ (by decide), u₁.gpr]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have c₂ : (s₂.gpr .r3).toNat = 1 := by rw [u₂.gpr]; rfl
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.diffK_ok hs₂ h6₂ (by omega) (k := W) (by omega) hmo htmp (by omega) htm
    (by rw [m₂]; exact hd.mono (by omega))) fun s₃ ⟨O₃, C₃, V₃, K₃⟩ => ?_
  rw [c₂, m₂] at V₃
  rw [m₂] at O₃
  have K₂₃ := K₂.trans (K₃.mono (by simp))
  have hs₃ := hs.of_rest K₂₃ (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs₃.ea (by omega)) (hs₃.read (by omega)) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  -- The digits, the top digit, the carry.
  have hX : VG.Proof.Mont.Arm.dval s.mem base src (2 * W) < 2 ^ (32 * W) := by
    rw [show 32 * W = 16 * (2 * W) by omega]; exact VG.Proof.Mont.Arm.dval_lt (hd.mono (by omega))
  have hsplit : VG.Proof.Mont.Arm.dval s.mem base src (2 * W + 1) = VG.Proof.Mont.Arm.dval s.mem base src (2 * W) +
      w32 s.mem base (src + 4 * (2 * W)) * 2 ^ (32 * W) := by
    rw [VG.Proof.Mont.Arm.dval, show 16 * (2 * W) = 32 * W by omega]
  have htop : w32 s₃.mem base (src + 4 * (2 * W)) = w32 s.mem base (src + 4 * (2 * W)) := O₃.w32 (by omega) (by omega)
  have hmP : m < 2 ^ (32 * W) := by rw [← hm]; exact val32_lt _ _ _ _
  have hT : val32 s₃.mem base M.tmp W < 2 ^ (32 * W) := val32_lt _ _ _ _
  have ht1 : w32 s.mem base (src + 4 * (2 * W)) ≤ 1 := by
    rcases Nat.lt_or_ge (w32 s.mem base (src + 4 * (2 * W))) 2 with h | h
    · omega
    · have := Nat.mul_le_mul_right (2 ^ (32 * W)) h; omega
  obtain ⟨hct, hres⟩ := VG.Proof.Mont.Arm.csub_arith (X := VG.Proof.Mont.Arm.dval s.mem base src (2 * W)) (t := w32 s.mem base (src + 4 * (2 * W)))
    (T := val32 s₃.mem base M.tmp W) (c := (s₃.gpr .r3).toNat) hmP hm0
    (by rw [hsplit, Nat.mul_comm (w32 _ _ _)] at hV; exact hV) ht1 C₃ hT (by rw [hm] at V₃; omega)
  -- The mask.
  have r5₄ : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * W)) := by rw [u₄.gpr, ← htop]
  have r3₄ : s₄.gpr .r3 = s₃.gpr .r3 := u₄.other _ (by decide)
  have r3₅ : (s₅.gpr .r3).toNat = (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [r3₄, r5₄]; omega), r3₄, r5₄]
  have b3 : s₇.gpr .r3 = if (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1 then BitVec.allOnes 32
      else 0 := by
    rw [u₇.gpr, dpVal, u₆.gpr, u₆.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 32).toNat = 0 := rfl
    rcases (by omega : (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 0 ∨
        (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1) with h | h
    · rw [ite_eq_right (by omega), h0]
      have : s₅.gpr .r3 = 0 := BitVec.eq_of_toNat_eq (by rw [r3₅, h0]; omega)
      rw [this]; rfl
    · rw [ite_eq_left h]
      have : s₅.gpr .r3 = 1 := BitVec.eq_of_toNat_eq (by rw [r3₅]; exact h)
      rw [this]; rfl
  have K₇ : Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s₇ := K₂₃.trans (((u₄.rest (by simp)).trans (u₅.rest (by simp))).trans
    ((u₆.rest (by simp)).trans (u₇.rest (by simp))))
  have hs₇ := hs.of_rest K₇ (by decide)
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have b3' : s₇.gpr .r3 = if decide ((s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1) = true then
      BitVec.allOnes 32 else 0 := by simp only [decide_eq_true_eq]; exact b3
  refine WP.mono (VG.Proof.Mont.Arm.selK_ok hs₇ (k := W) _ b3' (by omega) htmp ho (by omega) hot
    (by rw [m₇]; exact (O₃.digs (by omega) (by omega) hd).mono (by omega))) fun u ⟨O₈, V₈, K₈⟩ => ⟨?_, ?_, ?_⟩
  · rw [m₇] at O₈
    exact (Outs.of_outside O₃ (by simp)).trans (Outs.of_outside O₈ (by simp))
  · rw [V₈, m₇, O₃.dval (by omega) (by omega), hsplit, Nat.mul_comm (w32 _ _ _), ← hres]
    by_cases h : (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1
    · simp only [h, ite_true, decide_true]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]
  · exact K₇.trans (K₈.mono (by simp))

end VG.Proof.Mont.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.Arm.Ops`. -/
section

/-!
# Montgomery arithmetic on 32-bit ARM: the operations

For a modulus `m` in the working space (`ModOk`) and an accumulator of
`accLen M` bytes at `acc` apart from the numbers (`OpLay`): `mul acc o a b`
writes `[a] [b] R⁻¹ mod m` to `[o]` (`mul_ok`), `add` writes
`[a] + [b] mod m` (`add_ok`) and `sub` writes `[a] - [b] mod m` (`sub_ok`),
for `[a]`, `[b]` below `m`, in the shape of the other targets' operations
(`n` 64-bit words). Each changes only the registers `clob`, the result, the
temporary area and the accumulator (`OpKeep`).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_lsr op2_imm dpVal
  toNat_add_lt toNat_shr)

/-- The bytes of the accumulator: `2D + 2` digits. -/
def accLen (M : Mod) : Nat := 4 * (2 * digits M + 2)

/-- Where the operations' numbers are: in the working space, and the
accumulator apart from them, from the modulus and from the temporary area,
which `[o]` is apart from too. -/
structure OpLay (M : Mod) (size acc o a b : Nat) : Prop where
  acc_le : acc + VG.Proof.Mont.Arm.accLen M ≤ size
  o_le : o + 8 * M.n ≤ size
  a_le : a + 8 * M.n ≤ size
  b_le : b + 8 * M.n ≤ size
  acc_o : acc + VG.Proof.Mont.Arm.accLen M ≤ o ∨ o + 8 * M.n ≤ acc
  acc_a : acc + VG.Proof.Mont.Arm.accLen M ≤ a ∨ a + 8 * M.n ≤ acc
  acc_b : acc + VG.Proof.Mont.Arm.accLen M ≤ b ∨ b + 8 * M.n ≤ acc
  acc_mo : acc + VG.Proof.Mont.Arm.accLen M ≤ M.mo ∨ M.mo + 8 * M.n ≤ acc
  acc_tmp : acc + VG.Proof.Mont.Arm.accLen M ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ acc
  o_tmp : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions, the stack pointer, and the memory but `[o]`, the temporary area and
the accumulator. -/
structure OpKeep (M : Mod) (base : Addr) (acc o : Nat) (s s' : State) : Prop where
  rest : Rest VG.Proof.Mont.Arm.clob s s'
  mem : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, VG.Proof.Mont.Arm.accLen M)] s.mem s'.mem

theorem m_pos_of_inv {m : Nat} {minv : Nat} (h : (m * minv + 1) % 2 ^ 64 = 0) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · simp at h
  · exact h'

/-- The count of words, an immediate. -/
theorem words_encodable {M : Mod} (h : M.n < 7) : encodable (BitVec.ofNat 32 (words M)) = true := by
  have : ∀ n < 7, encodable (BitVec.ofNat 32 (2 * n)) = true := by decide
  exact this _ h

/-! ## Clearing the accumulator -/

/-- `k` stores of `r7 = 0` from `[acc]`. -/
theorem stores0_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) (h7 : s.gpr .r7 = 0)
    {acc : Nat} : ∀ k, acc + 4 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .str .r7 wb (acc + 4 * j))) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧ (∀ j < k, w32 u.mem base (acc + 4 * j) = 0) ∧ Rest [] s u
  | 0, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      Rest.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.stores0_ok hs h7 k (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    refine wp_str (hs.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.write (d := acc + 4 * k) (n := 4) (by omega))
      fun u m => WP.block_nil ⟨?_, fun j hj => ?_, K₁.trans (m.rest _)⟩
    · rw [m.mem]
      exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
    · rw [m.mem]
      rcases Nat.lt_or_ge j k with h | h
      · rw [w32_write_ne hn (size := size) (by omega) (by omega) (by omega), V₁ j h]
      · rw [show j = k by omega, w32_write_self, K₁.gpr _ (by decide), h7]; rfl

theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc k : Nat}
    (hk : acc + 4 * k ≤ size) {is : List Instr} {Q : State → Prop}
    (h : ∀ u, Outside base acc (4 * k) s.mem u.mem → (∀ j < k, w32 u.mem base (acc + 4 * j) = 0) →
      Rest [.r7] s u → WP isa (.block is) u Q) :
    WP isa (.block (zeros acc k ++ is)) s Q := by
  simp only [zeros, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.stores0_ok (hs.of_rest (u₁.rest (ws := [.r7]) (by simp)) (by decide))
    u₁.gpr k hk) fun u ⟨O, V, K⟩ => h u (u₁.mem ▸ O) V ((u₁.rest (by simp)).trans (K.mono (by simp)))

theorem dval_zero {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (d + 4 * j) = 0) → VG.Proof.Mont.Arm.dval m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval_zero fun j hj => h j (by omega), h k (by omega), Nat.zero_mul]

/-! ## Addition -/

/-- Digit `j` of `[a] + [b]`, from the carry `c`, to `[acc + 4j]`, with `r7`
and `r8` their words. -/
theorem addDigit_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hj : acc + 4 * j + 4 ≤ size) (hc : (s.gpr .r3).toNat ≤ 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Outside base (acc + 4 * j) 4 s.mem u.mem → w32 u.mem base (acc + 4 * j) < 2 ^ 16 →
      w32 u.mem base (acc + 4 * j) + 2 ^ 16 * (u.gpr .r3).toNat =
        VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2) + (s.gpr .r3).toNat →
      (u.gpr .r3).toNat ≤ 1 → Rest [.r3, .r4, .r5] s u → WP isa (.block is) u Q) :
    WP isa (.block (addDigit acc j ++ is)) s Q := by
  have hn := hs.nowrap
  simp only [addDigit, List.cons_append, List.nil_append]
  refine VG.Proof.Mont.Arm.wp_half (Nat.mod_lt _ (by decide)) h6 fun s₁ u₁ => ?_
  refine VG.Proof.Mont.Arm.wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have K₅ : Rest [.r3, .r4, .r5] s s₅ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))))
  have hs₅ := hs.of_rest K₅ (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs₅.ea (by omega)) (hs₅.write hj) fun s₆ m₆ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₇ u₇ => ?_
  have d0 := VG.Proof.Mont.Arm.hdig_lt (s.gpr .r7).toNat (j % 2)
  have d1 := VG.Proof.Mont.Arm.hdig_lt (s.gpr .r8).toNat (j % 2)
  have a1 : (s₁.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) := by rw [u₁.gpr, BitVec.toNat_ofNat]; omega
  have a2 : (s₂.gpr .r5).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega
  have a2r4 : s₂.gpr .r4 = s₁.gpr .r4 := u₂.other _ (by decide)
  have a3 : (s₃.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [a2r4, a1, a2]; omega), a2r4, a1, a2]
  have a3r3 : s₃.gpr .r3 = s.gpr .r3 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have a4 : (s₄.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2) +
      (s.gpr .r3).toNat := by
    rw [u₄.gpr, dpVal, toNat_add_lt (by rw [a3, a3r3]; omega), a3, a3r3]
  have h6₄ : s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact h6
  have a5 : (s₅.gpr .r5).toNat = (s₄.gpr .r4).toNat % 2 ^ 16 := by rw [u₅.gpr, dpVal, VG.Proof.Mont.Arm.toNat_and_r6 h6₄]
  have r4₆ : s₆.gpr .r4 = s₄.gpr .r4 := by rw [m₆.gpr, u₅.other _ (by decide)]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r3₇ : (s₇.gpr .r3).toNat = (s₄.gpr .r4).toNat / 2 ^ 16 := by rw [u₇.gpr, toNat_shr, r4₆]
  have w₇ : w32 s₇.mem base (acc + 4 * j) = (s₄.gpr .r4).toNat % 2 ^ 16 := by
    rw [u₇.mem, m₆.mem, w32_write_self, a5]
  refine k s₇ ?_ (by rw [w₇]; omega) (by rw [w₇, r3₇, a4]; omega) (by rw [r3₇, a4]; omega)
    (K₅.trans ((m₆.rest _).trans (u₇.rest (by simp))))
  rw [u₇.mem, m₆.mem, mem₅]; exact writeW32_outside _ _ _ (by omega)

/-- Word `k` of `[a] + [b]`. -/
def addWord (acc a b k : Nat) : List Instr :=
  [.ldr .r7 wb (a + 4 * k), .ldr .r8 wb (b + 4 * k)] ++ addDigit acc (2 * k) ++ addDigit acc (2 * k + 1)

/-- The first `k` words of `[a] + [b]`. -/
def addK (acc a b k : Nat) : List Instr := (List.range k).flatMap (VG.Proof.Mont.Arm.addWord acc a b)

theorem addK_succ (acc a b k : Nat) : VG.Proof.Mont.Arm.addK acc a b (k + 1) = VG.Proof.Mont.Arm.addK acc a b k ++ VG.Proof.Mont.Arm.addWord acc a b k := by
  simp only [VG.Proof.Mont.Arm.addK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The digits of the first `k` words of `[a] + [b]`, from the carry `c`. -/
theorem addK_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc a b : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (s.gpr .r3).toNat ≤ 1) :
    ∀ {k : Nat}, acc + 4 * (2 * k) ≤ size → a + 4 * k ≤ size → b + 4 * k ≤ size →
    (acc + 4 * (2 * k) ≤ a ∨ a + 4 * k ≤ acc) → (acc + 4 * (2 * k) ≤ b ∨ b + 4 * k ≤ acc) →
    WP isa (.block (VG.Proof.Mont.Arm.addK acc a b k)) s fun u =>
      Outside base acc (4 * (2 * k)) s.mem u.mem ∧ VG.Proof.Mont.Arm.Digs u.mem base acc (2 * k) ∧ (u.gpr .r3).toNat ≤ 1 ∧
      VG.Proof.Mont.Arm.dval u.mem base acc (2 * k) + 2 ^ (32 * k) * (u.gpr .r3).toNat =
        val32 s.mem base a k + val32 s.mem base b k + (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8] s u
  | 0, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      hc, by simp only [val32, VG.Proof.Mont.Arm.dval, Nat.mul_zero, Nat.pow_zero]; omega, Rest.refl _ _⟩
  | k + 1, hacc, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.Arm.addK_succ]
    refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.addK_ok hs h6 hc (k := k) (by omega) (by omega) (by omega)
      (by omega) (by omega)) fun s₁ ⟨O₁, D₁, C₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    simp only [VG.Proof.Mont.Arm.addWord, List.cons_append, List.append_assoc]
    refine wp_ldr (hs.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.read (d := a + 4 * k) (n := 4) (by omega))
      fun s₂ u₂ => ?_
    refine wp_ldr (hs.off_lt (by omega)) ((hs₁.of_rest (u₂.rest (ws := [.r7]) (by simp)) (by decide)).ea
      (by omega)) (by rw [u₂.wr, u₂.rd]; exact hs₁.read (d := b + 4 * k) (n := 4) (by omega)) fun s₃ u₃ => ?_
    have K₃ : Rest [.r3, .r4, .r5, .r7, .r8] s s₃ := K₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
    have hs₃ := hs.of_rest K₃ (by decide)
    refine VG.Proof.Mont.Arm.addDigit_ok hs₃ (j := 2 * k) (by rw [K₃.gpr _ (by decide)]; exact h6) (by omega)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact C₁) fun s₄ O₄ W₄ V₄ C₄ K₄ => ?_
    have K₄' := K₃.trans (K₄.mono (by simp))
    have hs₄ := hs.of_rest K₄' (by decide)
    refine VG.Proof.Mont.Arm.addDigit_ok hs₄ (j := 2 * k + 1) (by rw [K₄'.gpr _ (by decide)]; exact h6) (by omega) C₄
      fun u O₅ W₅ V₅ C₅ K₅ => WP.block_nil ?_
    have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
    have hwa : (s₂.gpr .r7).toNat = w32 s.mem base (a + 4 * k) := by
      rw [u₂.gpr]; exact O₁.w32 (by omega) (by omega)
    have hwb : (s₃.gpr .r8).toNat = w32 s.mem base (b + 4 * k) := by
      rw [u₃.gpr, u₂.mem]; exact O₁.w32 (by omega) (by omega)
    have r7₃ : s₃.gpr .r7 = s₂.gpr .r7 := u₃.other _ (by decide)
    have r7₄ : s₄.gpr .r7 = s₂.gpr .r7 := by rw [K₄.gpr _ (by decide), r7₃]
    have r8₄ : s₄.gpr .r8 = s₃.gpr .r8 := K₄.gpr _ (by decide)
    have r3₃ : s₃.gpr .r3 = s₁.gpr .r3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide)]
    rw [r7₃, hwa, hwb, r3₃, show 2 * k % 2 = 0 by omega] at V₄
    rw [r7₄, hwa, r8₄, hwb, show (2 * k + 1) % 2 = 1 by omega] at V₅
    have O₄' : Outside base acc (4 * (2 * (k + 1))) s₁.mem s₄.mem := by
      rw [← m₃]; exact O₄.mono (by omega) (by omega)
    have O₅' : Outside base acc (4 * (2 * (k + 1))) s₄.mem u.mem := O₅.mono (by omega) (by omega)
    have w0 : w32 u.mem base (acc + 4 * (2 * k)) = w32 s₄.mem base (acc + 4 * (2 * k)) :=
      O₅.w32 (by omega) (by omega)
    have low : ∀ j < 2 * k, w32 u.mem base (acc + 4 * j) = w32 s₁.mem base (acc + 4 * j) := fun j hj => by
      rw [O₅.w32 (by omega) (by omega), O₄.w32 (by omega) (by omega), m₃]
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O₄'.trans O₅'), fun j hj => ?_, C₅, ?_,
      K₄'.trans (K₅.mono (by simp))⟩
    · rcases Nat.lt_or_ge j (2 * k) with h | h
      · rw [low j h]; exact D₁ j h
      · obtain rfl | rfl : j = 2 * k ∨ j = 2 * k + 1 := by omega
        · rw [w0]; exact W₄
        · exact W₅
    · have hd : VG.Proof.Mont.Arm.dval u.mem base acc (2 * k) = VG.Proof.Mont.Arm.dval s₁.mem base acc (2 * k) := VG.Proof.Mont.Arm.dval_congr low
      have ea := VG.Proof.Mont.Arm.word_digits (w32 s.mem base (a + 4 * k)) (BitVec.isLt _)
      have eb := VG.Proof.Mont.Arm.word_digits (w32 s.mem base (b + 4 * k)) (BitVec.isLt _)
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval, hd, w0, val32_append _ _ _ k 1,
        val32_append _ _ _ k 1, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add,
        show 16 * (2 * k + 1) = 32 * k + 16 by omega, show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      generalize 2 ^ (32 * k) = P at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (a + 4 * k)) 0 = a0 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (a + 4 * k)) 1 = a1 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (b + 4 * k)) 0 = b0 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (b + 4 * k)) 1 = b1 at *
      grind

/-! ## Subtraction -/

/-- Digit `j` of `[a] + m - [b]`, from the carry `c`, to `[acc + 4j]`, with
`r7`, `r8` and `r9` the words of `[a]`, `[b]` and `m`. -/
theorem subDigit_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hj : acc + 4 * j + 4 ≤ size) (hc : (s.gpr .r3).toNat ≤ 2)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Outside base (acc + 4 * j) 4 s.mem u.mem → w32 u.mem base (acc + 4 * j) < 2 ^ 16 →
      w32 u.mem base (acc + 4 * j) + 2 ^ 16 * (u.gpr .r3).toNat =
        VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r9).toNat (j % 2) +
          (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2)) + (s.gpr .r3).toNat →
      (u.gpr .r3).toNat ≤ 2 → Rest [.r3, .r4, .r5] s u → WP isa (.block is) u Q) :
    WP isa (.block (subDigit acc j ++ is)) s Q := by
  have hn := hs.nowrap
  simp only [subDigit, List.cons_append, List.nil_append]
  refine VG.Proof.Mont.Arm.wp_half (Nat.mod_lt _ (by decide)) h6 fun s₁ u₁ => ?_
  refine VG.Proof.Mont.Arm.wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  have h6₄ : s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact h6
  refine VG.Proof.Mont.Arm.wp_half (Nat.mod_lt _ (by decide)) h6₄ fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  refine wp_dp (op2_reg _ _) fun s₈ u₈ => ?_
  have K₈ : Rest [.r3, .r4, .r5] s s₈ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans
      ((u₇.rest (by simp)).trans (u₈.rest (by simp))))))))
  have hs₈ := hs.of_rest K₈ (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs₈.ea (by omega)) (hs₈.write hj) fun s₉ m₉ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₁₀ u₁₀ => ?_
  have d0 := VG.Proof.Mont.Arm.hdig_lt (s.gpr .r7).toNat (j % 2)
  have d1 := VG.Proof.Mont.Arm.hdig_lt (s.gpr .r9).toNat (j % 2)
  have d2 := VG.Proof.Mont.Arm.hdig_lt (s.gpr .r8).toNat (j % 2)
  have a1 : (s₁.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) := by rw [u₁.gpr, BitVec.toNat_ofNat]; omega
  have a2 : (s₂.gpr .r5).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r9).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega
  have a2r4 : s₂.gpr .r4 = s₁.gpr .r4 := u₂.other _ (by decide)
  have a3 : (s₃.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r9).toNat (j % 2) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [a2r4, a1, a2]; omega), a2r4, a1, a2]
  have h6₃ : s₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  have a4 : (s₄.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r9).toNat (j % 2) +
      (2 ^ 16 - 1) := by
    rw [u₄.gpr, dpVal, toNat_add_lt (by rw [a3, h6₃, VG.Proof.Mont.Arm.toNat_mask16]; omega), a3, h6₃, VG.Proof.Mont.Arm.toNat_mask16]
  have a5 : (s₅.gpr .r5).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      BitVec.toNat_ofNat]; omega
  have a5r4 : s₅.gpr .r4 = s₄.gpr .r4 := u₅.other _ (by decide)
  have a6 : (s₆.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r9).toNat (j % 2) +
      (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2)) := by
    rw [u₆.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by rw [a5r4, a4, a5]; omega), a5r4, a4, a5]; omega
  have a6r3 : s₆.gpr .r3 = s.gpr .r3 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  have a7 : (s₇.gpr .r4).toNat = VG.Proof.Mont.Arm.hdig (s.gpr .r7).toNat (j % 2) + VG.Proof.Mont.Arm.hdig (s.gpr .r9).toNat (j % 2) +
      (2 ^ 16 - 1 - VG.Proof.Mont.Arm.hdig (s.gpr .r8).toNat (j % 2)) + (s.gpr .r3).toNat := by
    rw [u₇.gpr, dpVal, toNat_add_lt (by rw [a6, a6r3]; omega), a6, a6r3]
  have h6₇ : s₇.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide)]; exact h6₄
  have a8 : (s₈.gpr .r5).toNat = (s₇.gpr .r4).toNat % 2 ^ 16 := by rw [u₈.gpr, dpVal, VG.Proof.Mont.Arm.toNat_and_r6 h6₇]
  have r4₉ : s₉.gpr .r4 = s₇.gpr .r4 := by rw [m₉.gpr, u₈.other _ (by decide)]
  have mem₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r3₁₀ : (s₁₀.gpr .r3).toNat = (s₇.gpr .r4).toNat / 2 ^ 16 := by rw [u₁₀.gpr, toNat_shr, r4₉]
  have w₁₀ : w32 s₁₀.mem base (acc + 4 * j) = (s₇.gpr .r4).toNat % 2 ^ 16 := by
    rw [u₁₀.mem, m₉.mem, w32_write_self, a8]
  refine k s₁₀ ?_ (by rw [w₁₀]; omega) (by rw [w₁₀, r3₁₀, a7]; omega) (by rw [r3₁₀, a7]; omega)
    (K₈.trans ((m₉.rest _).trans (u₁₀.rest (by simp))))
  rw [u₁₀.mem, m₉.mem, mem₈]; exact writeW32_outside _ _ _ (by omega)

/-- Word `k` of `[a] + m - [b]`. -/
def subWord (acc a b mo k : Nat) : List Instr :=
  [.ldr .r7 wb (a + 4 * k), .ldr .r8 wb (b + 4 * k), .ldr .r9 wb (mo + 4 * k)] ++ subDigit acc (2 * k) ++
    subDigit acc (2 * k + 1)

/-- The first `k` words of `[a] + m - [b]`. -/
def subK (acc a b mo k : Nat) : List Instr := (List.range k).flatMap (VG.Proof.Mont.Arm.subWord acc a b mo)

theorem subK_succ (acc a b mo k : Nat) :
    VG.Proof.Mont.Arm.subK acc a b mo (k + 1) = VG.Proof.Mont.Arm.subK acc a b mo k ++ VG.Proof.Mont.Arm.subWord acc a b mo k := by
  simp only [VG.Proof.Mont.Arm.subK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The digits of the first `k` words of `[a] + m - [b]`, from the carry `c`:
`T + 2^(32k) c' + B + 1 = A + M + 2^(32k) + c`. -/
theorem subK_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {acc a b mo : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (s.gpr .r3).toNat ≤ 2) :
    ∀ {k : Nat}, acc + 4 * (2 * k) ≤ size → a + 4 * k ≤ size → b + 4 * k ≤ size → mo + 4 * k ≤ size →
    (acc + 4 * (2 * k) ≤ a ∨ a + 4 * k ≤ acc) → (acc + 4 * (2 * k) ≤ b ∨ b + 4 * k ≤ acc) →
    (acc + 4 * (2 * k) ≤ mo ∨ mo + 4 * k ≤ acc) →
    WP isa (.block (VG.Proof.Mont.Arm.subK acc a b mo k)) s fun u =>
      Outside base acc (4 * (2 * k)) s.mem u.mem ∧ VG.Proof.Mont.Arm.Digs u.mem base acc (2 * k) ∧ (u.gpr .r3).toNat ≤ 2 ∧
      VG.Proof.Mont.Arm.dval u.mem base acc (2 * k) + 2 ^ (32 * k) * (u.gpr .r3).toNat + val32 s.mem base b k + 1 =
        val32 s.mem base a k + val32 s.mem base mo k + 2 ^ (32 * k) + (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8, .r9] s u
  | 0, _, _, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), hc, by simp only [val32, VG.Proof.Mont.Arm.dval, Nat.mul_zero, Nat.pow_zero]; omega,
      Rest.refl _ _⟩
  | k + 1, hacc, ha, hb, hmo, hsa, hsb, hsm => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.Arm.subK_succ]
    refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.subK_ok hs h6 hc (k := k) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)) fun s₁ ⟨O₁, D₁, C₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    simp only [VG.Proof.Mont.Arm.subWord, List.cons_append, List.append_assoc]
    refine wp_ldr (hs.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.read (d := a + 4 * k) (n := 4) (by omega))
      fun s₂ u₂ => ?_
    have hs₂ := hs₁.of_rest (u₂.rest (ws := [.r7]) (by simp)) (by decide)
    refine wp_ldr (hs.off_lt (by omega)) (hs₂.ea (by omega)) (hs₂.read (d := b + 4 * k) (n := 4) (by omega))
      fun s₃ u₃ => ?_
    have hs₃' := hs₂.of_rest (u₃.rest (ws := [.r8]) (by simp)) (by decide)
    refine wp_ldr (hs.off_lt (by omega)) (hs₃'.ea (by omega)) (hs₃'.read (d := mo + 4 * k) (n := 4) (by omega))
      fun s₃' u₃' => ?_
    have K₃ : Rest [.r3, .r4, .r5, .r7, .r8, .r9] s s₃' :=
      K₁.trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₃'.rest (by simp))))
    have hs₃ := hs.of_rest K₃ (by decide)
    refine VG.Proof.Mont.Arm.subDigit_ok hs₃ (j := 2 * k) (by rw [K₃.gpr _ (by decide)]; exact h6) (by omega)
      (by rw [u₃'.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact C₁)
      fun s₄ O₄ W₄ V₄ C₄ K₄ => ?_
    have K₄' := K₃.trans (K₄.mono (by simp))
    have hs₄ := hs.of_rest K₄' (by decide)
    refine VG.Proof.Mont.Arm.subDigit_ok hs₄ (j := 2 * k + 1) (by rw [K₄'.gpr _ (by decide)]; exact h6) (by omega) C₄
      fun u O₅ W₅ V₅ C₅ K₅ => WP.block_nil ?_
    have m₃ : s₃'.mem = s₁.mem := by rw [u₃'.mem, u₃.mem, u₂.mem]
    have hwa : (s₂.gpr .r7).toNat = w32 s.mem base (a + 4 * k) := by
      rw [u₂.gpr]; exact O₁.w32 (by omega) (by omega)
    have hwb : (s₃.gpr .r8).toNat = w32 s.mem base (b + 4 * k) := by
      rw [u₃.gpr, u₂.mem]; exact O₁.w32 (by omega) (by omega)
    have hwm : (s₃'.gpr .r9).toNat = w32 s.mem base (mo + 4 * k) := by
      rw [u₃'.gpr, u₃.mem, u₂.mem]; exact O₁.w32 (by omega) (by omega)
    have r7₃ : s₃'.gpr .r7 = s₂.gpr .r7 := by rw [u₃'.other _ (by decide), u₃.other _ (by decide)]
    have r8₃ : s₃'.gpr .r8 = s₃.gpr .r8 := u₃'.other _ (by decide)
    have r7₄ : s₄.gpr .r7 = s₂.gpr .r7 := by rw [K₄.gpr _ (by decide), r7₃]
    have r8₄ : s₄.gpr .r8 = s₃.gpr .r8 := by rw [K₄.gpr _ (by decide), r8₃]
    have r9₄ : s₄.gpr .r9 = s₃'.gpr .r9 := K₄.gpr _ (by decide)
    have r3₃ : s₃'.gpr .r3 = s₁.gpr .r3 := by
      rw [u₃'.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
    rw [r7₃, hwa, r8₃, hwb, hwm, r3₃, show 2 * k % 2 = 0 by omega] at V₄
    rw [r7₄, hwa, r8₄, hwb, r9₄, hwm, show (2 * k + 1) % 2 = 1 by omega] at V₅
    have O₄' : Outside base acc (4 * (2 * (k + 1))) s₁.mem s₄.mem := by
      rw [← m₃]; exact O₄.mono (by omega) (by omega)
    have O₅' : Outside base acc (4 * (2 * (k + 1))) s₄.mem u.mem := O₅.mono (by omega) (by omega)
    have w0 : w32 u.mem base (acc + 4 * (2 * k)) = w32 s₄.mem base (acc + 4 * (2 * k)) :=
      O₅.w32 (by omega) (by omega)
    have low : ∀ j < 2 * k, w32 u.mem base (acc + 4 * j) = w32 s₁.mem base (acc + 4 * j) := fun j hj => by
      rw [O₅.w32 (by omega) (by omega), O₄.w32 (by omega) (by omega), m₃]
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O₄'.trans O₅'), fun j hj => ?_, C₅, ?_,
      K₄'.trans (K₅.mono (by simp))⟩
    · rcases Nat.lt_or_ge j (2 * k) with h | h
      · rw [low j h]; exact D₁ j h
      · obtain rfl | rfl : j = 2 * k ∨ j = 2 * k + 1 := by omega
        · rw [w0]; exact W₄
        · exact W₅
    · have hd : VG.Proof.Mont.Arm.dval u.mem base acc (2 * k) = VG.Proof.Mont.Arm.dval s₁.mem base acc (2 * k) := VG.Proof.Mont.Arm.dval_congr low
      have ea := VG.Proof.Mont.Arm.word_digits (w32 s.mem base (a + 4 * k)) (BitVec.isLt _)
      have eb := VG.Proof.Mont.Arm.word_digits (w32 s.mem base (b + 4 * k)) (BitVec.isLt _)
      have em := VG.Proof.Mont.Arm.word_digits (w32 s.mem base (mo + 4 * k)) (BitVec.isLt _)
      have b0 := VG.Proof.Mont.Arm.hdig_lt (w32 s.mem base (b + 4 * k)) 0
      have b1 := VG.Proof.Mont.Arm.hdig_lt (w32 s.mem base (b + 4 * k)) 1
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval, hd, w0, val32_append _ _ _ k 1,
        val32_append _ _ _ k 1, val32_append _ _ _ k 1, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add,
        show 16 * (2 * k + 1) = 32 * k + 16 by omega, show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (a + 4 * k)) 0 = a0 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (a + 4 * k)) 1 = a1 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (b + 4 * k)) 0 = b0 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (b + 4 * k)) 1 = b1 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (mo + 4 * k)) 0 = m0 at *
      generalize VG.Proof.Mont.Arm.hdig (w32 s.mem base (mo + 4 * k)) 1 = m1 at *
      have hw : w32 s₄.mem base (acc + 4 * (2 * k)) + 2 ^ 16 * w32 u.mem base (acc + 4 * (2 * k + 1)) +
          2 ^ 32 * (u.gpr .r3).toNat + w32 s.mem base (b + 4 * k) + 1 =
          w32 s.mem base (a + 4 * k) + w32 s.mem base (mo + 4 * k) + 2 ^ 32 + (s₁.gpr .r3).toNat := by omega
      clear V₄ V₅ ea eb em
      generalize 2 ^ (32 * k) = P at *
      grind

/-! ## The operations -/

theorem add_eq (M : Mod) (acc o a b : Nat) : add M acc o a b =
    ([mask16, .mov .r3 (.imm 0)] : List Instr) ++ VG.Proof.Mont.Arm.addK acc a b (words M) ++
      ([.str .r3 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc o :=
  rfl

theorem sub_eq (M : Mod) (acc o a b : Nat) : sub M acc o a b =
    ([mask16, .mov .r3 (.imm 1)] : List Instr) ++ VG.Proof.Mont.Arm.subK acc a b M.mo (words M) ++
      ([.dp .sub .r3 .r3 (.imm 1), .str .r3 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc o :=
  rfl

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {acc o a b : Nat} (hL : VG.Proof.Mont.Arm.OpLay M size acc o a b)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mul M acc o a b) s fun s' => VG.Proof.Mont.Arm.OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hW2 : W = 2 * M.n := hW ▸ rfl
  have hD : digits M = 2 * W := by rw [hW2, digits]; omega
  have hacc : VG.Proof.Mont.Arm.accLen M = 4 * (4 * W + 2) := by rw [VG.Proof.Mont.Arm.accLen, hD]; omega
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0; have := hM.n7
  have hm0 := VG.Proof.Mont.Arm.m_pos_of_inv hM.inv
  have hmv : val32 s.mem base M.mo W = m := by rw [hW2, ← wordsVal_eq_val32]; exact hM.val
  have hBv : val32 s.mem base b W < m := by rw [hW2, ← wordsVal_eq_val32]; exact hB
  have hML : VG.Proof.Mont.Arm.MulLay W size acc a b M.mo :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have himm : encodable (BitVec.ofNat 32 W) = true := hW ▸ VG.Proof.Mont.Arm.words_encodable hM.n7
  simp only [mul, hW, hD]
  refine WP.seq (VG.Proof.Mont.Arm.zeros_ok hs (k := 2 * (2 * W) + 2) (by omega) fun s₁ O₁ Z₁ K₁ => ?_)
  refine wp_movw fun s₂ u₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm himm) fun s₅ u₅ => WP.block_nil ?_
  have K₅ : Rest VG.Proof.Mont.Arm.clob s s₅ := (K₁.mono (by simp [VG.Proof.Mont.Arm.clob])).trans ((u₂.rest (by simp [VG.Proof.Mont.Arm.clob])).trans
    ((u₃.rest (by simp [VG.Proof.Mont.Arm.clob])).trans ((u₄.rest (by simp [VG.Proof.Mont.Arm.clob])).trans (u₅.rest (by simp [VG.Proof.Mont.Arm.clob])))))
  have hs₅ := hs.of_rest K₅ (by decide)
  have mem₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have O₅ : Outside base acc (4 * (4 * W + 2)) s.mem s₅.mem := by
    rw [mem₅]
    exact O₁.mono (Nat.le_refl _) (by omega)
  have Z₅ : ∀ j < 4 * W + 2, w32 s₅.mem base (acc + 4 * j) = 0 := fun j hj => by
    rw [mem₅]; exact Z₁ j (by omega)
  have hm₅ : val32 s₅.mem base M.mo W = m := by rw [O₅.val32 (by omega) (by omega), hmv]
  have hB₅ : val32 s₅.mem base b W < m := by rw [O₅.val32 (by omega) (by omega)]; exact hBv
  have r12₅ : s₅.gpr .r12 = s₂.gpr .r12 := by rw [u₅.other _ (by decide), u₄.other _ (by decide),
    u₃.other _ (by decide)]
  have hz : VG.Proof.Mont.Arm.dval s₅.mem base (acc + 4 * (2 * 0)) (2 * W + 2) = 0 := VG.Proof.Mont.Arm.dval_zero fun j hj => by
    rw [show acc + 4 * (2 * 0) + 4 * j = acc + 4 * j by omega]; exact Z₅ j (by omega)
  have I₀ : VG.Proof.Mont.Arm.LoopInv base W acc a b m 0 s₅ s₅ := by
    refine ⟨?_, ?_, ?_, ?_, VG.Proof.Mont.Outside.refl _ _ _ _, Rest.refl _ _, fun j hj => ?_, fun l h₁ h₂ => ?_,
      by rw [hz]; omega, ⟨0, by rw [hz]; simp only [Nat.mul_zero, VG.Proof.Mont.Arm.pval, Nat.zero_mul, Nat.add_zero]⟩⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, r12₅]; exact (BitVec.add_zero _).symm
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), r12₅]; exact (BitVec.add_zero _).symm
    · rw [u₅.gpr, Nat.sub_zero]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    · rw [show acc + 4 * (2 * 0) + 4 * j = acc + 4 * j by omega, Z₅ j (by omega)]; decide
    · exact Z₅ l h₂
  refine WP.seq (WP.mono (VG.Proof.Mont.Arm.loop_ok hs₅ hW hD hML (by omega) (by omega) hm₅ (VG.Proof.Mont.Arm.minv16_inv hM.inv) hB₅ I₀)
    fun t I => ?_)
  have ht := hs₅.of_rest I.rest (by decide)
  have hmt : val32 t.mem base M.mo W = m := by rw [I.out.val32 (by omega) (by omega), hm₅]
  -- The window's top digit is zero.
  have hmP : m < 2 ^ (32 * W) := by rw [← hmv]; exact val32_lt _ _ _ _
  have htop : VG.Proof.Mont.Arm.dval t.mem base (acc + 4 * (2 * W)) (2 * W + 2) = VG.Proof.Mont.Arm.dval t.mem base (acc + 4 * (2 * W)) (2 * W + 1) := by
    have hlt := I.lt
    rw [VG.Proof.Mont.Arm.dval] at hlt ⊢
    have hp : 2 ^ (32 * W) * 2 ≤ 2 ^ (16 * (2 * W + 1)) := by
      rw [show 16 * (2 * W + 1) = 32 * W + 16 by omega, Nat.pow_add]
      exact Nat.mul_le_mul_left _ (by decide)
    rcases Nat.eq_zero_or_pos (w32 t.mem base (acc + 4 * (2 * W) + 4 * (2 * W + 1))) with h | h
    · rw [h, Nat.zero_mul, Nat.add_zero]
    · have := Nat.mul_le_mul_right (2 ^ (16 * (2 * W + 1))) h
      omega
  have hV : VG.Proof.Mont.Arm.dval t.mem base (acc + 4 * (2 * W)) (2 * W + 1) < 2 * m := htop ▸ I.lt
  refine WP.mono (VG.Proof.Mont.Arm.csub_ok ht hW hD (src := acc + 4 * (2 * W)) (o := o) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hmt hm0 (I.digs.mono (by omega)) hV)
    fun u ⟨O, V, K⟩ => ⟨⟨(K₅.trans I.rest).trans (K.mono (by simp [VG.Proof.Mont.Arm.clob])), ?_⟩, ?_, ?_⟩
  · have O₅' : Outside base acc (VG.Proof.Mont.Arm.accLen M) s.mem s₅.mem := by rw [hacc]; exact O₅
    have Ot : Outside base acc (VG.Proof.Mont.Arm.accLen M) s₅.mem t.mem := by rw [hacc]; exact I.out
    refine ((Outs.of_outside O₅' (by simp)).trans (Outs.of_outside Ot (by simp))).trans ?_
    rw [show 4 * W = 8 * M.n by omega] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hW2, V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [htop, VG.Proof.Mont.Arm.pval_words] at hU
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hW2, V,
      show 64 * M.n = 32 * W by omega, ← O₅.val32 (d := a) (by omega) (by omega),
      ← O₅.val32 (d := b) (by omega) (by omega), Nat.mod_mul_mod, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

/-- `[o] = [a] + [b] mod m`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {acc o a b : Nat} (hL : VG.Proof.Mont.Arm.OpLay M size acc o a b)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M acc o a b)) s fun s' => VG.Proof.Mont.Arm.OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hW2 : W = 2 * M.n := hW ▸ rfl
  have hD : digits M = 2 * W := by rw [hW2, digits]; omega
  have hacc : VG.Proof.Mont.Arm.accLen M = 4 * (4 * W + 2) := by rw [VG.Proof.Mont.Arm.accLen, hD]; omega
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  have hm0 := VG.Proof.Mont.Arm.m_pos_of_inv hM.inv
  rw [VG.Proof.Mont.Arm.add_eq, hW, hD]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have K₂ : Rest VG.Proof.Mont.Arm.clob s s₂ := (u₁.rest (by simp [VG.Proof.Mont.Arm.clob])).trans (u₂.rest (by simp [VG.Proof.Mont.Arm.clob]))
  have hs₂ := hs.of_rest K₂ (by decide)
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [u₂.other _ (by decide), u₁.gpr]
  have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have c₂ : (s₂.gpr .r3).toNat = 0 := by rw [u₂.gpr]; rfl
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.addK_ok hs₂ (a := a) (b := b) (acc := acc) h6₂ (by omega) (k := W)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₃ ⟨O₃, D₃, C₃, V₃, K₃⟩ => ?_
  have K₂₃ := K₂.trans (K₃.mono (by simp [VG.Proof.Mont.Arm.clob]))
  have hs₃ := hs.of_rest K₂₃ (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs₃.ea (by omega)) (hs₃.write (d := acc + 4 * (2 * W)) (n := 4) (by omega))
    fun s₄ m₄ => ?_
  have hs₄ := hs₃.of_rest (m₄.rest []) (by decide)
  rw [mem₂, c₂, Nat.add_zero] at V₃
  rw [mem₂] at O₃
  have O₄ : Outside base acc (4 * (2 * W + 1)) s.mem s₄.mem := by
    rw [m₄.mem]
    exact (O₃.mono (Nat.le_refl _) (by omega)).trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  have low : ∀ j < 2 * W, w32 s₄.mem base (acc + 4 * j) = w32 s₃.mem base (acc + 4 * j) := fun j hj => by
    rw [m₄.mem, w32_write_ne hn (size := size) (by omega) (by omega) (by omega)]
  have top : w32 s₄.mem base (acc + 4 * (2 * W)) = (s₃.gpr .r3).toNat := by rw [m₄.mem, w32_write_self]
  have hsum : VG.Proof.Mont.Arm.dval s₄.mem base acc (2 * W + 1) = val32 s.mem base a W + val32 s.mem base b W := by
    rw [VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval_congr low, top, show 16 * (2 * W) = 32 * W by omega, Nat.mul_comm ((s₃.gpr .r3).toNat), ← V₃]
  have hd₄ : VG.Proof.Mont.Arm.Digs s₄.mem base acc (2 * W + 1) := fun j hj => by
    rcases Nat.lt_or_ge j (2 * W) with h | h
    · rw [low j h]; exact D₃ j h
    · rw [show j = 2 * W by omega, top]; omega
  have hA : val32 s.mem base a W + val32 s.mem base b W < 2 * m := by
    rw [hW2, ← wordsVal_eq_val32, ← wordsVal_eq_val32]; exact hAB
  have hm₄ : val32 s₄.mem base M.mo W = m := by
    rw [O₄.val32 (by omega) (by omega), hW2, ← wordsVal_eq_val32]; exact hM.val
  refine WP.mono (VG.Proof.Mont.Arm.csub_ok hs₄ hW hD (src := acc) (o := o) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hm₄ hm0 hd₄ (by rw [hsum]; exact hA)) fun u ⟨O, V, K⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · exact (K₂₃.trans (m₄.rest _)).trans (K.mono (by simp [VG.Proof.Mont.Arm.clob]))
  · have O₄' : Outside base acc (VG.Proof.Mont.Arm.accLen M) s.mem s₄.mem := O₄.mono (Nat.le_refl _) (by omega)
    refine (Outs.of_outside O₄' (by simp)).trans ?_
    rw [show 4 * W = 8 * M.n by omega] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hW2, V, hsum]

/-- `[o] = [a] - [b] mod m`. -/
theorem sub_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.Arm.Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {acc o a b : Nat} (hL : VG.Proof.Mont.Arm.OpLay M size acc o a b)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M acc o a b)) s fun s' => VG.Proof.Mont.Arm.OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hW2 : W = 2 * M.n := hW ▸ rfl
  have hD : digits M = 2 * W := by rw [hW2, digits]; omega
  have hacc : VG.Proof.Mont.Arm.accLen M = 4 * (4 * W + 2) := by rw [VG.Proof.Mont.Arm.accLen, hD]; omega
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  have hm0 := VG.Proof.Mont.Arm.m_pos_of_inv hM.inv
  have hmv : val32 s.mem base M.mo W = m := by rw [hW2, ← wordsVal_eq_val32]; exact hM.val
  have hAv : val32 s.mem base a W < m := by rw [hW2, ← wordsVal_eq_val32]; exact hA
  have hBv : val32 s.mem base b W < m := by rw [hW2, ← wordsVal_eq_val32]; exact hB
  have hmP : m < 2 ^ (32 * W) := by rw [← hmv]; exact val32_lt _ _ _ _
  rw [VG.Proof.Mont.Arm.sub_eq, hW, hD]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have K₂ : Rest VG.Proof.Mont.Arm.clob s s₂ := (u₁.rest (by simp [VG.Proof.Mont.Arm.clob])).trans (u₂.rest (by simp [VG.Proof.Mont.Arm.clob]))
  have hs₂ := hs.of_rest K₂ (by decide)
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [u₂.other _ (by decide), u₁.gpr]
  have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have c₂ : (s₂.gpr .r3).toNat = 1 := by rw [u₂.gpr]; rfl
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Mont.Arm.subK_ok hs₂ (a := a) (b := b) (mo := M.mo) (acc := acc) h6₂ (by omega)
    (k := W) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₃ ⟨O₃, D₃, C₃, V₃, K₃⟩ => ?_
  rw [mem₂, c₂, hmv] at V₃
  rw [mem₂] at O₃
  have hT : VG.Proof.Mont.Arm.dval s₃.mem base acc (2 * W) < 2 ^ (32 * W) := by
    rw [show 32 * W = 16 * (2 * W) by omega]; exact VG.Proof.Mont.Arm.dval_lt D₃
  have hc1 : 1 ≤ (s₃.gpr .r3).toNat := by
    rcases Nat.eq_zero_or_pos (s₃.gpr .r3).toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at V₃; omega
    · exact h
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  have K₂₄ := (K₂.trans (K₃.mono (by simp [VG.Proof.Mont.Arm.clob]))).trans (u₄.rest (by simp [VG.Proof.Mont.Arm.clob]))
  have hs₄ := hs.of_rest K₂₄ (by decide)
  have r3₄ : (s₄.gpr .r3).toNat = (s₃.gpr .r3).toNat - 1 := by
    rw [u₄.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by exact hc1)]; rfl
  refine wp_str (hs.off_lt (by omega)) (hs₄.ea (by omega)) (hs₄.write (d := acc + 4 * (2 * W)) (n := 4) (by omega))
    fun s₅ m₅ => ?_
  have hs₅ := hs₄.of_rest (m₅.rest []) (by decide)
  have mem₄ : s₄.mem = s₃.mem := u₄.mem
  have O₅ : Outside base acc (4 * (2 * W + 1)) s.mem s₅.mem := by
    rw [m₅.mem, mem₄]
    exact (O₃.mono (Nat.le_refl _) (by omega)).trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  have low : ∀ j < 2 * W, w32 s₅.mem base (acc + 4 * j) = w32 s₃.mem base (acc + 4 * j) := fun j hj => by
    rw [m₅.mem, mem₄, w32_write_ne hn (size := size) (by omega) (by omega) (by omega)]
  have top : w32 s₅.mem base (acc + 4 * (2 * W)) = (s₃.gpr .r3).toNat - 1 := by
    rw [m₅.mem, w32_write_self, r3₄]
  have hdiff : VG.Proof.Mont.Arm.dval s₅.mem base acc (2 * W + 1) = val32 s.mem base a W + m - val32 s.mem base b W := by
    rw [VG.Proof.Mont.Arm.dval, VG.Proof.Mont.Arm.dval_congr low, top, show 16 * (2 * W) = 32 * W by omega]
    have e : ((s₃.gpr .r3).toNat - 1) * 2 ^ (32 * W) + 2 ^ (32 * W) = 2 ^ (32 * W) * (s₃.gpr .r3).toNat := by
      rw [Nat.mul_comm, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hc1]
    omega
  have hd₅ : VG.Proof.Mont.Arm.Digs s₅.mem base acc (2 * W + 1) := fun j hj => by
    rcases Nat.lt_or_ge j (2 * W) with h | h
    · rw [low j h]; exact D₃ j h
    · rw [show j = 2 * W by omega, top]; omega
  have hm₅ : val32 s₅.mem base M.mo W = m := by rw [O₅.val32 (by omega) (by omega), hmv]
  refine WP.mono (VG.Proof.Mont.Arm.csub_ok hs₅ hW hD (src := acc) (o := o) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hm₅ hm0 hd₅ (by rw [hdiff]; omega)) fun u ⟨O, V, K⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · exact (K₂₄.trans (m₅.rest _)).trans (K.mono (by simp [VG.Proof.Mont.Arm.clob]))
  · have O₅' : Outside base acc (VG.Proof.Mont.Arm.accLen M) s.mem s₅.mem := O₅.mono (Nat.le_refl _) (by omega)
    refine (Outs.of_outside O₅' (by simp)).trans ?_
    rw [show 4 * W = 8 * M.n by omega] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hW2, V, hdiff]

end VG.Proof.Mont.Arm

end
