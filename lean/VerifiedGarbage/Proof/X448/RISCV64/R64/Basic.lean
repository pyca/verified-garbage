module

import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.X448.RISCV64.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Wide
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# X448 on RISC-V, 64-bit limbs: words of the working space

A field element's 56 bytes at `o` are seven doublewords (`dw`) as well as
fourteen words (`limb`): `V` is `val7` of the doublewords (`V_eq`). The
doublewords of memory after a store (`dw_write_self`, `dw_write_other`) and
through a frame (`dw_frame`); a doubleword load and store of the working
space (`ld_ok`, `sd_ok`); and the registers the field arithmetic changes
(`clob64`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Proof.X448.RISCV64 (V)

/-- The registers the field arithmetic changes. -/
abbrev clob64 : List Reg := [.t0, .t3, .t4, .t5, .t6, .a1, .a2, .a4, .a5, .a6, .a7]

/-- The doubleword at `P + d`, as a number. -/
def dw (m : Mem) (P : Addr) (d : Nat) : Nat := (m.readW (P + BitVec.ofNat 64 d) 64).toNat

theorem dw_lt (m : Mem) (P : Addr) (d : Nat) : dw m P d < 2 ^ 64 := (m.readW _ 64).isLt

/-- A doubleword is its two words. -/
theorem dw_split (m : Mem) (P : Addr) (d : Nat) : dw m P d = wd m P d + 2 ^ 32 * wd m P (d + 4) := by
  unfold dw wd
  rw [Words64.readW64_split, Offset.add_add]
  have h1 := (m.readW (P + BitVec.ofNat 64 d) 32).isLt
  have h2 := (m.readW (P + BitVec.ofNat 64 (d + 4)) 32).isLt
  generalize m.readW (P + BitVec.ofNat 64 d) 32 = lo at *
  generalize m.readW (P + BitVec.ofNat 64 (d + 4)) 32 = hi at *
  have e : (hi.setWidth 64 <<< 32 ||| lo.setWidth 64) = hi.setWidth 64 <<< 32 + lo.setWidth 64 := by
    rw [BitVec.add_eq_or_of_and_eq_zero]
    ext i hi'
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getElem_zero]
    by_cases h : i < 32
    · simp [h]
    · simp [h, BitVec.getLsbD_of_ge lo i (by omega)]
  rw [e, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : hi.toNat < 2 ^ 64),
    Nat.shiftLeft_eq]
  omega_using [h1, h2]

/-- Seven doublewords, lowest first. -/
def val7 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
    2 ^ 64 * f 6)))))

theorem val7_congr {f g : Nat → Nat} (h : ∀ i < 7, f i = g i) : val7 f = val7 g := by
  unfold val7
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide)]

theorem val7_lt {f : Nat → Nat} (h : ∀ i < 7, f i < 2 ^ 64) : val7 f < (2 ^ 64) ^ 7 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide)
  have := h 3 (by decide); have := h 4 (by decide); have := h 5 (by decide)
  have := h 6 (by decide)
  unfold val7; omega_arith

/-- The doublewords of the element at `o`. -/
abbrev ew (m : Mem) (P : Addr) (o : Nat) (i : Nat) : Nat := dw m P (o + 8 * i)

/-- The number of an element is its seven doublewords. -/
theorem V_eq (m : Mem) (P : Addr) (o : Nat) : V m P o = val7 (ew m P o) := by
  simp only [V, val7, ew, val32, limb, dw_split]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
  omega_arith

/-! ## Bits -/

/-- An `or` of disjoint bits is their sum. -/
theorem or_add {x y : BitVec 64} (h : x &&& y = 0#64) (hb : x.toNat + y.toNat < 2 ^ 64) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ h, BitVec.toNat_add, Nat.mod_eq_of_lt hb]

/-- `x` shifted left by one, with a bit `y` in bit 0. -/
theorem dbl_or (x y : BitVec 64) (hy : y.toNat ≤ 1) :
    (x <<< 1 ||| y).toNat = x.toNat * 2 % 2 ^ 64 + y.toNat := by
  have h01 : y = 0#64 ∨ y = 1#64 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hand : x <<< 1 &&& y = 0#64 := by
    rcases h01 with rfl | rfl
    · simp
    · ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_one, BitVec.getElem_zero]
      by_cases h0 : i = 0 <;> simp [h0]
  have e : (x <<< 1).toNat = x.toNat * 2 % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have : x.toNat * 2 % 2 ^ 64 % 2 = 0 := by omega
  rw [or_add hand (by rw [e]; omega), e]

/-- The upper half of `h` and the lower half of `h'`, as a doubleword. -/
theorem rot_or (h h' : BitVec 64) :
    (h >>> 32 ||| h' <<< 32).toNat = h.toNat / 2 ^ 32 + 2 ^ 32 * (h'.toNat % 2 ^ 32) := by
  have hand : h >>> 32 &&& h' <<< 32 = 0#64 := by
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft, BitVec.getElem_zero]
    by_cases hl : i < 32
    · simp [hl]
    · simp only [hl, decide_false, Bool.not_false, Bool.true_and]
      rw [BitVec.getLsbD_of_ge h (32 + i) (by omega)]; simp
  have := h.isLt; have := h'.isLt
  rw [or_add hand, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  · omega
  · rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega

/-! ## Memory -/

theorem dw_write_self (m : Mem) (P : Addr) (d : Nat) (v : BitVec 64) :
    dw (m.writeW (P + BitVec.ofNat 64 d) v) P d = v.toNat := by
  rw [dw, Mem.readW_writeW_self64]

theorem dw_write_other (m : Mem) (P : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    dw (m.writeW (P + BitVec.ofNat 64 e) v) P d = dw m P d := by
  rw [dw, Mem.readW_writeW_sep (Offset.sep P h hd he) (by decide), dw]

theorem dw_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {d : Nat}
    (hd : ∀ r ∈ rs, (⟨P + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) : dw m' P d = dw m P d := by
  rw [dw, dw, hf.readW (Region.contains_self _ _) hd (by decide)]

/-- An address `P + d` is a multiple of 8 if `P` and `d` are. -/
theorem al8 {P : Addr} (hP : P.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) :
    (P + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

section
variable {b : Addr} {is : List Instr} {s : State} {Q : State → Prop}

/-- `ld t, d(a3)` in the working space. -/
theorem ld_ok (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 8 ≤ 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Upd s s' t (s.mem.readW (b + BitVec.ofNat 64 d) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t .a3 d :: is)) s Q :=
  wp_ld (by omega) (by rw [hc.a3]) (al8 hc.al hd8) (hc.inR hd) k

/-- `sd t, d(a3)` in the working space. -/
theorem sd_ok (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 8 ≤ 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t .a3 d :: is)) s Q :=
  wp_sd (by omega) (by rw [hc.a3]) (al8 hc.al hd8) (hc.inW hd) k

end

end VG.Proof.X448.RISCV64.R64
