module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! ### `Bignum.X86_64.CrtExp5`, which only this module used -/

section

/-! ### `Bignum.CrtWin5`, which only this module used -/

section

/-!
# RSA with the CRT: the exponent's bits for windows of 5 bits

`expLoop5S` (`Impl/Rsa/X86_64/Crt.lean`) reads an exponent of `L` bytes
after `padBits L = 2 L mod 5` zero bits, which make its bits a whole number
of windows (`win5_dvd`). The bits read but not yet in a window are kept at
the top of a word: `b` of them, the low `b` bits of the value `P` of the
bytes read, as `(P mod 2^b) 2^(64 - b)`, and the windows taken so far are
`⌊P / 2^b⌋`. A byte more goes below them (`refill_word`, `refill_val`),
and a window is the word's top 5 bits (`take_hi`, `take_lo`, `take_val`).
These are the facts about it that do not depend on the target.
-/

@[expose] public section

namespace VG.Proof.Bignum

/-- The zero bits before an exponent of `L` bytes: `2 L mod 5`. -/
def padBits (L : Nat) : Nat := 2 * L % 5

theorem padBits_lt (L : Nat) : padBits L < 5 := Nat.mod_lt _ (by decide)

/-- The padded exponent is a whole number of windows. -/
theorem win5_dvd (L : Nat) : (padBits L + 8 * L) % 5 = 0 := by unfold padBits; omega_using []

/-- `⌊L / 5⌋` by a multiplication: the high word of `L M`, for
`M = ⌈2^66 / 5⌉`, shifted right by 2. -/
theorem div5_magic {L : Nat} (h : L < 2 ^ 32) :
    L * 0xCCCCCCCCCCCCCCCD / 2 ^ 64 / 2 ^ 2 = L / 5 := by
  simp only [Nat.reducePow] at *
  omega_using [h]

/-- The padding from `L mod 5`: `2 (L mod 5)`, less 5 if that is not below
5. -/
theorem padBits_eq (L : Nat) : (if 2 * (L % 5) < 5 then 2 * (L % 5) else 2 * (L % 5) - 5) = padBits L := by
  unfold padBits
  split <;> omega_arith

/-! ## The bits at the top of a word -/

/-- The top 5 of `b ≥ 5` bits at the top of a word. -/
theorem take_hi {r b : Nat} (hb : 5 ≤ b) (hb' : b ≤ 12) (hr : r < 2 ^ b) :
    BitVec.ofNat 64 (r * 2 ^ (64 - b)) >>> 59 = BitVec.ofNat 64 (r / 2 ^ (b - 5)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rcases (by omega_using [hb, hb'] : b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceSub] at * <;> omega_using [hr]

/-- The bits below them, moved up 5. -/
theorem take_lo {r b : Nat} (hb : 5 ≤ b) (hb' : b ≤ 12) (hr : r < 2 ^ b) :
    BitVec.ofNat 64 (r * 2 ^ (64 - b)) <<< 5 = BitVec.ofNat 64 (r % 2 ^ (b - 5) * 2 ^ (64 - (b - 5))) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rcases (by omega_using [hb, hb'] : b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceSub] at * <;> omega_using []

/-- A byte below `b < 5` bits at the top of a word, by a multiplication by
`2^(56 - b)` and an or. -/
theorem refill_word {r b y : Nat} (hb : b < 5) (hr : r < 2 ^ b) (hy : y < 256) :
    BitVec.ofNat 64 y * BitVec.ofNat 64 (2 ^ (56 - b)) ||| BitVec.ofNat 64 (r * 2 ^ (64 - b)) =
      BitVec.ofNat 64 ((256 * r + y) * 2 ^ (56 - b)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have hp : 2 ^ (64 - b) = 2 ^ 8 * 2 ^ (56 - b) := by rw [← Nat.pow_add]; congr 1; omega_using [hb]
  have h56 : 2 ^ (56 - b) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega_using [])
  have hb2 : 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega_using [hb])
  have hlo : y * 2 ^ (56 - b) < 2 ^ (64 - b) := by
    rw [hp]; exact Nat.mul_lt_mul_of_pos_right (by omega_using [hy]) (Nat.two_pow_pos _)
  have h64 : 2 ^ (64 - b) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega_using [])
  have hlo' : y % 2 ^ 64 * (2 ^ (56 - b) % 2 ^ 64) % 2 ^ 64 = y * 2 ^ (56 - b) := by
    rw [Nat.mod_eq_of_lt (by omega_using [hy] : y < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [h56] : 2 ^ (56 - b) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_using [hp, h56, hlo] : y * 2 ^ (56 - b) < 2 ^ 64)]
  have hhi : r * 2 ^ (64 - b) < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos (64 - b))
    rwa [← Nat.pow_add, show b + (64 - b) = 64 by omega_using [hb]] at this
  rw [hlo', Nat.mod_eq_of_lt hhi, Nat.or_comm, Nat.mul_comm r, ← Nat.two_pow_add_eq_or_of_lt hlo]
  have hr1 : 2 ^ (64 - b) * (r + 1) ≤ 2 ^ 64 := by
    have := Nat.mul_le_mul_left (2 ^ (64 - b)) (show r + 1 ≤ 2 ^ b by omega_using [hr])
    rwa [← Nat.pow_add, show 64 - b + b = 64 by omega_using [hb]] at this
  have key : 2 ^ (64 - b) * r + y * 2 ^ (56 - b) = (256 * r + y) * 2 ^ (56 - b) := by rw [hp]; grind
  rw [← key, Nat.mod_eq_of_lt (by rw [Nat.mul_add, Nat.mul_one] at hr1; omega_using [hlo, hr1])]

/-! ## The exponent's value -/

/-- A byte `y` more: `P' = 256 P + y`, with `b + 8` bits left. -/
theorem refill_val {P y b : Nat} (hy : y < 256) :
    (256 * P + y) % 2 ^ (b + 8) = 256 * (P % 2 ^ b) + y ∧ (256 * P + y) / 2 ^ (b + 8) = P / 2 ^ b := by
  have e : 2 ^ (b + 8) = 2 ^ b * 256 := Nat.pow_add 2 b 8
  have hb := Nat.two_pow_pos b
  have hlt : 256 * (P % 2 ^ b) + y < 2 ^ b * 256 := by have := Nat.mod_lt P hb; omega_using [hy]
  have hP : 256 * P + y = 256 * (P % 2 ^ b) + y + 2 ^ b * 256 * (P / 2 ^ b) := by
    have := Nat.div_add_mod P (2 ^ b); grind
  rw [e, hP, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ (by omega_using [hb]),
    Nat.div_eq_of_lt hlt, Nat.zero_add]
  exact ⟨rfl, rfl⟩

/-- A window of the top 5 of `b ≥ 5` bits: `32 ⌊P / 2^b⌋ + v`, with
`b - 5` bits left. -/
theorem take_val {P b : Nat} (hb : 5 ≤ b) :
    P / 2 ^ (b - 5) = 32 * (P / 2 ^ b) + P % 2 ^ b / 2 ^ (b - 5) ∧
      P % 2 ^ (b - 5) = P % 2 ^ b % 2 ^ (b - 5) := by
  have e : 2 ^ b = 2 ^ (b - 5) * 32 := by rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add]; congr 1; omega_using [hb]
  rw [e]
  refine ⟨?_, (Nat.mod_mul_right_mod _ _ _).symm⟩
  rw [Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (P / 2 ^ (b - 5)) 32
  omega_using []

end VG.Proof.Bignum

end

end


/-!
# RSA with the CRT on x86-64: the exponentiation by windows of 5 bits

`Crt.expLoop5S` (`Impl/Rsa/X86_64/Crt.lean`): `tabBuildN` writes the table
of the 32 powers, then each window takes the top 5 of the exponent's bits
kept at the top of `sV`, after `padBits L` zero bits (`padInit_ok`), a byte
more read below them when fewer than 5 are left (`refill_ok`).

The bits are those of `CrtWin5.lean`: after `i` bytes, with `b` bits left,
`sV = (P mod 2^b) 2^(64 - b)` for the value `P` of the bytes read,
`sPow = 2^(56 - b)`, and `Y ≡ x^⌊P / 2^b⌋ R`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## What the exponentiation changes -/

/-- What `expLoop5S` changes: `crtExpRanges` with a table of 32 entries, and
`sPow`. -/
def crtExpRanges5 (wx : Nat) : List (Nat × Nat) := (8 * Crt.sPow, 8) :: crtExpRanges wx 32

theorem crtExpRanges_sub5 (wx : Nat) : ∀ r ∈ crtExpRanges wx 32, r ∈ crtExpRanges5 wx :=
  fun _ h => List.mem_cons_of_mem _ h

theorem crtExpRanges5_ok (wx : Nat) :
    ∀ r ∈ crtExpRanges5 wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx 32 := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot wx 8 (show Crt.sPow < 32 by decide)
    simp only [Crt.sPow, sFn] at *; omega_arith
  · exact crtExpRanges_ok wx r hr

theorem crtExpRanges5_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ Crt.aT) : ∀ r ∈ crtExpRanges5 wx, slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot wx j (show Crt.sPow < 32 by decide)
    simp only [Crt.sPow, sFn] at *; omega_arith
  · exact crtExpRanges_arr wx hj h1 h2 h3 h4 (n := 32) r hr

/-- Two different header words are disjoint. -/
theorem hdr_sep {k s : Nat} (h : k ≠ s) : 8 * k + 8 ≤ 8 * s ∨ 8 * s + 8 ≤ 8 * k := by omega_using [h]

/-- A header slot that `expLoop5S`'s ranges miss. -/
theorem crtExpRanges5_hdr (wx : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ Crt.sPow) (h1 : k ≠ Crt.sExp)
    (h2 : k ≠ Crt.sExpLen) (h3 : k ≠ Crt.sI) (h4 : k ≠ Crt.sTab) (h5 : k ≠ Crt.sV) (h6 : k ≠ Crt.sBit)
    (h7 : k ≠ Crt.sNib) (h8 : k ≠ Crt.sEnt) (h9 : k ≠ Crt.sJ) :
    ∀ r ∈ crtExpRanges5 wx, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [crtExpRanges5, crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [hdr_sep h0, hdr_sep h1, hdr_sep h2, hdr_sep h3, hdr_sep h4, Or.inl (hdr_lt_slot wx _ hk),
    Or.inl (hdr_lt_slot wx _ hk), Or.inl (hdr_lt_slot wx _ hk), Or.inl (hdr_lt_slot wx _ hk),
    Or.inl (hdr_lt_slot wx _ hk), hdr_sep h5, hdr_sep h6, hdr_sep h7, hdr_sep h8, hdr_sep h9]

/-- What changes only within `expLoop5S`'s ranges keeps the context. -/
theorem CExpCtx.of_frm5 {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc 32) (hf : Frm P (crtExpRanges5 wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : CExpCtx t' P wx minv X Xc 32 := by
  have hn := hc.scrT.nowrap
  have rN := crtExpRanges5_arr wx (j := aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rX := crtExpRanges5_arr wx (j := Crt.aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lX := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hh : ∀ i < 17, word t'.mem P (8 * i) = word t.mem P (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => Or.inl (by have := crtExpRanges5_ok wx r hr; omega_arith))
      (by have := hdr_lt_slot wx 8 (show i < 32 by omega_arith); omega_arith)
  exact ⟨⟨hc.good.scr.congr hwr, hdi.trans hc.good.rdi,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩, hc.scrT.congr hwr,
    by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.inv,
    by rw [hf.wv_eq (fun r hr => by have := rX r hr; omega_arith) (by omega_arith)]; exact hc.x⟩

/-- The prime's workspace with room for a table of 32 entries. -/
theorem SubCtx.scr32 {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv)
    (hT : o + slot wx 8 + wsTab wx ≤ Z) : Scr t (off B o) (slot wx 8 + tabBytes wx 32) :=
  h.scr.sub (by simp only [wsTab] at hT; omega_arith) (by unfold slot hdrBytes; omega_arith)

/-! ## The padding -/

theorem toNat_ofNat_of_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `⌊L / 5⌋`: the high word of `L M` shifted right by 2. -/
theorem div5_bv {L : Nat} (hL : L < 2 ^ 32) :
    BitVec.ofNat 64 ((0xCCCCCCCCCCCCCCCD : BitVec 64).toNat * (BitVec.ofNat 64 L).toNat / 2 ^ 64) >>> 2 =
      BitVec.ofNat 64 (L / 5) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_of_lt (by omega_arith : L < 2 ^ 64), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0xCCCCCCCCCCCCCCCD : BitVec 64).toNat = 0xCCCCCCCCCCCCCCCD from rfl, Nat.mul_comm,
    toNat_ofNat_of_lt (by simp only [Nat.reducePow] at *; omega_arith), toNat_ofNat_of_lt (by omega_arith), div5_magic hL]

/-- `2 (L mod 5)` from `⌊L / 5⌋` by additions and a subtraction. -/
theorem mod5x2_bv (L : Nat) :
    (BitVec.ofNat 64 L - (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5) +
        (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5)) + BitVec.ofNat 64 (L / 5))) +
      (BitVec.ofNat 64 L - (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5) +
        (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5)) + BitVec.ofNat 64 (L / 5))) =
      BitVec.ofNat 64 (2 * (L % 5)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `rdx := ⌊L / 5⌋` and `rcx := L`, `L` in `sExpLen`. -/
theorem padDiv_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hL : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) (hL' : L < 2 ^ 32) :
    WP isa (.block [.mov .rcx (.mem (hdr Crt.sExpLen)), .movImm64 .rax 0xCCCCCCCCCCCCCCCD, .mul .rcx,
      .shift .shr .rdx 2]) t fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (L / 5) ∧ t'.gpr .rcx = BitVec.ofNat 64 L ∧ t'.mem = t.mem ∧
      Keep [.rax, .rcx, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.gpr .rdx = BitVec.ofNat 64 (L / 5) ∧
      t'.gpr .rcx = BitVec.ofNat 64 L ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExpLen) (by decide), hL]
  exact div5_bv hL'

/-- `rax := padBits L` into `sBit`, from `rdx = ⌊L / 5⌋` and `rcx = L`. -/
theorem padMod_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hdx : t.gpr .rdx = BitVec.ofNat 64 (L / 5))
    (hcx : t.gpr .rcx = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .rax (.reg .rdx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rdx), .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .rcx), .mov .rax (.reg .rcx),
      .alu .sub .rax (.imm 5), .cmov .b .rax (.reg .rcx), .store (hdr Crt.sBit) .rax]) t fun t' =>
      t'.gpr .rax = BitVec.ofNat 64 (padBits L) ∧
      t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (padBits L)) ∧
      Keep [.rax, .rcx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (padBits L) ∧
      t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (padBits L))) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have h2r : (BitVec.ofNat 64 (2 * (L % 5))).toNat = 2 * (L % 5) := toNat_ofNat_of_lt (by omega_arith)
  have hpad := padBits_eq L
  by_cases h5 : 2 * (L % 5) < 5
  · rw [ite_eq_left h5] at hpad
    rw [← hpad]
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sBit) (by decide), hdx, hcx, mod5x2_bv, execCmov, eval,
      h2r, show (5 : BitVec 64).toNat = 5 from rfl, h5]
  · rw [ite_eq_right h5] at hpad
    have e : BitVec.ofNat 64 (2 * (L % 5)) - 5 = BitVec.ofNat 64 (padBits L) := by
      rw [← hpad]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, h2r, toNat_ofNat_of_lt (by omega_arith)]
      simp only [show (5 : BitVec 64).toNat = 5 from rfl]; omega_arith
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sBit) (by decide), hdx, hcx, mod5x2_bv, execCmov, eval,
      h2r, show (5 : BitVec 64).toNat = 5 from rfl, h5, e]

/-- One step of `2 ^ (56 - b)`: halve `rcx` once `b ≥ k + 1`. -/
theorem padStep_ok {s : State} {b k : Nat} (hb : b < 5) (hk : k < 4) (hax : s.gpr .rax = BitVec.ofNat 64 b)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b k))) :
    WP isa (.block [.mov .rdx (.reg .rcx), .shift .shr .rdx 1, .alu .cmp .rax (.imm (BitVec.ofNat 32 (k + 1))),
      .cmov .ae .rcx (.reg .rdx)]) s fun s' => s'.gpr .rax = BitVec.ofNat 64 b ∧
        s'.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b (k + 1))) ∧ s'.mem = s.mem ∧
        s'.gpr .rdi = s.gpr .rdi ∧ s'.wr = s.wr := by
  have e1 : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_of_lt (by omega_using [hb])
  have e2 := (by decide : ∀ k < 4, (BitVec.signExtend 64 (BitVec.ofNat 32 (k + 1))).toNat = k + 1) k hk
  by_cases h : k + 1 ≤ b
  · have v : ∀ k < 4, BitVec.ofNat 64 (2 ^ (56 - k)) >>> 1 = BitVec.ofNat 64 (2 ^ (56 - (k + 1))) := by decide
    xrun [hax, hcx, e1, e2, execCmov, eval, show ¬ b < k + 1 by omega_using [h], Nat.min_eq_right (by omega_using [h] : k ≤ b),
      Nat.min_eq_right h, v k hk]
  · xrun [hax, hcx, e1, e2, execCmov, eval, show b < k + 1 by omega_using [h], Nat.min_eq_left (by omega_using [h] : b ≤ k),
      Nat.min_eq_left (by omega_using [h] : b ≤ k + 1)]

/-- `sV := 0` and `sPow := 2^(56 - b)` for `b < 5` in `rax`: `2^56` halved
for each of 1 to 4 that is at most `b`. -/
theorem padPow_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n b : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hax : t.gpr .rax = BitVec.ofNat 64 b) (hb : b < 5) :
    WP isa (.block (([.mov32 .rcx (.imm 0), .store (hdr Crt.sV) .rcx, .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 56))] : List Instr) ++
      (List.range 4).flatMap (fun k => [.mov .rdx (.reg .rcx), .shift .shr .rdx 1,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 (k + 1))), .cmov .ae .rcx (.reg .rdx)]) ++
      ([.store (hdr Crt.sPow) .rcx] : List Instr))) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
        (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - b))) ∧ Keep [.rax, .rcx, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sV))
      (BitVec.setWidth 64 (0 : BitVec 32))).writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - b)))) ?_
      (by decide))
    fun t' ⟨h, k⟩ => ⟨h, k⟩
  have hdi := hc.good.rdi
  have hsp := hc.st (i := Crt.sPow) (by decide)
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr ?_)
  refine WP.mono (Q := fun (s₁ : State) => s₁.gpr .rax = BitVec.ofNat 64 b ∧
    s₁.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b 0)) ∧
    s₁.mem = t.mem.writeW (off P (8 * Crt.sV)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
    s₁.gpr .rdi = t.gpr .rdi ∧ s₁.wr = t.wr) ?_ fun s₁ h₁ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hc.st (i := Crt.sV) (by decide), hax, Nat.min_zero, Nat.sub_zero]
  refine WP.mono (wp_range_flatMap (fun k (s : State) => s.gpr .rax = BitVec.ofNat 64 b ∧
    s.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b k)) ∧
    s.mem = t.mem.writeW (off P (8 * Crt.sV)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
    s.gpr .rdi = t.gpr .rdi ∧ s.wr = t.wr)
    (fun k s hk h => WP.mono (padStep_ok hb hk h.1 h.2.1) fun _ h' =>
      ⟨h'.1, h'.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.trans h.2.2.2.2⟩)
    4 (Nat.le_refl _) s₁ h₁) fun s₂ ⟨_, hcx, hm, hdi₂, hwr⟩ => ?_
  rw [Nat.min_eq_left (by omega_using [hb] : b ≤ 4)] at hcx
  xrun [State.ea, hdr, hdi₂, hdi, hdrOff, hwr, hsp, hcx, hm]

theorem padInit_eq : Crt.padInit =
    ([.mov .rcx (.mem (hdr Crt.sExpLen)), .movImm64 .rax 0xCCCCCCCCCCCCCCCD, .mul .rcx, .shift .shr .rdx 2] :
      List Instr) ++
    (([.mov .rax (.reg .rdx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
      .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .rcx), .mov .rax (.reg .rcx), .alu .sub .rax (.imm 5),
      .cmov .b .rax (.reg .rcx), .store (hdr Crt.sBit) .rax] : List Instr) ++
    (([.mov32 .rcx (.imm 0), .store (hdr Crt.sV) .rcx, .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 56))] : List Instr) ++
      (List.range 4).flatMap (fun k => [.mov .rdx (.reg .rcx), .shift .shr .rdx 1,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 (k + 1))), .cmov .ae .rcx (.reg .rdx)]) ++
      ([.store (hdr Crt.sPow) .rcx] : List Instr))) := rfl

/-- `padInit`: `sBit := padBits L` for the exponent's length `L` in
`sExpLen`, `sV := 0` and `sPow := 2^(56 - padBits L)`. -/
theorem padInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hL : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) (hL' : L < 2 ^ 32) :
    WP isa (.block Crt.padInit) t fun t' =>
      t'.mem = ((t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (padBits L))).writeW (off P (8 * Crt.sV))
        (BitVec.setWidth 64 (0 : BitVec 32))).writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - padBits L))) ∧
      Keep [.rax, .rcx, .rdx] t t' := by
  rw [padInit_eq, WP.block_append_iff]
  refine WP.mono (padDiv_ok hc hL hL') fun t₁ ⟨hdx, hcx, hm₁, k₁⟩ => ?_
  have hc₁ : CExpCtx t₁ P wx minv X Xc n := hc.of_frm (by rw [hm₁]; exact Frm.refl _ _ _) k₁.2.2 (k₁.gpr (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (padMod_ok hc₁ hdx hcx) fun t₂ ⟨hax, hm₂, k₂⟩ => ?_
  have o₂ := writeW_outside t₁.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (padBits L)) (by decide)
  rw [← hm₂] at o₂
  have hc₂ : CExpCtx t₂ P wx minv X Xc n :=
    hc₁.of_frm (Frm.of_outside o₂ (by simp [crtExpRanges, crtWinRanges])) k₂.2.2 (k₂.gpr (by decide))
  refine WP.mono (padPow_ok hc₂ hax (padBits_lt L)) fun t' ⟨hm', k'⟩ => ⟨?_, ((k₁.trans k₂).trans k').mono (by decide)⟩
  rw [hm', hm₂, hm₁]

/-! ## A window's blocks -/

/-- `imul`'s result: the low word of the product. -/
theorem imul_eq (a b : BitVec 64) : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_mul]

theorem shr8_pow {b : Nat} (hb : b < 5) :
    BitVec.ofNat 64 (2 ^ (56 - b)) >>> 8 = BitVec.ofNat 64 (2 ^ (56 - (b + 8))) := by
  rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem shl5_pow {b : Nat} (hb : 5 ≤ b) (hb' : b ≤ 12) :
    BitVec.ofNat 64 (2 ^ (56 - b)) <<< 5 = BitVec.ofNat 64 (2 ^ (56 - (b - 5))) := by
  rcases (by omega_arith : b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ofNat_add8 (b : Nat) : BitVec.ofNat 64 b + 8 = BitVec.ofNat 64 (b + 8) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]

theorem ofNat_sub5 {b : Nat} (hb : 5 ≤ b) (hb' : b < 2 ^ 64) : BitVec.ofNat 64 b - 5 = BitVec.ofNat 64 (b - 5) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_of_lt hb', toNat_ofNat_of_lt (by omega_arith),
    show (5 : BitVec 64).toNat = 5 from rfl]
  omega_arith

/-- `CF := b < 5`, `b` in `sBit`. -/
theorem bitCmp_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n b : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb' : b < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .cmp .rax (.imm 5)]) t fun t' =>
      t'.cf = some (decide (b < 5)) ∧ t'.mem = t.mem ∧ Keep [.rax] t t' := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.cf = some (decide (b < 5)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sBit) (by decide), hb, toNat_ofNat_of_lt hb',
    show (5 : BitVec 64).toNat = 5 from rfl]

/-- A byte more below the `b < 5` bits at the top of `sV`: the byte `y` at
`ep + i` (`sExp`, `sI`), by a multiplication by `sPow = 2^(56 - b)`. -/
theorem refill_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) {ep : Addr} {i b r : Nat} {y : Byte}
    (he : word t.mem P (8 * Crt.sExp) = ep) (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hp : word t.mem P (8 * Crt.sPow) = BitVec.ofNat 64 (2 ^ (56 - b)))
    (hv : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (r * 2 ^ (64 - b)))
    (hbit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb : b < 5) (hr : r < 2 ^ b)
    (hrd : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1) (hy : t.mem (ep + BitVec.ofNat 64 i) = y) :
    WP isa (.block Crt.refill) t fun t' =>
      t'.mem = (((t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 ((256 * r + y.toNat) * 2 ^ (56 - b)))).writeW
        (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).writeW (off P (8 * Crt.sPow))
          (BitVec.ofNat 64 (2 ^ (56 - (b + 8))))).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 8)) ∧
      Keep [.rax, .rcx, .rdx, .r8] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r8] (Q := fun t' => t'.mem = (((t.mem.writeW (off P (8 * Crt.sV))
      (BitVec.ofNat 64 ((256 * r + y.toNat) * 2 ^ (56 - b)))).writeW (off P (8 * Crt.sI))
        (BitVec.ofNat 64 (i + 1))).writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - (b + 8))))).writeW
          (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 8))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  have hw := refill_word hb hr y.isLt
  unfold Crt.refill
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sPow) (by decide), hc.ld (i := Crt.sBit) (by decide), hc.ld (i := Crt.sV) (by decide),
    hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sI) (by decide), hc.st (i := Crt.sPow) (by decide),
    hc.st (i := Crt.sBit) (by decide), he, hi, hp, hv, hbit, byteRead, hrd, hy, execImul, imul_eq, setWidth_byte,
    Nat.pow_zero, Nat.mul_one, hw, ofNat_add_one, shr8_pow hb, ofNat_add8]

/-- The window: `sNib := ` the top 5 of the `b ≥ 5` bits at the top of `sV`,
the others moved up 5, `b - 5` left. -/
theorem takeWin_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) {b r : Nat}
    (hp : word t.mem P (8 * Crt.sPow) = BitVec.ofNat 64 (2 ^ (56 - b)))
    (hv : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (r * 2 ^ (64 - b)))
    (hbit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb : 5 ≤ b) (hb' : b ≤ 12) (hr : r < 2 ^ b) :
    WP isa (.block Crt.takeWin) t fun t' =>
      t'.mem = (((t.mem.writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - (b - 5))))).writeW
        (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 5))).writeW (off P (8 * Crt.sNib))
          (BitVec.ofNat 64 (r / 2 ^ (b - 5)))).writeW (off P (8 * Crt.sV))
            (BitVec.ofNat 64 (r % 2 ^ (b - 5) * 2 ^ (64 - (b - 5)))) ∧
      Keep [.rax, .rcx, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.mem = (((t.mem.writeW (off P (8 * Crt.sPow))
      (BitVec.ofNat 64 (2 ^ (56 - (b - 5))))).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 5))).writeW
        (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (r / 2 ^ (b - 5)))).writeW (off P (8 * Crt.sV))
          (BitVec.ofNat 64 (r % 2 ^ (b - 5) * 2 ^ (64 - (b - 5))))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  unfold Crt.takeWin
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sV) (by decide), hc.ld (i := Crt.sPow) (by decide),
    hc.ld (i := Crt.sBit) (by decide), hc.st (i := Crt.sPow) (by decide), hc.st (i := Crt.sBit) (by decide),
    hc.st (i := Crt.sNib) (by decide), hc.st (i := Crt.sV) (by decide), hp, hv, hbit, shl5_pow hb hb',
    ofNat_sub5 hb (by omega_arith), take_hi hb hb' hr, take_lo hb hb' hr]

/-- `ZF` once no byte nor bit is left: `L - i + b = 0`. -/
theorem winEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L i b : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hL : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L)
    (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) (hbit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hiL : i ≤ L) (hL' : L < 2 ^ 32) (hb : b < 2 ^ 32) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sExpLen)), .alu .sub .rax (.mem (hdr Crt.sI)),
      .alu .add .rax (.mem (hdr Crt.sBit))]) t fun t' =>
      t'.zf = some (decide (L - i + b = 0)) ∧ t'.mem = t.mem ∧ Keep [.rax] t t' := by
  have e : BitVec.ofNat 64 L - BitVec.ofNat 64 i + BitVec.ofNat 64 b = BitVec.ofNat 64 (L - i + b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega_arith), toNat_ofNat_of_lt (by omega_arith),
      toNat_ofNat_of_lt (by omega_arith), toNat_ofNat_of_lt (by omega_arith)]
    omega_arith
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (L - i + b = 0)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExpLen) (by decide), hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sBit) (by decide), hL, hi, hbit, e, ofNat64_beq_zero (show L - i + b < 2 ^ 64 by omega_arith)]

/-! ## The window's invariant -/

/-- A store to a header slot is within `expLoop5S`'s ranges if the slot is. -/
theorem frm5_hdrW (m : Mem) (P : Addr) (wx : Nat) {k : Nat} (v : BitVec 64) (hk : (8 * k, 8) ∈ crtExpRanges5 wx)
    (hk' : k < 32) : Frm P (crtExpRanges5 wx) m (m.writeW (off P (8 * k)) v) :=
  Frm.of_outside (writeW_outside m P v (by omega_arith)) hk

/-- Words past the header are kept by a store to a header slot. -/
theorem wv_hdrW (m : Mem) (P : Addr) {k d n : Nat} (v : BitVec 64) (hk : k < 32) (hd : 8 * 32 ≤ d)
    (hn : d + 8 * n ≤ 2 ^ 64) : wv (m.writeW (off P (8 * k)) v) P d n = wv m P d n :=
  (writeW_outside m P v (by omega_arith)).wv (by omega_arith) hn

/-- The table is kept by a store to a header slot but `sTab`. -/
theorem _root_.VG.Proof.Bignum.CTab.hdrW {m : Mem} {P : Addr} {wx X : Nat} {Q : Prop} {x n k : Nat} (h : CTab m P wx X Q x n)
    (v : BitVec 64) (hk : k < 32) (hkt : k ≠ Crt.sTab) (hn : slot wx 8 + tabBytes wx n ≤ 2 ^ 64) :
    CTab (m.writeW (off P (8 * k)) v) P wx X Q x n := by
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have he : ∀ j < n, wv (m.writeW (off P (8 * k)) v) P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
    fun j hj => wv_hdrW m P v hk (by have := slot_mono wx (show 8 ≤ 8 + j by omega_arith); omega_arith)
      (by have := ent_le wx hj; omega_arith)
  exact ⟨by rw [hdrStore_hdr _ _ _ hk (by decide) hkt]; exact h.tab, fun j hj => (he j hj).symm ▸ h.lt j hj,
    fun hq j hj => (he j hj).symm ▸ h.val hq j hj⟩

/-- After `i` bytes of the exponent (`L` bytes `eb` at `ep`) from `t₀`, `b`
of their bits left at the top of `sV`: `Y ≡ x^⌊P / 2^b⌋ R` for the value `P`
of the bytes read. -/
structure W5At (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (ep : Addr) (L : Nat) (eb : List Byte) (i b : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc 32
  tab : CTab t.mem P wx X Q x 32
  ylt : wv t.mem P (slot wx aY) wx < X
  y : Q → wv t.mem P (slot wx aY) wx % X = x ^ (pre eb i / 2 ^ b) * 2 ^ (64 * wx) % X
  v : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (pre eb i % 2 ^ b * 2 ^ (64 - b))
  bit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b
  pow : word t.mem P (8 * Crt.sPow) = BitVec.ofNat 64 (2 ^ (56 - b))
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : word t.mem P (8 * Crt.sExp) = ep
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (crtExpRanges5 wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem W5At.of_mem {t₀ t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i b : Nat} (h : W5At t₀ P wx minv X Xc Q x ep L eb i b t)
    (hm : t'.mem = t.mem) {rs : List Reg} (k : Keep rs t t') (hrs : ∀ r ∈ rs, r ∈ mmRegs)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : W5At t₀ P wx minv X Xc Q x ep L eb i b t' :=
  ⟨h.ctx.of_frm5 (by rw [hm]; exact Frm.refl _ _ _) k.2.2 hdi, hm ▸ h.tab, hm ▸ h.ylt,
    hm ▸ h.y, hm ▸ h.v, hm ▸ h.bit, hm ▸ h.pow, hm ▸ h.idx, hm ▸ h.e, hm ▸ h.len, hm ▸ h.frm,
    (h.keep.trans k).mono fun r hr => by
      rcases List.mem_append.mp hr with h' | h'
      · exact h'
      · exact hrs r h'⟩

/-- A byte more if fewer than 5 bits are left: then `b ≥ 5`. -/
theorem fill_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i b : Nat} (hL : eb.length = L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx 32 ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hb : b < 8) (hiL : i ≤ L) (hfill : b < 5 → i < L) (hI : W5At t₀ P wx minv X Xc Q x ep L eb i b t) :
    WP isa (seqs [.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .cmp .rax (.imm 5)],
        .ite .b (.block Crt.refill) (.block [])]) t fun t' =>
      ∃ i' b', 5 ≤ b' ∧ b' ≤ 12 ∧ 8 * i' + b = 8 * i + b' ∧ i' ≤ L ∧ W5At t₀ P wx minv X Xc Q x ep L eb i' b' t' := by
  have hn := hI.ctx.scrT.nowrap
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (bitCmp_ok hI.ctx hI.bit (by omega_arith)) fun t₁ ⟨hcf, hm₁, k₁⟩ => ?_)
  have hI₁ := hI.of_mem hm₁ k₁ (by decide) (k₁.gpr (by decide))
  refine WP.ite (decide (b < 5)) (by simp only [eval, hcf]) (fun h5 => ?_) (fun h5 => ?_)
  · have h5' : b < 5 := of_decide_eq_true h5
    have hi : i < L := hfill h5'
    have hrdi : InRegions (t₁.rd ++ t₁.wr) (ep + BitVec.ofNat 64 i) 1 := by
      rw [hI₁.keep.2.1, hI₁.keep.2.2]; exact hrd i hi
    have hbi : t₁.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith) := by
      rw [hI₁.frm _ fun r hr => Or.inr (by have := (crtExpRanges5_ok wx r hr).2; have := hout i hi; omega_arith)]
      exact hbytes i hi
    have hr : pre eb i % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
    refine WP.mono (refill_ok hI₁.ctx hI₁.e hI₁.idx hI₁.pow hI₁.v hI₁.bit h5' hr hrdi hbi) fun t₂ ⟨hm₂, k₂⟩ =>
      ⟨i + 1, b + 8, by omega_arith, by omega_arith, by omega_arith, by omega_arith, ?_⟩
    have hv := (refill_val (P := pre eb i) (b := b) (eb[i]'(by omega_arith)).isLt)
    rw [← pre_succ eb (by omega_arith)] at hv
    have hm : t₂.mem = (((t₁.mem.writeW (off P (8 * Crt.sV))
        (BitVec.ofNat 64 ((256 * (pre eb i % 2 ^ b) + (eb[i]'(by omega_arith)).toNat) * 2 ^ (56 - b)))).writeW
          (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).writeW (off P (8 * Crt.sPow))
            (BitVec.ofNat 64 (2 ^ (56 - (b + 8))))).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 8)) := hm₂
    have f₂ : Frm P (crtExpRanges5 wx) t₁.mem t₂.mem := by
      rw [hm]
      exact (((frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide)).trans
        (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges]) (by decide))).trans
        (frm5_hdrW _ P wx _ (by simp [crtExpRanges5]) (by decide))).trans
        (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))
    have hY : wv t₂.mem P (slot wx aY) wx = wv t₁.mem P (slot wx aY) wx := by
      rw [hm, wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith),
        wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith)]
    have hnT : slot wx 8 + tabBytes wx 32 ≤ 2 ^ 64 := by omega_arith
    refine ⟨hI₁.ctx.of_frm5 f₂ k₂.2.2 (k₂.gpr (by decide)), ?_, hY ▸ hI₁.ylt, fun hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hI₁.frm.trans f₂, (hI₁.keep.trans k₂).mono (by decide)⟩
    · rw [hm]
      exact (((hI₁.tab.hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide)
        (by decide) hnT).hdrW _ (by decide) (by decide) hnT
    · rw [hY, hI₁.y hq, hv.2]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self, hv.1, show 64 - (b + 8) = 56 - b by omega_arith]
    · rw [hm, word_writeW_self]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hI₁.e
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hI₁.len
  · have h5' : ¬ b < 5 := fun h => absurd (decide_eq_true h) (by rw [h5]; decide)
    exact WP.block_nil ⟨i, b, by omega_arith, by omega_arith, by omega_arith, hiL, hI₁⟩

/-! ## A window -/

theorem expWin5_eq (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) :
    Crt.expWin5 sq mul sel =
    ([.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .cmp .rax (.imm 5)], .ite .b (.block Crt.refill) (.block [])] : List (Prog isa)) ++
    ([sq, sq, sq, sq, sq, .block Crt.takeWin] ++
      (sel ++ [mul aY aY Crt.aT, .block [.mov .rax (.mem (hdr Crt.sExpLen)), .alu .sub .rax (.mem (hdr Crt.sI)),
        .alu .add .rax (.mem (hdr Crt.sBit))]])) := rfl

/-- A header slot but `sEnt` and `sJ` is kept by a change within `selRanges`. -/
theorem sel_hdr {m m' : Mem} {P : Addr} {wx : Nat} (f : Frm P (selRanges wx) m m') {k : Nat} (hk : k < 32)
    (h1 : k ≠ Crt.sEnt) (h2 : k ≠ Crt.sJ) : word m' P (8 * k) = word m P (8 * k) :=
  f.word_eq (fun r hr => by
    have := hdr_lt_slot wx Crt.aT hk
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only; omega_arith
    · simp only [Crt.sEnt, sFn] at h1 ⊢; omega_arith
    · simp only [Crt.sJ, sFn] at h2 ⊢; omega_arith) (by omega_arith)

/-- The last window: no byte nor bit left after it. -/
theorem win5_last {K p L i j b i' b' : Nat} (hK : 5 * K = p + 8 * L) (hib : p + 8 * i = 5 * j + b)
    (hrel : 8 * i' + b = 8 * i + b') (hiL : i' ≤ L) (hb5 : 5 ≤ b') (hb12 : b' ≤ 12) :
    L - i' + (b' - 5) = 0 ↔ j + 1 = K := by
  have e : 5 * K + 5 = 5 * (j + 1) + 8 * (L - i') + b' := by omega_using [hK, hib, hrel, hiL]
  constructor
  · intro h
    rw [Nat.add_eq_zero_iff, Nat.sub_eq_zero_iff_le, Nat.sub_eq_zero_iff_le] at h
    rw [Nat.sub_eq_zero_of_le h.1, Nat.le_antisymm h.2 hb5] at e
    omega_using [e]
  · intro h
    subst h
    have e1 : L - i' = 0 := by omega_using [e, hb5, hb12]
    rw [e1]; omega_using [e]

/-- Window `j` of `K`: a byte more if fewer than 5 bits are left, then
`Y := Y³² T_v R⁻¹` for `v` the top 5 of the `b'` bits left;
`ZF` after the last. -/
theorem crtWin5_ok (M : Mont) (Sq : MontS) (S : CrtSel 32) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    {Q : Prop} {x : Nat} {ep : Addr} {L : Nat} {eb : List Byte} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hL : eb.length = L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx 32 ≤ ofs P (ep + BitVec.ofNat 64 i))
    {K j : Nat} (hK : 5 * K = padBits L + 8 * L) (hj : j < K) {i b : Nat} (hib : padBits L + 8 * i = 5 * j + b)
    (hb : b < 8) (hiL : i ≤ L) (hI : W5At t₀ P wx minv X Xc Q x ep L eb i b t) :
    WP isa (seqs (Crt.expWin5 Sq.mm M.mm S.code)) t fun t' => t'.zf = some (decide (j + 1 = K)) ∧
      ∃ i' b', padBits L + 8 * i' = 5 * (j + 1) + b' ∧ b' < 8 ∧ i' ≤ L ∧
        W5At t₀ P wx minv X Xc Q x ep L eb i' b' t' := by
  rw [expWin5_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (fill_ok hL hrd hbytes hout hb hiL (fun h5 => by
    rcases Nat.lt_or_ge i L with h | h
    · exact h
    · omega_arith) hI) fun t₁ ⟨i', b', hb5, hb12, hrel, hiL', hI₁⟩ => ?_
  have hc := hI₁.ctx
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  -- Five squarings, whose results stay below `Sq.bd X R`.
  have hXR : X ≤ 2 ^ (64 * wx) := by rw [← hc.n]; exact Nat.le_of_lt (wv_lt _ _ _ _)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc hw hw' hR (Nat.lt_of_lt_of_le hI₁.ylt (Sq.le hXR)) hI₁.y)
    fun t₂ ⟨hc₂, hY₂, hYv₂, hh₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₂ hw hw' hR hY₂ hYv₂) fun t₃ ⟨hc₃, hY₃, hYv₃, hh₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₃ hw hw' hR hY₃ hYv₃) fun t₄ ⟨hc₄, hY₄, hYv₄, hh₄, f₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₄ hw hw' hR hY₄ hYv₄) fun t₅ ⟨hc₅, hY₅, hYv₅, hh₅, f₅, k₅⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₅ hw hw' hR hY₅ hYv₅) fun t₆ ⟨hc₆, _, hYv₆, hh₆, f₆, k₆⟩ => ?_)
  have hh16 : ∀ k < 32, word t₆.mem P (8 * k) = word t₁.mem P (8 * k) := fun k hk =>
    (hh₆ k hk).trans ((hh₅ k hk).trans ((hh₄ k hk).trans ((hh₃ k hk).trans (hh₂ k hk))))
  have f16 : Frm P (crtWinRanges wx) t₁.mem t₆.mem := (((f₂.trans f₃).trans f₄).trans f₅).trans f₆
  have k16 : Keep mmRegs t₁ t₆ := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  have htab₆ : CTab t₆.mem P wx X Q x 32 := hI₁.tab.of_win f16 hn
  -- The window.
  have hr : pre eb i' % 2 ^ b' < 2 ^ b' := Nat.mod_lt _ (Nat.two_pow_pos b')
  refine wp_seqs_append (a := [.block Crt.takeWin]) (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (takeWin_ok hc₆ (by rw [hh16 _ (by decide)]; exact hI₁.pow)
    (by rw [hh16 _ (by decide)]; exact hI₁.v) (by rw [hh16 _ (by decide)]; exact hI₁.bit) hb5 hb12 hr)
    fun t₇ ⟨hm₇, k₇⟩ => ?_
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hnT : slot wx 8 + tabBytes wx 32 ≤ 2 ^ 64 := by omega_arith
  have f₇ : Frm P (crtExpRanges5 wx) t₆.mem t₇.mem := by
    rw [hm₇]
    exact (((frm5_hdrW _ P wx _ (by simp [crtExpRanges5]) (by decide)).trans
      (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))
  have hc₇ := hc₆.of_frm5 f₇ k₇.2.2 (k₇.gpr (by decide))
  have htab₇ : CTab t₇.mem P wx X Q x 32 := by
    rw [hm₇]
    exact (((htab₆.hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide)
      (by decide) hnT).hdrW _ (by decide) (by decide) hnT
  have hY₇ : wv t₇.mem P (slot wx aY) wx = wv t₆.mem P (slot wx aY) wx := by
    rw [hm₇, wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith)
      (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith),
      wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith)]
  have hh₇ : ∀ k < 32, k ≠ Crt.sPow → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sV →
      word t₇.mem P (8 * k) = word t₁.mem P (8 * k) := fun k hk h1 h2 h3 h4 => by
    rw [hm₇, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h4), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h3),
      hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1), hh16 k hk]
  have hv32 : pre eb i' % 2 ^ b' / 2 ^ (b' - 5) < 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add,
      show 5 + (b' - 5) = b' by omega_arith]
    exact hr
  -- `T := T_v`.
  refine wp_seqs_append S.ne (by simp) ?_
  have ht₇ : word t₇.mem P (8 * Crt.sTab) = off P (slot wx 8) := by
    rw [hh₇ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI₁.tab.tab
  refine WP.mono (S.ok hc₇ hw hw' hv32 ht₇
      (by rw [hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]))
    fun t₈ ⟨hc₈, hT₈, f₈, k₈⟩ => ?_
  have hY₈ : wv t₈.mem P (slot wx aY) wx = wv t₇.mem P (slot wx aY) wx :=
    f₈.wv_eq (fun r hr => by
      have := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith) (by omega_arith)
  have htab₈ : CTab t₈.mem P wx X Q x 32 := htab₇.of_win (f₈.mono (selRanges_sub wx)) hn
  simp only [seqs]
  -- `Y := Y T`.
  have hv := take_val (P := pre eb i') hb5
  refine WP.seq (WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := 32 * (pre eb i' / 2 ^ b'))
    (v := pre eb i' % 2 ^ b' / 2 ^ (b' - 5)) hc₈ hw hw' hR (by rw [hT₈]; exact htab₇.lt _ hv32)
    (fun hq => by rw [hY₈, hY₇, hYv₆ hq, show ∀ C : Nat, 2 * (2 * (2 * (2 * (2 * C)))) = 32 * C from fun C => by omega_arith])
    (fun hq => by rw [hT₈]; exact htab₇.val hq _ hv32)) fun t₉ ⟨hc₉, hY₉, hYv₉, hh₉, f₉, k₉⟩ => ?_)
  have hh₉' : ∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → word t₉.mem P (8 * k) = word t₇.mem P (8 * k) :=
    fun k hk h1 h2 => (hh₉ k hk).trans (sel_hdr f₈ hk h1 h2)
  -- The end.
  refine WP.mono (winEnd_ok (L := L) (i := i') (b := b' - 5) hc₉
    (by rw [hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.len)
    (by rw [hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.idx)
    (by rw [hh₉' _ (by decide) (by decide) (by decide), hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self])
    hiL' (by omega_arith) (by omega_arith)) fun t' ⟨hz, hm', k'⟩ => ⟨by rw [hz]; congr 1; exact decide_eq_decide.mpr (win5_last hK hib hrel hiL' hb5 hb12),
      i', b' - 5, by omega_arith, by omega_arith, hiL', ?_⟩
  have fall : Frm P (crtExpRanges5 wx) t₁.mem t'.mem := by
    rw [hm']
    exact ((f16.mono fun r hr => crtExpRanges_sub5 wx r (crtWinRanges_sub wx r hr)).trans f₇).trans
      ((f₈.mono fun r hr => crtExpRanges_sub5 wx r (crtWinRanges_sub wx r (selRanges_sub wx r hr))).trans
        (f₉.mono fun r hr => crtExpRanges_sub5 wx r (crtWinRanges_sub wx r hr)))
  have htab' : CTab t'.mem P wx X Q x 32 := by rw [hm']; exact htab₈.of_win f₉ hn
  have hY' : wv t'.mem P (slot wx aY) wx < X := by rw [hm']; exact hY₉
  refine ⟨hc₉.of_frm5 (by rw [hm']; exact Frm.refl _ _ _) k'.2.2 (k'.gpr (by decide)), htab', hY', fun hq => ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, hI₁.frm.trans fall,
    ((((((hI₁.keep.trans k16).trans k₇).trans k₈).trans k₉).trans k').mono (by decide))⟩
  · rw [hm', hYv₉ hq, hv.1]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hm₇, word_writeW_self, hv.2]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.idx
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.e
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.len

/-! ## The exponentiation -/

/-- What changes within `expLoop5S`'s ranges keeps the prime's workspace. -/
theorem SubCtx.of_frm5 {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hf : Frm (off B o) (crtExpRanges5 wx) s.mem t.mem)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx minv := by
  have hn := h.scr.nowrap
  simp only [wsTab] at hT
  have hL : o + (slot wx 8 + tabBytes wx 32) ≤ 2 ^ 64 := by omega_arith
  have hr := crtExpRanges5_ok wx
  have hr' : ∀ r ∈ crtExpRanges5 wx, r.1 + r.2 ≤ slot wx 8 + tabBytes wx 32 := fun r hr' => (hr r hr').2
  have hh : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith))
      (by have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
          omega_arith)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold slot hdrBytes at hL; omega_arith) (by have := hdr_lt_slot w 8 hi'; have := h.lo; omega_arith)
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_arith)).trans (h.narr j hj), h.lo, h.hi⟩

/-- After `j` windows: `padBits L + 8 i = 5 j + b`. -/
def W5Inv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (ep : Addr) (L : Nat) (eb : List Byte) (j : Nat) (t : State) : Prop :=
  ∃ i b, padBits L + 8 * i = 5 * j + b ∧ b < 8 ∧ i ≤ L ∧ W5At t₀ P wx minv X Xc Q x ep L eb i b t

theorem expLoop5_eq (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) (sp sl : Nat) :
    Crt.expLoop5S sq mul sel sp sl = ((expInit sp sl :: Crt.tabBuildN mul 30) ++
      ([.block Crt.padInit] : List (Prog isa))) ++ ([.loop (seqs (Crt.expWin5 sq mul sel)) .ne] : List (Prog isa)) := by
  simp [Crt.expLoop5S, expInit]

/-- `expLoop5S`'s start, table and padding: the windows' invariant. -/
theorem crtExpHead5_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    {X x : Nat} {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hw2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL2 : eb.length ≤ 1024) :
    WP isa (seqs ((expInit sp sl :: Crt.tabBuildN M.mm 30) ++ ([.block Crt.padInit] : List (Prog isa)))) s
      (W5Inv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb 0) := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hs32 := hc.scr32 hT
  have hPn := hs32.nowrap
  have hT' := hT
  simp only [wsTab] at hT'
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc₀ : CExpCtx s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) 32 :=
    ⟨hc.good, hs32, hn, hinv, rfl⟩
  refine wp_seqs_append (by simp) (by simp) ?_
  -- The start and the table.
  rw [← List.singleton_append]
  refine wp_seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) ?_
  simp only [seqs, expInit]
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep) (off B o) (d := 8 * Crt.sExpLen)
    (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
    (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off B o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off B o) (crtExpRanges wx 32) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  have hc₁ := hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide))
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have hYe₁ : wv t₁.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith), o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith)
      (by omega_arith), o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  refine WP.mono (tabBuild_ok M (Q := Q) (x := x) hc₁ (by decide) (by decide) hw2 (by omega_arith) hR hxl hxc
    (by rw [hYe₁]; exact hyl) (fun hq => by rw [hYe₁]; exact hyc hq)) fun t₂ ⟨hc₂, htab₂, hYe₂, hh₂, f₂, k₂⟩ => ?_
  -- The padding.
  have hlen₂ : word t₂.mem (off B o) (8 * Crt.sExpLen) = BitVec.ofNat 64 eb.length := by
    rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  refine WP.mono (padInit_ok hc₂ hlen₂ (by omega_arith)) fun t₃ ⟨hm₃, k₃⟩ => ?_
  have hnT : slot wx 8 + tabBytes wx 32 ≤ 2 ^ 64 := by omega_arith
  have f₃ : Frm (off B o) (crtExpRanges5 wx) t₂.mem t₃.mem := by
    rw [hm₃]
    exact ((frm5_hdrW _ _ wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide)).trans
      (frm5_hdrW _ _ wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ _ wx _ (by simp [crtExpRanges5]) (by decide))
  have f03 : Frm (off B o) (crtExpRanges5 wx) s.mem t₃.mem :=
    ((f₁.mono (crtExpRanges_sub5 wx)).trans (f₂.mono (crtExpRanges_sub5 wx))).trans f₃
  have hh₃ : ∀ k < 32, k ≠ Crt.sBit → k ≠ Crt.sV → k ≠ Crt.sPow → word t₃.mem (off B o) (8 * k) =
      word t₂.mem (off B o) (8 * k) := fun k hk h1 h2 h3 => by
    rw [hm₃, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h3), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1)]
  have hY₃ : wv t₃.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [hm₃, wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith)
      (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), hYe₂, hYe₁]
  have h0 : W5Inv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb 0 t₃ := by
    refine ⟨0, padBits eb.length, by omega_arith, by have := padBits_lt eb.length; omega_arith, by omega_arith,
      hc₂.of_frm5 f₃ k₃.2.2 (k₃.gpr (by decide)), ?_, hY₃ ▸ hyl, fun hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, f03,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [hm₃]
      exact ((htab₂.hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide)
        (by decide) hnT
    · rw [hY₃, hyc hq, pre_zero, Nat.zero_div, Nat.pow_zero, Nat.one_mul]
    · rw [hm₃, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, pre_zero, Nat.zero_mod,
        Nat.zero_mul]; rfl
    · rw [hm₃, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₃, word_writeW_self]
    · rw [hh₃ _ (by decide) (by decide) (by decide) (by decide), hh₂ _ (by decide) (by decide) (by decide) (by decide),
        hm₁, word_writeW_self]; rfl
    · rw [hh₃ _ (by decide) (by decide) (by decide) (by decide), hh₂ _ (by decide) (by decide) (by decide) (by decide),
        hm₁, hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hh₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hlen₂
  exact h0

/-- The exponentiation in a prime's workspace by windows of 5 bits, with room
for its table of 32 entries: as `crtExpLoop_ok`. -/
theorem crtExpLoop5S_ok (M : Mont) (Sq : MontS) (S : CrtSel 32) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    {X x : Nat} {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hw2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop5S Sq.mm M.mm S.code sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges5 wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hs32 := hc.scr32 hT
  have hPn := hs32.nowrap
  have hT' := hT
  simp only [wsTab] at hT'
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 + tabBytes wx 32 ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  rw [expLoop5_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (crtExpHead5_ok M hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl
    hyc hsp hsl hep hel hL2) fun t₃ h0 => ?_)
  simp only [seqs]
  -- The windows.
  have hK := win5_dvd eb.length
  refine wp_upto (a := 0) (N := (padBits eb.length + 8 * eb.length) / 5) (by omega_arith)
    (W5Inv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb)
    (fun j _ hj t ⟨i, b, hib, hb, hiL, hI⟩ => crtWin5_ok M Sq S hw2 (by omega_arith) hR rfl (by omega_arith) he.rd he.val
      hout (by omega_arith) hj hib hb hiL hI)
    (fun t ⟨i, b, hib, hb, hiL, hI⟩ => ?_) h0
  have hb0 : b = 0 := by omega_arith
  have hiL' : i = eb.length := by omega_arith
  subst hb0 hiL'
  exact ⟨hc.of_frm5 hT hI.frm hI.keep.2.2 (hI.keep.gpr (by decide)), hI.ylt,
    fun hq => by rw [hI.y hq, Nat.pow_zero, Nat.div_one, pre_len], hI.frm, hI.keep⟩

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.CrtSelVExp`, which only this module used -/

section

/-! ### `Bignum.X86_64.CrtSelV`, which only this module used -/

section

/-!
# RSA with the CRT on x86-64: gathering a table entry with AVX2

`Crt.gatherPassV` (`Impl/Rsa/X86_64/Crt.lean`) is `Crt.gatherPass` with the
masks broadcast to whole `ymm` registers: each step replaces the words of
`[rbx]` at `r14`, four (`.l256`, two lanes) or two (`.l128`, one), by
`OR_j (mask_j & T_j) | (keep & [rbx])` (`gChunkV_ok`), the words read a
lane at a time (`q128` of `lane`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The lanes of a VEX length. -/
def nl : VLen → Nat
  | .l128 => 1
  | .l256 => 2

/-- Quadword `q` of lane `l` of a 256-bit read. -/
theorem q_read256 (m : Mem) (a : Addr) {l q : Nat} (hl : l < 2) (hq : q < 2) :
    q128 (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) q =
      m.readW (a + BitVec.ofNat 64 (16 * l + 8 * q)) 64 := by
  have e : (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) =
      (m.readW a 256).extractLsb' (128 * l) 128 := by
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  rw [e, q128, qword, extract_extract _ _ _ _ _ (by omega_arith), show 128 * l + 64 * q = 8 * (16 * l + 8 * q) by omega_arith]
  exact readW_extract m a (k := 16 * l + 8 * q) (n := 8) (by omega_arith)

/-- Quadword `q` of a 128-bit read. -/
theorem q_read128 (m : Mem) (a : Addr) {q : Nat} (hq : q < 2) :
    q128 (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 (8 * q)) 64 := by
  rw [q128, qword, show 64 * q = 8 * (8 * q) by omega_arith]
  exact readW_extract m a (k := 8 * q) (n := 8) (by omega_arith)

/-- A 256-bit write of a register, read back a quadword at a time. -/
theorem read_write256 (m : Mem) (a : Addr) (hi lo : BitVec 128) {l q : Nat} (hl : l < 2) (hq : q < 2) :
    (m.writeW a (hi ++ lo)).readW (a + BitVec.ofNat 64 (16 * l + 8 * q)) 64 = q128 (if l = 0 then lo else hi) q := by
  have e := readW_writeW_inside m a (hi ++ lo) (k := 16 * l + 8 * q) (n := 8) (by omega_arith) (by decide)
  rw [show 8 * 8 = 64 by rfl] at e
  rw [e]
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [q128, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi', Bool.true_and]
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [show 8 * (16 * 0 + 8 * q) + i < 128 by omega_arith, ↓reduceIte]
    exact congrArg _ (by omega_arith)
  · simp only [show ¬ 8 * (16 * 1 + 8 * q) + i < 128 by omega_arith, Nat.one_ne_zero, ↓reduceIte]
    exact congrArg _ (by omega_arith)

/-- A 128-bit write, read back a quadword at a time. -/
theorem read_write128' (m : Mem) (a : Addr) (v : BitVec 128) {q : Nat} (hq : q < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * q)) 64 = q128 v q := by
  have e := readW_writeW_inside m a v (k := 8 * q) (n := 8) (by omega_arith) (by decide)
  rw [show 8 * (8 * q) = 64 * q by omega_arith, show 8 * 8 = 64 by rfl] at e
  exact e

/-- `n` bytes of the working space are readable and writable. -/
theorem inRegionsN {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) {d n : Nat} (hd : d + n ≤ Z) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (off B d) n ∧ InRegions s.wr (off B d) n := by
  obtain ⟨r, hr, hc⟩ := hs.region hd hn
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r, hr, hc⟩⟩

/-- What a step leaves of the vector registers but `xmm0` and `xmm1`. -/
def VKeep01 (s t : State) : Prop := ∀ y, y ≠ .xmm0 → y ≠ .xmm1 → ∀ l, t.lane y l = s.lane y l

/-! ## A step -/

/-- `xmm0 |= x & [b + 8 r14]`, lane by lane. -/
theorem gOrV_ok (L : VLen) {s : State} {B : Addr} {Z e c : Nat} (hs : Scr s B Z) {b : Reg} {x : XReg}
    (hb : s.gpr b = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 c)
    (he : e + 8 * c + 16 * nl L ≤ Z) :
    WP isa (.block (Crt.gatherOrV L b x)) s fun t =>
      (∀ l < nl L, ∀ q < 2, q128 (t.lane .xmm0 l) q =
        q128 (s.lane .xmm0 l) q ||| (q128 (s.lane x l) q &&& word s.mem B (e + 8 * c + 16 * l + 8 * q))) ∧
      VKeep01 s t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  have eA : s.ea (ix b .r14) = off B (e + 8 * c) := ea_ix0 s hb h14
  cases L with
  | l256 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 32) (by simp only [nl] at he; omega_arith) (by decide)
    apply WP.of_runBlock
    simp only [Crt.gatherOrV, runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load256, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 h1 l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      simp only [lane_vbin256, State.lane_setV256, ↓reduceIte, show XReg.xmm0 ≠ XReg.xmm1 by decide,
        reduceVBinOpSse, XBinOp.eval]
      rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
      · simp only [↓reduceIte]
        rw [q128_or, q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 =
          (if (0 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
      · simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [q128_or, q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128 =
          (if (1 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
    · simp only [lane_vbin256, State.lane_setV256, h0, h1, ↓reduceIte]
  | l128 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 16) (by simp only [nl] at he; omega_arith) (by decide)
    apply WP.of_runBlock
    simp only [Crt.gatherOrV, runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load128, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 h1 l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      obtain rfl : l = 0 := by omega_arith
      simp only [lane_vbin128, State.lane_setV128, ↓reduceIte, show XReg.xmm0 ≠ XReg.xmm1 by decide,
        reduceVBinOpSse, XBinOp.eval]
      rw [q128_or, q128_and, q_read128 _ _ hq, off_add_eq]
      simp only [Nat.mul_zero, Nat.add_zero]
    · simp only [lane_vbin128, State.lane_setV128, h0, h1, ↓reduceIte]

/-- A write of `w` bits changes only those bytes. -/
theorem writeW_outsideV (m : Mem) (base : Addr) {d w : Nat} (v : BitVec w) (h : d + w / 8 ≤ 2 ^ 64)
    (hw : 0 < w / 8) :
    Outside base d (w / 8) m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega_arith)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

/-- `xmm0 := xmm8 & [rcx + 8 r14]`, lane by lane. -/
theorem gFirstV_ok (L : VLen) {s : State} {B : Addr} {Z e c : Nat} (hs : Scr s B Z)
    (hb : s.gpr .rcx = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (he : e + 8 * c + 16 * nl L ≤ Z) :
    WP isa (.block [.vbinLoad .vpand L .xmm0 .xmm8 (ix .rcx .r14)]) s fun t =>
      (∀ l < nl L, ∀ q < 2, q128 (t.lane .xmm0 l) q = q128 (s.lane .xmm8 l) q &&& word s.mem B (e + 8 * c + 16 * l + 8 * q)) ∧
      VKeep01 s t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  have eA : s.ea (ix .rcx .r14) = off B (e + 8 * c) := ea_ix0 s hb h14
  cases L with
  | l256 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 32) (by simp only [nl] at he; omega_arith) (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load256, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 _ l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      simp only [State.lane_setV256, ↓reduceIte, reduceVBinOpSse, XBinOp.eval]
      rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
      · simp only [↓reduceIte]
        rw [q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 =
          (if (0 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
      · simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [q128_and, show (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128 =
          (if (1 : Nat) = 0 then (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 0 128 else
            (s.mem.readW (off B (e + 8 * c)) 256).extractLsb' 128 128) from rfl, q_read256 _ _ (by decide) hq,
          off_add_eq, ← Nat.add_assoc]
    · simp only [State.lane_setV256, h0, ↓reduceIte]
  | l128 =>
    obtain ⟨iA, -⟩ := inRegionsN hs (d := e + 8 * c) (n := 16) (by simp only [nl] at he; omega_arith) (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, eA, State.load128, iA, ite_true,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl q hq => ?_, fun y h0 _ l => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [nl] at hl
      obtain rfl : l = 0 := by omega_arith
      simp only [State.lane_setV128, ↓reduceIte, reduceVBinOpSse, XBinOp.eval]
      rw [q128_and, q_read128 _ _ hq, off_add_eq]
      simp only [Nat.mul_zero, Nat.add_zero]
    · simp only [State.lane_setV128, h0, ↓reduceIte]

/-- The store of `xmm0` at `[rbx + 8 r14]`, and `r14 += n`. -/
theorem gStoreV_ok (L : VLen) {s : State} {B : Addr} {Z e c n : Nat} (hs : Scr s B Z)
    (hb : s.gpr .rbx = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (he : e + 8 * c + 16 * nl L ≤ Z)
    (hn : n = 2 ∨ n = 4) :
    WP isa (.block [.vmovdquStore L (ix .rbx .r14) .xmm0, .alu .add .r14 (.imm (BitVec.ofNat 32 n))]) s fun t =>
      (∀ l < nl L, ∀ q < 2, word t.mem B (e + 8 * c + 16 * l + 8 * q) = q128 (s.lane .xmm0 l) q) ∧
      Outside B (e + 8 * c) (16 * nl L) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .r14 → t.gpr r = s.gpr r) ∧ (∀ y l, t.lane y l = s.lane y l) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hnw := hs.nowrap
  have eO : s.ea (ix .rbx .r14) = off B (e + 8 * c) := ea_ix0 s hb h14
  have himm : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
    rcases hn with rfl | rfl <;> decide
  have hadd : ∀ t : State, t.gpr .r14 = BitVec.ofNat 64 c →
      WP isa (.block [.alu .add .r14 (.imm (BitVec.ofNat 32 n))]) t fun t' =>
        t'.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r14 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem ∧ (∀ y l, t'.lane y l = t.lane y l) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := fun t h => by
    refine WP.mono (WP.keep [.r14] (Q := fun t' => t'.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧
      t'.mem = t.mem ∧ ∀ y l, t'.lane y l = t.lane y l) (by xrun [h, himm]; exact fun _ _ => rfl) rfl)
      fun t' ⟨⟨h1, h2, h3⟩, k⟩ =>
      ⟨h1, fun r hr => k.1 r (by simpa using hr), h2, h3, k.2.1, k.2.2⟩
  cases L with
  | l256 =>
    obtain ⟨-, sO⟩ := inRegionsN hs (d := e + 8 * c) (n := 32) (by simp only [nl] at he; omega_arith) (by decide)
    rw [WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B (e + 8 * c)) (s.ymm .xmm0) },
      by simp only [exec, eO, State.store256, sO, ite_true], ?_⟩
    refine WP.mono (hadd _ h14) fun t ⟨h1, h2, hm, hl, hrd, hwr⟩ => ⟨fun l hl' q hq => ?_, ?_, h1, h2, hl, hrd, hwr⟩
    · simp only [nl] at hl'
      rw [hm]
      show (s.mem.writeW (off B (e + 8 * c)) (s.ymm .xmm0)).readW (off B (e + 8 * c + 16 * l + 8 * q)) 64 = _
      rw [Nat.add_assoc (e + 8 * c), show off B (e + 8 * c + (16 * l + 8 * q)) =
        off B (e + 8 * c) + BitVec.ofNat 64 (16 * l + 8 * q) from (off_add_eq _ _ _).symm, State.ymm_eq,
        read_write256 _ _ _ _ hl' hq]
      rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
    · rw [hm]; exact writeW_outsideV s.mem B (d := e + 8 * c) (s.ymm .xmm0) (by simp only [nl] at he; omega_arith) (by decide)
  | l128 =>
    obtain ⟨-, sO⟩ := inRegionsN hs (d := e + 8 * c) (n := 16) (by simp only [nl] at he; omega_arith) (by decide)
    rw [WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B (e + 8 * c)) (s.xmm .xmm0) },
      by simp only [exec, eO, State.store128, sO, ite_true], ?_⟩
    refine WP.mono (hadd _ h14) fun t ⟨h1, h2, hm, hl, hrd, hwr⟩ => ⟨fun l hl' q hq => ?_, ?_, h1, h2, hl, hrd, hwr⟩
    · simp only [nl] at hl'
      obtain rfl : l = 0 := by omega_arith
      rw [hm]
      show (s.mem.writeW (off B (e + 8 * c)) (s.xmm .xmm0)).readW (off B (e + 8 * c + 16 * 0 + 8 * q)) 64 = _
      rw [Nat.mul_zero, Nat.add_zero, show off B (e + 8 * c + 8 * q) = off B (e + 8 * c) + BitVec.ofNat 64 (8 * q)
        from (off_add_eq _ _ _).symm, read_write128' _ _ _ hq]
      rfl
    · rw [hm]; exact writeW_outsideV s.mem B (d := e + 8 * c) (s.xmm .xmm0) (by simp only [nl] at he; omega_arith) (by decide)

/-! ## A chunk of words -/

/-- The registers of pass `p` of the selection with AVX2: as `GRegs`, the
masks in every lane, the keep mask that of `p ≠ 0`, and `r12` the words
below which the chunks have four. -/
structure GRegsV (B : Addr) (wx p v : Nat) (s : State) : Prop where
  base : ∀ k < 8, s.gpr (gReg k) = off B (slot wx (8 + 8 * p + k))
  bx : s.gpr .rbx = off B (slot wx Crt.aT)
  r13 : s.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2))
  r12 : s.gpr .r12 = BitVec.ofNat 64 (4 * ((wx + 1) / 2 / 2))
  msk : ∀ k < 8, ∀ l < 2, ∀ q < 2, q128 (s.lane (gX k) l) q = mask (decide (8 * p + k = v))
  keep : ∀ l < 2, ∀ q < 2, q128 (s.lane .xmm7 l) q = mask (decide (p ≠ 0))

theorem GRegsV.congr {B : Addr} {wx p v : Nat} {s t : State} (h : GRegsV B wx p v s)
    (hg : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r) (hx : VKeep01 s t) : GRegsV B wx p v t :=
  ⟨fun k hk => (hg _ (gReg_ne k hk)).trans (h.base k hk), (hg _ (by decide)).trans h.bx,
    (hg _ (by decide)).trans h.r13, (hg _ (by decide)).trans h.r12,
    fun k hk l hl q hq => by rw [hx _ (gX_ne k hk).1 (gX_ne k hk).2.1]; exact h.msk k hk l hl q hq,
    fun l hl q hq => by rw [hx _ (by decide) (by decide)]; exact h.keep l hl q hq⟩

/-- Word `k` of `[aT]` after pass `p` with AVX2, from memory `m`. -/
def gvalV (m : Mem) (B : Addr) (wx p v k : Nat) : BitVec 64 :=
  gacc (fun j => word m B (slot wx (8 + 8 * p + j) + 8 * k)) (8 * p) v 7 |||
    (word m B (slot wx Crt.aT + 8 * k) &&& mask (decide (p ≠ 0)))

/-- After the entries `8 p` to `8 p + n` of the chunk at word `c`, from `s`. -/
structure GathAccV (s : State) (B : Addr) (wx p v c : Nat) (L : VLen) (n : Nat) (t : State) : Prop where
  acc : ∀ l < nl L, ∀ q < 2, q128 (t.lane .xmm0 l) q =
    gacc (fun j => word s.mem B (slot wx (8 + 8 * p + j) + 8 * c + 16 * l + 8 * q)) (8 * p) v n
  xmm : VKeep01 s t
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem nl_le (L : VLen) : nl L ≤ 2 := by cases L <;> decide

/-- The chunk at word `c` of an entry is within the table. -/
theorem gEntV_le (wx : Nat) {j c : Nat} (L : VLen) (hj : j < 32) (hc : c + 2 * nl L ≤ wx + 2) :
    slot wx (8 + j) + 8 * c + 16 * nl L ≤ slot wx 8 + tabBytes wx 32 := by
  have := ent_le wx hj; unfold slot at *; omega_arith

/-- The chunk at word `c` of `[aT]` is within its array. -/
theorem gTV_le (wx : Nat) {c : Nat} (L : VLen) (hc : c + 2 * nl L ≤ wx + 2) :
    slot wx Crt.aT + 8 * c + 16 * nl L ≤ slot wx 8 + tabBytes wx 32 := by
  have := slot_succ wx Crt.aT
  have := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  unfold tabBytes; omega_arith

theorem gAccV0 (L : VLen) {s : State} {B : Addr} {wx p v c : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (hc : c + 2 * nl L ≤ wx + 2) :
    WP isa (.block [.vbinLoad .vpand L .xmm0 .xmm8 (ix .rcx .r14)]) s (GathAccV s B wx p v c L 0) := by
  have hb := hG.base 0 (by decide)
  rw [Nat.add_zero] at hb
  refine WP.mono (gFirstV_ok L hs hb h14 (gEntV_le wx (j := 8 * p) L (by omega_arith) hc))
    fun t ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ⟨fun l hl q hq => ?_, hx, hg, hm, hrd, hwr⟩
  rw [hx0 l hl q hq, show s.lane .xmm8 l = s.lane (gX 0) l from rfl,
    hG.msk 0 (by decide) l (by have := nl_le L; omega_arith) q hq, BitVec.and_comm]
  rfl

theorem gAccV_step (L : VLen) {s t : State} {B : Addr} {wx p v c n : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (hc : c + 2 * nl L ≤ wx + 2)
    (hn : n < 7) (hA : GathAccV s B wx p v c L n t) :
    WP isa (.block (Crt.gatherOrV L (gReg (n + 1)) (gX (n + 1)))) t (GathAccV s B wx p v c L (n + 1)) := by
  have hb : t.gpr (gReg (n + 1)) = off B (slot wx (8 + 8 * p + (n + 1))) := by
    rw [hA.gpr]; exact hG.base _ (by omega_arith)
  have hnx := gX_ne (n + 1) (by omega_arith)
  refine WP.mono (gOrV_ok L (hs.congr hA.wr) (Nat.add_assoc 8 (8 * p) (n + 1) ▸ hb) (by rw [hA.gpr]; exact h14)
      (gEntV_le wx (j := 8 * p + (n + 1)) L (by omega_arith) hc))
    fun t' ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ⟨fun l hl q hq => ?_, fun y h0 h1 l => (hx y h0 h1 l).trans (hA.xmm y h0 h1 l),
      hg.trans hA.gpr, hm.trans hA.mem, hrd.trans hA.rd, hwr.trans hA.wr⟩
  rw [hx0 l hl q hq, hA.acc l hl q hq, hA.xmm _ hnx.1 hnx.2.1, hG.msk _ (by omega_arith) l (by have := nl_le L; omega_arith) q hq,
    hA.mem, BitVec.and_comm]
  simp only [gacc, Nat.add_assoc]

/-- The chunk at word `c` of a pass: `[aT] := ([aT] & keep) | OR_j (T_(8p+j) & mask_j)`, and `r14 += n`. -/
theorem gChunkV_ok (L : VLen) {s : State} {B : Addr} {wx p v c n : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 c) (hc : c + 2 * nl L ≤ wx + 2)
    (hn : n = 2 * nl L) :
    WP isa (.block (Crt.gatherBodyV L n)) s fun t =>
      (∀ k < 2 * nl L, word t.mem B (slot wx Crt.aT + 8 * (c + k)) = gvalV s.mem B wx p v (c + k)) ∧
      Outside B (slot wx Crt.aT + 8 * c) (16 * nl L) s.mem t.mem ∧
      t.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r14 → t.gpr r = s.gpr r) ∧
      VKeep01 s t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hnl := nl_le L
  simp only [Crt.gatherBodyV, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (gAccV0 L hs hG hp h14 hc) fun t₀ a₀ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 0) L hs hG hp h14 hc (by decide) a₀) fun t₁ a₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 1) L hs hG hp h14 hc (by decide) a₁) fun t₂ a₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 2) L hs hG hp h14 hc (by decide) a₂) fun t₃ a₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 3) L hs hG hp h14 hc (by decide) a₃) fun t₄ a₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 4) L hs hG hp h14 hc (by decide) a₄) fun t₅ a₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 5) L hs hG hp h14 hc (by decide) a₅) fun t₆ a₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gAccV_step (n := 6) L hs hG hp h14 hc (by decide) a₆) fun t₇ a₇ => ?_
  rw [WP.block_append_iff]
  have hT := gTV_le wx L hc
  refine WP.mono (gOrV_ok L (hs.congr a₇.wr) (x := .xmm7) (by rw [a₇.gpr]; exact hG.bx) (by rw [a₇.gpr]; exact h14)
    hT) fun t₈ ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ?_
  refine WP.mono (gStoreV_ok L (hs.congr (hwr.trans a₇.wr)) (by rw [hg, a₇.gpr]; exact hG.bx)
    (by rw [hg, a₇.gpr]; exact h14) hT (by cases L <;> simp only [nl] at hn <;> omega_arith))
    fun t ⟨hw', ho, h14', hg', hl', hrd', hwr'⟩ => ⟨fun k hk => ?_, by rw [hm, a₇.mem] at ho; exact ho, h14',
      fun r hr => by rw [hg' r hr, hg, a₇.gpr], fun y h0 h1 l => by rw [hl', hx y h0 h1 l, a₇.xmm y h0 h1 l],
      by rw [hrd', hrd, a₇.rd], by rw [hwr', hwr, a₇.wr]⟩
  obtain ⟨l, q, hl, hq, rfl⟩ : ∃ l q, l < nl L ∧ q < 2 ∧ k = 2 * l + q :=
    ⟨k / 2, k % 2, by omega_arith, Nat.mod_lt _ (by decide), by omega_arith⟩
  rw [show slot wx Crt.aT + 8 * (c + (2 * l + q)) = slot wx Crt.aT + 8 * c + 16 * l + 8 * q by omega_arith, hw' l hl q hq,
    hx0 l hl q hq, a₇.acc l hl q hq, a₇.xmm _ (by decide) (by decide), hG.keep l (by omega_arith) q hq, a₇.mem,
    BitVec.and_comm]
  unfold gvalV
  simp only [show ∀ j, slot wx (8 + 8 * p + j) + 8 * c + 16 * l + 8 * q = slot wx (8 + 8 * p + j) + 8 * (c + (2 * l + q))
    from fun j => by omega_arith, show slot wx Crt.aT + 8 * c + 16 * l + 8 * q = slot wx Crt.aT + 8 * (c + (2 * l + q)) by omega_arith]

/-! ## The chunks of a pass -/

theorem gvalV_congr {m m' : Mem} {B : Addr} {wx p v k : Nat}
    (he : ∀ j < 8, word m' B (slot wx (8 + 8 * p + j) + 8 * k) = word m B (slot wx (8 + 8 * p + j) + 8 * k))
    (hT : word m' B (slot wx Crt.aT + 8 * k) = word m B (slot wx Crt.aT + 8 * k)) :
    gvalV m' B wx p v k = gvalV m B wx p v k := by
  unfold gvalV
  rw [hT, gacc_congr fun j hj => he j (by omega_arith)]

/-- After the chunks of a pass below word `c`, from `s`. -/
structure GathInvV (s : State) (B : Addr) (wx p v c : Nat) (t : State) : Prop where
  r14 : t.gpr .r14 = BitVec.ofNat 64 c
  gpr : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r
  xmm : VKeep01 s t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : Outside B (slot wx Crt.aT) (8 * c) s.mem t.mem
  val : ∀ k < c, word t.mem B (slot wx Crt.aT + 8 * k) = gvalV s.mem B wx p v k

theorem GathInvV.init {s : State} {B : Addr} {wx p v : Nat} (h14 : s.gpr .r14 = BitVec.ofNat 64 0) :
    GathInvV s B wx p v 0 s :=
  ⟨h14, fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The chunk at word `c`, from the invariant below `c`. -/
theorem gStepV_ok (L : VLen) {s t : State} {B : Addr} {wx p v c n : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (hc : c + 2 * nl L ≤ wx + 2) (hn : n = 2 * nl L)
    (hI : GathInvV s B wx p v c t) :
    WP isa (.block (Crt.gatherBodyV L n)) t fun t' =>
      GathInvV s B wx p v (c + 2 * nl L) t' ∧ t'.gpr .r14 = BitVec.ofNat 64 c + BitVec.ofNat 64 n := by
  have hnw := hs.nowrap
  have hnl := nl_le L
  have hTa := slot_succ wx Crt.aT
  have hT8 := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  refine WP.mono (gChunkV_ok L (hs.congr hI.wr) (hG.congr hI.gpr hI.xmm) hp hI.r14 hc hn)
    fun t' ⟨hv, ho, h14, hg, hx, hrd, hwr⟩ => ⟨⟨by rw [h14, hn, ← BitVec.ofNat_add],
      fun r hr => (hg r hr).trans (hI.gpr r hr), fun y h0 h1 l => (hx y h0 h1 l).trans (hI.xmm y h0 h1 l),
      hrd.trans hI.rd, hwr.trans hI.wr, (hI.out.mono (Nat.le_refl _) (by omega_arith)).trans (ho.mono (by omega_arith) (by omega_arith)),
      fun k hk => ?_⟩, h14⟩
  by_cases hkc : k < c
  · rw [ho.word (by omega_arith) (by omega_arith), hI.val k hkc]
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 2 * nl L ∧ k = c + i := ⟨k - c, by omega_arith, by omega_arith⟩
  rw [hv i hi]
  refine gvalV_congr (fun j hj => ?_) ?_
  · have := ent_le wx (n := 32) (j := 8 * p + j) (by omega_arith)
    have := slot_mono wx (show 8 ≤ 8 + (8 * p + j) by omega_arith)
    rw [show 8 + 8 * p + j = 8 + (8 * p + j) by omega_arith]
    exact hI.out.word (by omega_arith) (by unfold slot at *; omega_arith)
  · exact hI.out.word (by omega_arith) (by omega_arith)

/-- The four-word chunks of a pass: every word below `4 N`. -/
theorem gLoopV_ok {s : State} {B : Addr} {wx p v N : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hN : 0 < N)
    (hN' : 4 * N ≤ wx + 1) (hw' : wx < 2 ^ 30) (h12 : s.gpr .r12 = BitVec.ofNat 64 (4 * N)) :
    WP isa (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne) s
      (GathInvV s B wx p v (4 * N)) := by
  refine wp_upto (a := 0) (N := N) hN (fun j => GathInvV s B wx p v (4 * j)) (fun j _ hj t hI => ?_) (fun t h => h)
    (by simpa using GathInvV.init h14)
  rw [WP.block_append_iff]
  refine WP.mono (gStepV_ok .l256 hs hG hp (c := 4 * j) (by simp only [nl]; omega_arith) rfl hI)
    fun t' ⟨hI', h14'⟩ => ?_
  have h12' : t'.gpr .r12 = BitVec.ofNat 64 (4 * N) := (hI'.gpr _ (by decide)).trans h12
  have hadd : BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 4 = BitVec.ofNat 64 (4 * (j + 1)) := by
    rw [← BitVec.ofNat_add]; congr 1
  refine WP.mono (WP.keep [.r14] (Q := fun t'' => t''.zf = some (decide (j + 1 = N)) ∧ t''.mem = t'.mem ∧
      (∀ y l, t''.lane y l = t'.lane y l) ∧ t''.gpr .r14 = t'.gpr .r14) (by
    xrun [h14', h12', hadd, ofNat_sub_beq (show 4 * (j + 1) < 2 ^ 64 by omega_arith) (show 4 * N < 2 ^ 64 by omega_arith)]
    exact ⟨decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩, fun _ _ => rfl⟩) rfl) fun t'' ⟨⟨hz, hm, hl, h14''⟩, k⟩ => ⟨hz, ?_⟩
  have hk : ∀ r, r ≠ .r14 → t''.gpr r = t'.gpr r := fun r hr => k.1 r (by simpa using hr)
  exact ⟨by rw [h14'', h14', hadd], fun r hr => by rw [hk r hr]; exact hI'.gpr r hr,
    fun y h0 h1 l => (hl y l).trans (hI'.xmm y h0 h1 l), k.2.1.trans hI'.rd, k.2.2.trans hI'.wr,
    by rw [hm]; simpa [nl, Nat.mul_add] using hI'.out, fun k' hk' => by rw [hm]; exact hI'.val k' (by simp only [nl]; omega_arith)⟩

end VG.Proof.Bignum.X86_64

end

end


/-!
# RSA with the CRT on x86-64: the table's selection with AVX2

`Crt.tabSelectV` reads entry `v` of the window's table into `[aT]` as
`Crt.tabSelect` does (`tabSelV_ok`), its passes four words at a time
(`CrtSelV.lean`), so it is a `CrtSel` (`CrtSel.avx`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## A pass's head -/

theorem r12V_eq (M : Nat) (hM : 2 * M < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * M) >>> 2) + (BitVec.ofNat 64 (2 * M) >>> 2) +
      ((BitVec.ofNat 64 (2 * M) >>> 2) + (BitVec.ofNat 64 (2 * M) >>> 2)) = BitVec.ofNat 64 (4 * (M / 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- A pass's registers, as `gRegs_ok`, and `r12 = 4 ⌊M / 2⌋` for `M = ⌈w / 2⌉`. -/
theorem gRegsV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc p n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hw' : wx < 2 ^ 30)
    (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 (8 * p))
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + 8 * p))) :
    WP isa (.block Crt.gatherRegsV) t fun t' =>
      t'.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧ t'.gpr .rcx = off P (slot wx (8 + 8 * p)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ t'.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2)) ∧
      t'.gpr .r12 = BitVec.ofNat 64 (4 * ((wx + 1) / 2 / 2)) ∧
      t'.gpr .rbx = off P (slot wx Crt.aT) ∧ t'.mem = t.mem ∧ (∀ y l, t'.lane y l = t.lane y l) ∧
      Keep [.r15, .rcx, .r12, .r11, .r13, .rbx] t t' := by
  refine WP.block_append_iff.mpr (WP.mono (WP.vecKeep (by decide) (gRegs_ok hc hw' hJ hE))
    fun t₁ ⟨⟨h15, hcx, h11, h13, hbx, hm, _, k₁⟩, hx₁, hy₁⟩ => ?_)
  refine WP.mono (WP.vecKeep (by decide) (WP.keep [.r12] (Q := fun t' => t'.gpr .r12 =
      BitVec.ofNat 64 (4 * ((wx + 1) / 2 / 2)) ∧ t'.mem = t₁.mem) (by
    xrun [h13, r12V_eq ((wx + 1) / 2) (by omega_arith)]) rfl)) fun t' ⟨⟨⟨h12, hm'⟩, k'⟩, hx', hy'⟩ =>
      ⟨by rw [k'.gpr (by decide)]; exact h15, by rw [k'.gpr (by decide)]; exact hcx,
        by rw [k'.gpr (by decide)]; exact h11, by rw [k'.gpr (by decide)]; exact h13, h12,
        by rw [k'.gpr (by decide)]; exact hbx, hm'.trans hm,
        fun y l => by simp only [State.lane, hx', hy', hx₁, hy₁], (k₁.trans k').mono (by decide)⟩

/-- `x := r14` in every quadword: `vmovq`, `vpbroadcastq`. -/
theorem dupV_ok {s : State} (x : XReg) :
    WP isa (.block [.vop (.vmovq x .r14), .vop (.vpbroadcastq .l256 x x)]) s fun t =>
      (∀ l < 2, ∀ q < 2, q128 (t.lane x l) q = s.gpr .r14) ∧ (∀ y, y ≠ x → ∀ l, t.lane y l = s.lane y l) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl q hq => ?_, fun y hy l => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [VOp.exec, State.lane_setV256, ↓reduceIte, VG.X86_64.RegUpd.xmm_setV]
    rw [show qword ((0 : BitVec 64) ++ s.gpr .r14) 0 = s.gpr .r14 from q128_low _]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp only [↓reduceIte, Nat.one_ne_zero] <;>
      exact q128_pair _ hq
  · simp only [VOp.exec, State.lane_setV256, State.lane_setV128, hy, ↓reduceIte]

/-- The mask of `k + j = v` in every quadword of `x`, `v` in `sNib` and `k` in `r15`. -/
theorem gMaskV_ok {t : State} {P : Addr} {k j v : Nat} (hdi : t.gpr .rdi = P)
    (hld : InRegions (t.rd ++ t.wr) (off P (8 * Crt.sNib)) 8) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (h15 : t.gpr .r15 = BitVec.ofNat 64 k) (hk : k < 32) (hj : j < 8) (hv : v < 32) (x : XReg) :
    WP isa (.block (Crt.selMaskV (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x)) t fun t' =>
      (∀ l < 2, ∀ q < 2, q128 (t'.lane x l) q = mask (decide (k + j = v))) ∧
      (∀ y, y ≠ x → ∀ l, t'.lane y l = t.lane y l) ∧ t'.mem = t.mem ∧ Keep [.r14] t t' := by
  rw [show Crt.selMaskV (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x =
    ([.mov .r14 (.reg .r15), .alu .add .r14 (.imm (BitVec.ofNat 32 j)), .alu .xor .r14 (.mem (hdr Crt.sNib)),
      .alu .cmp .r14 (.imm 1), .alu .sbb .r14 (.reg .r14)] : List Instr) ++
    ([.vop (.vmovq x .r14), .vop (.vpbroadcastq .l256 x x)] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.vecKeep rfl (WP.keep [.r14] (Q := fun t' =>
      (∃ b : Bool, b = decide (BitVec.ofNat 64 k + BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 v = 0) ∧
        t'.gpr .r14 = mask b) ∧ t'.mem = t.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hld, hN, h15, sx_ofNat (show j < 2 ^ 31 by omega_arith)]
    exact ⟨_, decide_lt_one _, rfl⟩) rfl)) fun t₁ ⟨⟨⟨⟨b, hb, h14⟩, hm⟩, k₁⟩, hx₁, hy₁⟩ => ?_)
  refine WP.mono (dupV_ok x) fun t' ⟨hd, hy, hg, hm', hrd, hwr⟩ => ⟨fun l hl q hq => ?_,
    fun y hy' l => by rw [hy y hy' l]; simp only [State.lane, hx₁, hy₁], by rw [hm', hm], ?_⟩
  · rw [hd l hl q hq, h14, hb, BitVec.ofNat_add_ofNat]
    congr 1
    exact decide_eq_decide.mpr (xor_eq_zero_iff.trans (ofNat64_inj (by omega_arith) (by omega_arith)))
  · exact ⟨fun r hr => by rw [hg]; exact k₁.1 r hr, hrd.trans k₁.2.1, hwr.trans k₁.2.2⟩

/-- The mask of `p ≠ 0` in every quadword of `ymm7`, `8 p` in `r15`. -/
theorem gKeepV_ok {t : State} {p : Nat} (h15 : t.gpr .r15 = BitVec.ofNat 64 (8 * p)) (hp : p < 4) :
    WP isa (.block Crt.keepMaskV) t fun t' =>
      (∀ l < 2, ∀ q < 2, q128 (t'.lane .xmm7 l) q = mask (decide (p ≠ 0))) ∧
      (∀ y, y ≠ .xmm7 → ∀ l, t'.lane y l = t.lane y l) ∧ t'.mem = t.mem ∧ Keep [.r14] t t' := by
  rw [show Crt.keepMaskV =
    ([.mov32 .r14 (.imm 0), .alu .cmp .r14 (.reg .r15), .alu .sbb .r14 (.reg .r14)] : List Instr) ++
    ([.vop (.vmovq .xmm7 .r14), .vop (.vpbroadcastq .l256 .xmm7 .xmm7)] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.vecKeep (by decide) (WP.keep [.r14] (Q := fun t' =>
      t'.gpr .r14 = mask (decide (p ≠ 0)) ∧ t'.mem = t.mem) (by
    xrun [h15]
    rcases (by omega_arith : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;> decide) rfl))
      fun t₁ ⟨⟨⟨h14, hm⟩, k₁⟩, hx₁, hy₁⟩ => ?_)
  refine WP.mono (dupV_ok .xmm7) fun t' ⟨hd, hy, hg, hm', hrd, hwr⟩ => ⟨fun l hl q hq => by rw [hd l hl q hq, h14],
    fun y hy' l => by rw [hy y hy' l]; simp only [State.lane, hx₁, hy₁], by rw [hm', hm], ?_⟩
  exact ⟨fun r hr => by rw [hg]; exact k₁.1 r hr, hrd.trans k₁.2.1, hwr.trans k₁.2.2⟩

/-- A pass's head with AVX2: its registers, masks and bases. -/
theorem gathHeadV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v p : Nat}
    (hc : CExpCtx t P wx minv X Xc 32) (hw' : wx < 2 ^ 30) (hv : v < 32) (hp : p < 4)
    (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 (8 * p))
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + 8 * p))) :
    WP isa (seqs Crt.gatherHeadV) t fun s => GRegsV P wx p v s ∧ s.gpr .r14 = BitVec.ofNat 64 0 ∧
      s.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ s.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧ s.mem = t.mem ∧
      Keep mmRegs t s := by
  simp only [Crt.gatherHeadV, seqs]
  refine WP.seq (WP.mono (gRegsV_ok hc hw' hJ hE) fun t₁ ⟨h15, hcx, h11, h13, h12, hbx, hm₁, _, k₁⟩ => ?_)
  have hdi₁ : t₁.gpr .rdi = P := (k₁.gpr (by decide)).trans hc.good.rdi
  have hld : ∀ s : State, s.mem = t.mem → s.rd = t.rd → s.wr = t.wr →
      InRegions (s.rd ++ s.wr) (off P (8 * Crt.sNib)) 8 := fun s _ hrd hwr => by
    rw [hrd, hwr]; exact hc.ld (by decide)
  have mstep : ∀ (s : State) (j : Nat) (x : XReg), j < 8 → s.gpr .rdi = P → s.mem = t.mem → s.rd = t.rd →
      s.wr = t.wr → s.gpr .r15 = BitVec.ofNat 64 (8 * p) →
      WP isa (.block (Crt.selMaskV (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x)) s fun s' =>
        (∀ l < 2, ∀ q < 2, q128 (s'.lane x l) q = mask (decide (8 * p + j = v))) ∧
        (∀ y, y ≠ x → ∀ l, s'.lane y l = s.lane y l) ∧
        s'.mem = t.mem ∧ s'.gpr .rdi = P ∧ s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧
        Keep [.r14] s s' :=
    fun s j x hj hdi hm hrd hwr h15 => WP.mono (gMaskV_ok hdi (hld s hm hrd hwr) (by rw [hm]; exact hN) h15
      (by omega_arith) hj hv x) fun s' ⟨hq, hy, hm', k⟩ =>
        ⟨hq, hy, hm'.trans hm, (k.gpr (by decide)).trans hdi, k.2.1.trans hrd, k.2.2.trans hwr,
          (k.gpr (by decide)).trans h15, k⟩
  refine WP.seq (WP.mono (mstep t₁ 0 .xmm8 (by decide) hdi₁ hm₁ k₁.2.1 k₁.2.2 h15)
    fun s₀ ⟨q₀, y₀, m₀, d₀, r₀, w₀, f₀, k₀⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₀ 1 .xmm9 (by decide) d₀ m₀ r₀ w₀ f₀)
    fun s₁ ⟨q₁, y₁, m₁, d₁, r₁, w₁, f₁, k₁'⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₁ 2 .xmm10 (by decide) d₁ m₁ r₁ w₁ f₁)
    fun s₂ ⟨q₂, y₂, m₂, d₂, r₂, w₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₂ 3 .xmm11 (by decide) d₂ m₂ r₂ w₂ f₂)
    fun s₃ ⟨q₃, y₃, m₃, d₃, r₃, w₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₃ 4 .xmm12 (by decide) d₃ m₃ r₃ w₃ f₃)
    fun s₄ ⟨q₄, y₄, m₄, d₄, r₄, w₄, f₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₄ 5 .xmm13 (by decide) d₄ m₄ r₄ w₄ f₄)
    fun s₅ ⟨q₅, y₅, m₅, d₅, r₅, w₅, f₅, k₅⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₅ 6 .xmm14 (by decide) d₅ m₅ r₅ w₅ f₅)
    fun s₆ ⟨q₆, y₆, m₆, d₆, r₆, w₆, f₆, k₆⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₆ 7 .xmm15 (by decide) d₆ m₆ r₆ w₆ f₆)
    fun s₇ ⟨q₇, y₇, m₇, d₇, r₇, w₇, f₇, k₇⟩ => ?_)
  refine WP.seq (WP.mono (gKeepV_ok f₇ hp) fun s₈ ⟨q₈, y₈, m₈, k₈⟩ => ?_)
  have kM := ((((((((k₀.trans k₁').trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈)
  have hcx₈ : s₈.gpr .rcx = off P (slot wx (8 + 8 * p)) := (kM.gpr (by decide)).trans hcx
  have h11₈ : s₈.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) := (kM.gpr (by decide)).trans h11
  refine WP.mono (WP.vecKeep (by decide) (gBases_ok hcx₈ h11₈)) fun s₉ ⟨⟨hb, h14, m₉, _, k₉⟩, hx₉, hy₉⟩ => ?_
  have kA := kM.trans k₉
  have l₉ : ∀ y l, s₉.lane y l = s₈.lane y l := fun y l => by simp only [State.lane, hx₉, hy₉]
  have hG : GRegsV P wx p v s₉ := by
    refine ⟨hb, by rw [kA.gpr (by decide)]; exact hbx, by rw [kA.gpr (by decide)]; exact h13,
      by rw [kA.gpr (by decide)]; exact h12, fun k hk l hl q hq => ?_, fun l hl q hq => by rw [l₉]; exact q₈ l hl q hq⟩
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega_arith
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show gX 0 = .xmm8 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide), y₂ _ (by decide), y₁ _ (by decide)]; exact q₀ l hl q hq
    · rw [show gX 1 = .xmm9 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide), y₂ _ (by decide)]; exact q₁ l hl q hq
    · rw [show gX 2 = .xmm10 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide)]; exact q₂ l hl q hq
    · rw [show gX 3 = .xmm11 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide)]; exact q₃ l hl q hq
    · rw [show gX 4 = .xmm12 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide)]
      exact q₄ l hl q hq
    · rw [show gX 5 = .xmm13 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide)]; exact q₅ l hl q hq
    · rw [show gX 6 = .xmm14 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide)]; exact q₆ l hl q hq
    · rw [show gX 7 = .xmm15 from rfl, l₉, y₈ _ (by decide)]; exact q₇ l hl q hq
  exact ⟨hG, h14, by rw [kA.gpr (by decide)]; exact h11, by rw [kA.gpr (by decide)]; exact h15,
    by rw [m₉, m₈, m₇], (k₁.trans kA).mono (by decide)⟩

/-- The words of `[aT]` below `2 ⌈w / 2⌉` after a pass's chunks: the four-word
loop if any, then the last two words if left. -/
theorem gChunksV_ok {s : State} {B : Addr} {wx p v : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    {c : Prog isa} {Q : State → Prop}
    (hk : ∀ t, (∃ s₀ : State, s₀.mem = s.mem ∧ GathInvV s₀ B wx p v (2 * ((wx + 1) / 2)) t ∧
        (∀ r, r ≠ .r14 → s₀.gpr r = s.gpr r) ∧ (∀ y l, s₀.lane y l = s.lane y l) ∧ s₀.rd = s.rd ∧ s₀.wr = s.wr) →
      WP isa c t Q) :
    WP isa (.seq (.block [.alu .test .r12 (.reg .r12)])
      (.seq (.ite .ne (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne)
          (.block []))
        (.seq (.block [.alu .cmp .r14 (.reg .r13)]) (.seq (.ite .ne (.block (Crt.gatherBodyV .l128 2)) (.block [])) c)))) s
      Q := by
  have hM := (wx + 1) / 2
  -- `ZF` of `r12 = 4 ⌊M / 2⌋`.
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t => t.zf = some (decide ((wx + 1) / 2 / 2 = 0)) ∧ t.mem = s.mem ∧
      (∀ y l, t.lane y l = s.lane y l) ∧ t.gpr .r12 = s.gpr .r12) (by
    xrun [hG.r12, BitVec.and_self, ofNat_beq_zero (show 4 * ((wx + 1) / 2 / 2) < 2 ^ 64 by omega_arith)]
    exact ⟨decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩, fun _ _ => rfl⟩) rfl)
    fun s₁ ⟨⟨hz₁, hm₁, hl₁, h12₁⟩, k₁⟩ => ?_)
  have hg₁ : s₁.gpr = s.gpr := funext fun r => by
    by_cases hr : r = .r12
    · rw [hr, h12₁]
    · exact k₁.1 r (by simpa using hr)
  have hs₁ : Scr s₁ B (slot wx 8 + tabBytes wx 32) := hs.congr k₁.2.2
  have hG₁ : GRegsV B wx p v s₁ := hG.congr (fun r _ => by rw [hg₁]) (fun y _ _ l => hl₁ y l)
  have h14₁ : s₁.gpr .r14 = BitVec.ofNat 64 0 := by rw [hg₁]; exact h14
  -- The four-word chunks.
  have hloop : WP isa (.ite .ne (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] :
      List Instr))) .ne) (.block [])) s₁ (GathInvV s₁ B wx p v (4 * ((wx + 1) / 2 / 2))) := by
    by_cases hN : (wx + 1) / 2 / 2 = 0
    · refine WP.ite false (by simp [eval, hz₁, hN]) (by simp) (fun _ => WP.block_nil ?_)
      rw [hN]; exact GathInvV.init h14₁
    · refine WP.ite true (by simp [eval, hz₁, hN]) (fun _ => ?_) (by simp)
      exact gLoopV_ok hs₁ hG₁ hp h14₁ (by omega_arith) (by omega_arith) hw' hG₁.r12
  refine WP.seq (WP.mono hloop fun s₂ hI₂ => ?_)
  -- The last two words, if left.
  have hr13 : s₂.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2)) := by rw [hI₂.gpr _ (by decide)]; exact hG₁.r13
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.zf = some (decide (4 * ((wx + 1) / 2 / 2) = 2 * ((wx + 1) / 2))) ∧
      t.mem = s₂.mem ∧ (∀ y l, t.lane y l = s₂.lane y l) ∧ t.gpr .r14 = s₂.gpr .r14) (by
    xrun [hI₂.r14, hr13, ofNat_sub_beq (show 4 * ((wx + 1) / 2 / 2) < 2 ^ 64 by omega_arith)
      (show 2 * ((wx + 1) / 2) < 2 ^ 64 by omega_arith)]
    exact fun _ _ => rfl) rfl) fun s₃ ⟨⟨hz₃, hm₃, hl₃, h14₃⟩, k₃⟩ => ?_)
  have hg₃ : s₃.gpr = s₂.gpr := funext fun r => by
    by_cases hr : r = .r14
    · rw [hr, h14₃]
    · exact k₃.1 r (by simpa using hr)
  have hI₃ : GathInvV s₁ B wx p v (4 * ((wx + 1) / 2 / 2)) s₃ :=
    ⟨by rw [hg₃]; exact hI₂.r14, fun r hr => by rw [hg₃]; exact hI₂.gpr r hr,
      fun y h0 h1 l => (hl₃ y l).trans (hI₂.xmm y h0 h1 l), k₃.2.1.trans hI₂.rd, k₃.2.2.trans hI₂.wr,
      by rw [hm₃]; exact hI₂.out, fun k hk => by rw [hm₃]; exact hI₂.val k hk⟩
  have hfin : ∀ t, GathInvV s₁ B wx p v (2 * ((wx + 1) / 2)) t →
      ∃ s₀ : State, s₀.mem = s.mem ∧ GathInvV s₀ B wx p v (2 * ((wx + 1) / 2)) t ∧
        (∀ r, r ≠ .r14 → s₀.gpr r = s.gpr r) ∧ (∀ y l, s₀.lane y l = s.lane y l) ∧ s₀.rd = s.rd ∧ s₀.wr = s.wr :=
    fun t h => ⟨s₁, hm₁, h, fun r _ => by rw [hg₁], hl₁, k₁.2.1, k₁.2.2⟩
  refine WP.seq (WP.mono ?_ hk)
  by_cases hodd : 4 * ((wx + 1) / 2 / 2) = 2 * ((wx + 1) / 2)
  · refine WP.ite false (by simp [eval, hz₃, hodd]) (by simp) (fun _ => WP.block_nil (hfin _ ?_))
    rw [← hodd]; exact hI₃
  · refine WP.ite true (by simp [eval, hz₃, hodd]) (fun _ => ?_) (by simp)
    refine WP.mono (gStepV_ok .l128 hs₁ hG₁ hp (c := 4 * ((wx + 1) / 2 / 2)) (by simp only [nl]; omega_arith) rfl hI₃)
      fun t ⟨hI, _⟩ => hfin t ?_
    rw [show 2 * ((wx + 1) / 2) = 4 * ((wx + 1) / 2 / 2) + 2 * nl .l128 by simp only [nl]; omega_arith]
    exact hI

/-- The pass's end with AVX2: as `gEnd_ok`, `ZF` after the fourth. -/
theorem gEndV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc p n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hp : p < 4) (h7 : t.gpr .rax = off P (slot wx (8 + 8 * p + 7)))
    (h11 : t.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2))) (h15 : t.gpr .r15 = BitVec.ofNat 64 (8 * p)) :
    WP isa (.block Crt.gatherEndV) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx (8 + 8 * (p + 1))))).writeW (off P (8 * Crt.sJ))
        (BitVec.ofNat 64 (8 * (p + 1))) ∧ t'.zf = some (decide (p + 1 = 4)) ∧ Keep [.rax] t t' := by
  have hs : slot wx (8 + 8 * p + 7) + 8 * (wx + 2) = slot wx (8 + 8 * (p + 1)) := by
    rw [← slot_succ, show 8 + 8 * p + 7 + 1 = 8 + 8 * (p + 1) by omega_arith]
  have h8 : BitVec.ofNat 64 (8 * p) + 8 = BitVec.ofNat 64 (8 * (p + 1)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt))
      (off P (slot wx (8 + 8 * (p + 1))))).writeW (off P (8 * Crt.sJ)) (BitVec.ofNat 64 (8 * (p + 1))) ∧
      t'.zf = some (decide (p + 1 = 4))) (by
    unfold Crt.gatherEndV
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sEnt) (by decide), hc.st (i := Crt.sJ) (by decide),
      h7, h11, h15, off_add_eq, hs, sx_ofNat (show 8 < 2 ^ 31 by omega_arith), h8]
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
      ofNat_sub_beq (show 8 * (p + 1) < 2 ^ 64 by omega_arith) (show 32 < 2 ^ 64 by decide)]
    exact decide_eq_decide.mpr (by omega_arith)) rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- Pass `p` of the selection with AVX2. -/
theorem gPassV_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v p : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 32) (hp : p < 4) (hI : GathPassInv t₀ P wx minv X Xc v 32 p t) :
    WP isa (seqs Crt.gatherPassV) t fun t' => t'.zf = some (decide (p + 1 = 4)) ∧
      GathPassInv t₀ P wx minv X Xc v 32 (p + 1) t' := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hTa := slot_succ wx Crt.aT
  have hT8 := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  rw [show seqs Crt.gatherPassV = .seq (seqs Crt.gatherHeadV) (.seq (.block [.alu .test .r12 (.reg .r12)])
      (.seq (.ite .ne (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne)
          (.block []))
        (.seq (.block [.alu .cmp .r14 (.reg .r13)]) (.seq (.ite .ne (.block (Crt.gatherBodyV .l128 2)) (.block []))
          (.block Crt.gatherEndV))))) from rfl]
  refine WP.seq (WP.mono (gathHeadV_ok hc hw' hv hp hI.nib hI.idx hI.ent) fun s₉ ⟨hG, h14, h11, h15, hm₉, kA⟩ => ?_)
  have hs₉ : Scr s₉ P (slot wx 8 + tabBytes wx 32) := hc.scrT.congr kA.2.2
  -- The chunks.
  refine gChunksV_ok hs₉ hG hp h14 hw hw' fun s₁₀ ⟨s₀, hm₀, hL, hg₀, _, hrd₀, hwr₀⟩ => ?_
  have hgL : ∀ r, r ≠ .r14 → s₁₀.gpr r = s₉.gpr r := fun r hr => (hL.gpr r hr).trans (hg₀ r hr)
  have kL : Keep [.r14] s₉ s₁₀ := ⟨fun r hr => hgL r (by simpa using hr), hL.rd.trans hrd₀, hL.wr.trans hwr₀⟩
  have oL : Outside P (slot wx Crt.aT) (8 * (wx + 2)) t.mem s₁₀.mem := by
    rw [← hm₉, ← hm₀]; exact hL.out.mono (Nat.le_refl _) (by omega_arith)
  have hc₁₀ : CExpCtx s₁₀ P wx minv X Xc 32 :=
    hc.of_win (Frm.of_outside oL (by simp [crtWinRanges])) (by rw [kL.2.2, kA.2.2]) ((kA.trans kL).gpr (by decide))
  refine WP.mono (gEndV_ok hc₁₀ hp (by rw [hgL _ (by decide)]; exact hG.base 7 (by decide))
    (by rw [hgL _ (by decide)]; exact h11) (by rw [hgL _ (by decide)]; exact h15)) fun t' ⟨hm', hz, k'⟩ => ⟨hz, ?_⟩
  -- What changed.
  have o₁ := writeW_outside s₁₀.mem P (d := 8 * Crt.sEnt) (off P (slot wx (8 + 8 * (p + 1)))) (by decide)
  have o₂ := writeW_outside (s₁₀.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx (8 + 8 * (p + 1))))) P
    (d := 8 * Crt.sJ) (BitVec.ofNat 64 (8 * (p + 1))) (by decide)
  rw [← hm'] at o₂
  have fL : Frm P (selRanges wx) t.mem s₁₀.mem := Frm.of_outside oL (by simp [selRanges])
  have fE : Frm P (selRanges wx) s₁₀.mem t'.mem :=
    (Frm.of_outside o₁ (by simp [selRanges])).trans (Frm.of_outside o₂ (by simp [selRanges]))
  have hT : ∀ k < 2 * ((wx + 1) / 2), word t'.mem P (slot wx Crt.aT + 8 * k) = word s₁₀.mem P (slot wx Crt.aT + 8 * k) :=
    fun k hk => by
      have := hdr_lt_slot wx Crt.aT (show Crt.sJ < 32 by decide)
      have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide)
      rw [o₂.word (by omega_arith) (by omega_arith), o₁.word (by omega_arith) (by omega_arith)]
  have hE : ∀ j < 32, ∀ k < 2 * ((wx + 1) / 2), word t.mem P (slot wx (8 + j) + 8 * k) =
      word t₀.mem P (slot wx (8 + j) + 8 * k) := fun j hj k hk =>
    hI.frm.word_eq (fun r hr => by
      have := hdr_lt_slot wx 8 (show 31 < 32 by decide)
      have := slot_mono wx (show 8 ≤ 8 + j by omega_arith)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; omega_arith
      · simp only [Crt.sJ, sFn]; omega_arith) (by have := ent_le wx hj; omega_arith)
  refine ⟨hc₁₀.of_win (fE.mono (selRanges_sub wx)) k'.2.2 (k'.gpr (by decide)), ?_, ?_, ?_, Or.inr fun k hk => ?_,
    hI.frm.trans (fL.trans fE), ((hI.keep.trans ((kA.trans kL).trans k')).mono (by decide))⟩
  · have := hdr_lt_slot wx Crt.aT (show Crt.sNib < 32 by decide)
    rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), oL.word (by omega_arith) (by omega_arith)]
    exact hI.nib
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm', word_writeW_self]
  · rw [hT k hk, hL.val k hk, hm₀, hm₉]
    simp only [gvalV, gacc_eq, gath_and_mask]
    have hold := hI.val
    have hv' : v < 32 := hv
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · by_cases h8 : v < 8
      · simp [h8, show v ≤ 8 * 0 + 7 by omega_arith, hE v (by omega_arith) k hk]
      · simp [h8, show ¬ v ≤ 8 * 0 + 7 by omega_arith]
    · rcases hold with h | hold
      · omega_arith
      rw [hold k hk]
      have hp0' : p ≠ 0 := by omega_arith
      by_cases h8 : v < 8 * p
      · simp [h8, hp0', show ¬ 8 * p ≤ v by omega_arith, show v < 8 * (p + 1) by omega_arith]
      · by_cases h8' : v < 8 * (p + 1)
        · simp [h8, h8', hp0', show 8 * p ≤ v by omega_arith, show v ≤ 8 * p + 7 by omega_arith,
            show 8 + 8 * p + (v - 8 * p) = 8 + v by omega_arith, hE v (by omega_arith) k hk]
        · simp [h8, h8', hp0', show ¬ v ≤ 8 * p + 7 by omega_arith]

theorem tabSelectV_eq : Crt.tabSelectV = [.block [.mov .rax (.mem (hdr Crt.sTab)), .store (hdr Crt.sEnt) .rax,
    .mov32 .rax (.imm 0), .store (hdr Crt.sJ) .rax], .loop (seqs Crt.gatherPassV) .ne,
    .block [.vop .vzeroupper]] := rfl

/-- `vzeroupper` keeps all but the vector registers' upper bits. -/
theorem vzu_ok (s : State) : WP isa (.block [.vop .vzeroupper]) s fun t =>
    t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The selection with AVX2: `[aT] := T_v`. -/
theorem tabSelV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx t P wx minv X Xc 32) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 32)
    (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (seqs Crt.tabSelectV) t fun t' => CExpCtx t' P wx minv X Xc 32 ∧
      wv t'.mem P (slot wx Crt.aT) wx = wv t.mem P (slot wx (8 + v)) wx ∧
      Frm P (selRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  rw [tabSelectV_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sEnt) (off P (slot wx 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))) P (d := 8 * Crt.sJ)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (selRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [selRanges])).trans (Frm.of_outside o2 (by simp [selRanges]))
  have h₁ : GathPassInv t₁ P wx minv X Xc v 32 0 t₁ := by
    refine ⟨hc.of_win (f₁.mono (selRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide)), ?_, ?_, ?_, .inl rfl,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₁, word_writeW_self]; rfl
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 4) (by decide) (GathPassInv t₁ P wx minv X Xc v 32)
    (fun p _ hp s hI => gPassV_ok hw hw' hv hp hI) (fun s h => h) h₁) fun t₂ hI => ?_)
  -- `vzeroupper`.
  refine WP.mono (vzu_ok t₂) fun t₃ ⟨hg₃, hm₃, hrd₃, hwr₃⟩ => ?_
  have hEv : ∀ i < wx, word t₁.mem P (slot wx (8 + v) + 8 * i) = word t.mem P (slot wx (8 + v) + 8 * i) :=
    fun i hi => f₁.word_eq (fun r hr => by
      have := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
      have := hdr_lt_slot wx 8 (show 31 < 32 by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := slot_le (w := wx) (show Crt.aT < 8 by decide); simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; omega_arith
      · simp only [Crt.sJ, sFn]; omega_arith) (by have := ent_le wx hv; omega_arith)
  have k₂ : Keep mmRegs t t₂ := (k₁.trans hI.keep).mono (by decide)
  refine ⟨hI.ctx.of_frm (by rw [hm₃]; exact Frm.refl _ _ _) (by rw [hwr₃]) (by rw [hg₃]), wv_congr2 fun i hi => ?_,
    by rw [hm₃]; exact f₁.trans hI.frm, ⟨fun r hr => by rw [hg₃]; exact k₂.1 r hr, hrd₃.trans k₂.2.1, hwr₃.trans k₂.2.2⟩⟩
  rw [hm₃]
  rcases hI.val with h | h
  · omega_arith
  rw [h i (by omega_arith), ite_eq_left (by omega_arith), hEv i hi]

/-- The selection with AVX2, from a table of 32 entries. -/
def CrtSel.avx : CrtSel 32 := ⟨Crt.tabSelectV, by simp [tabSelectV_eq], tabSelV_ok⟩

end VG.Proof.Bignum.X86_64

end

end


/-!
# RSA with the CRT on x86-64: the exponentiation, as the phases need it

`Crt.code mul ex` takes its exponentiation in a prime's workspace, `ex sp sl`
for the exponent's pointer and length in `n`'s slots `sp` and `sl`: `expLoop`
by windows of 4 bits with a table of 16 entries (`CrtExpL.w4`), or
`expLoop5S` by windows of 5 bits with a table of 32 read with AVX2
(`CrtExpL.w5S`). A `CrtExpL` is such a code with what the phases need of
it: `Y := x^e R` in the prime's `aY`, changing only `crtExpRanges5`, within
the room for a table of 32 entries.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- An exponentiation in a prime's workspace, by the multiplication `M`:
as `crtExpLoop_ok`. -/
structure CrtExpL (M : Mont) where
  code : Nat → Nat → List (Prog isa)
  ne : ∀ sp sl, code sp sl ≠ []
  ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat} {Q : Prop}
    (hc : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hw2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (code sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges5 wx) s.mem t.mem ∧ Keep mmRegs s t

/-- `expLoop`'s ranges are within `expLoop5S`'s. -/
theorem crtExpRanges_widen5 (wx : Nat) :
    ∀ r ∈ crtExpRanges wx, ∃ r' ∈ crtExpRanges5 wx, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  intro r hr
  simp only [crtExpRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(slot wx 8, tabBytes wx 32), by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _,
      by unfold tabBytes; omega_using []⟩
  · exact ⟨r, crtExpRanges_sub5 wx r (crtWinRanges_sub wx r hr), Nat.le_refl _, Nat.le_refl _⟩

/-- `expLoop` by windows of 4 bits, its table of 16 read with SSE2. -/
def CrtExpL.w4 (M : Mont) : CrtExpL M where
  code := Crt.expLoop M.mm Crt.tabSelect
  ne _ _ := by simp [Crt.expLoop, Crt.expLoopS]
  ok hc _ hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he :=
    WP.mono (crtExpLoop_ok M CrtSel.sse hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he)
      fun _ ⟨h1, h2, h3, f, k⟩ => ⟨h1, h2, h3, f.widen (crtExpRanges_widen5 _), k⟩

/-- `CrtExpL.w4` with its squarings by `Sq`. -/
def CrtExpL.w4S (M : Mont) (Sq : MontS) : CrtExpL M where
  code := Crt.expLoopS Sq.mm M.mm Crt.tabSelect
  ne _ _ := by simp [Crt.expLoopS]
  ok hc _ hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he :=
    WP.mono (crtExpLoopS_ok M Sq CrtSel.sse hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he)
      fun _ ⟨h1, h2, h3, f, k⟩ => ⟨h1, h2, h3, f.widen (crtExpRanges_widen5 _), k⟩

/-- The loop by windows of 5 bits, with its squarings by `Sq`. -/
def CrtExpL.w5S (M : Mont) (Sq : MontS) : CrtExpL M where
  code := Crt.expLoop5S Sq.mm M.mm Crt.tabSelectV
  ne _ _ := by simp [Crt.expLoop5S]
  ok hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he :=
    crtExpLoop5S_ok M Sq CrtSel.avx hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he

end VG.Proof.Bignum.X86_64
