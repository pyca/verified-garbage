module

-- separate module: the digits block, which xmssTree and xmssPk share

public import VerifiedGarbage.Proof.SlhDsa.AArch64.TreeBase
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Xmss
public import VerifiedGarbage.Proof.SlhDsa.VerifySpec
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: the digits of a message

`Xmss.digits` (`Impl/SlhDsa/AArch64/Xmss.lean`), which `xmssTree` and
`xmssPk` share, stores the two halves of each of the `n` bytes at
`S + oMsg` (`x19 = S`), high first, to the bytes from `S + oDigits`
(`digitByte_ok`, one byte at a time), summing them in `x12`; then the three
digits of the checksum (`tail_ok`). So the `len` bytes there are the WOTS⁺
digits of the message (`digits_ok`, through `wotsDigits_eq`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Xmss

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase

/-! ## Bytes -/

theorem write1_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.write a 1 v) a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.lt_one_iff, ite_true, Nat.mul_zero]
  exact BitVec.extractLsb'_eq_self

theorem write1_other (m : Mem) {a x : Addr} (v : BitVec 8) (h : x ≠ a) : (m.write a 1 v) x = m x := by
  refine Mem.write_apply fun h' => h ?_
  have : (x - a).toNat = 0 := by omega
  have e : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  rw [← BitVec.sub_add_cancel x a, e]; simp

theorem at_ne (S : Addr) {a c : Nat} (ha : a < 65536) (hc : c < 65536) (h : a ≠ c) : at' S a ≠ at' S c :=
  Offset.add_ofNat_ne S (by omega) (by omega) h

theorem setw8 (v : Nat) : (BitVec.ofNat 64 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem shr_ofNat (v k : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v >>> k : BitVec 64) = BitVec.ofNat 64 (v / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv)]

theorem and15 (v : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v &&& (15 : BitVec 16).setWidth 64) = BitVec.ofNat 64 (v % 16) := by
  rw [show (15 : BitVec 16).setWidth 64 = BitVec.ofNat 64 (2 ^ 4 - 1) by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (show 2 ^ 4 - 1 < 2 ^ 64 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte64 (x : Byte) : (x.setWidth 64 : BitVec 64) = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## The bytes of the message -/

/-- Byte `b` of the message at `S + oMsg`. -/
def msgByte (m : Mem) (S : Addr) (b : Nat) : Nat := (m (at' S (Layout.oMsg + b))).toNat

/-- Digit `j` of the message's bytes: the high half of byte `j / 2` for an
even `j`, the low half for an odd one. -/
def nibD (m : Mem) (S : Addr) (j : Nat) : Nat :=
  if j % 2 = 0 then msgByte m S (j / 2) / 16 else msgByte m S (j / 2) % 16

/-- The sum of the digits of the first `b` bytes. -/
def dsum (m : Mem) (S : Addr) : Nat → Nat
  | 0 => 0
  | b + 1 => dsum m S b + (msgByte m S b / 16 + msgByte m S b % 16)

theorem dsum_le (m : Mem) (S : Addr) : ∀ b, dsum m S b ≤ 30 * b
  | 0 => Nat.le_refl _
  | b + 1 => by
    have := dsum_le m S b
    have := (m (at' S (Layout.oMsg + b))).isLt
    simp only [dsum, msgByte]; omega

/-- The registers a block of the digits writes. -/
abbrev DRegs (r : Reg) : Prop := r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

/-- After the digits of `b` bytes, from `s₀`. -/
structure DInv (s₀ : State) (S : Addr) (b : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = S
  x11 : s.gpr .x11 = (15 : BitVec 16).setWidth 64
  x12 : s.gpr .x12 = BitVec.ofNat 64 (dsum s₀.mem S b)
  other : ∀ r, DRegs r → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  v : s.v = s₀.v
  dig : ∀ j < 2 * b, s.mem (at' S (Layout.oDigits + j)) = BitVec.ofNat 8 (nibD s₀.mem S j)
  frame : Frame [⟨at' S Layout.oDigits, 2 * b⟩] s₀.mem s.mem

theorem dig_region (S : Addr) {b : Nat} (hb : b ≤ 32) {o : Nat} (ho : o < 65536)
    (h : o < Layout.oDigits ∨ Layout.oDigits + 2 * b ≤ o) :
    ∀ r ∈ [(⟨at' S Layout.oDigits, 2 * b⟩ : Region)], Region.Disjoint ⟨at' S o, 1⟩ r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact disj_scr S (by omega) (by omega) (by simp only [Layout.oDigits]; omega)

/-- The stores of byte `b` of the message: its halves to digits `2b` and `2b + 1`. -/
theorem digitByte_ok {s₀ : State} {S : Addr} {b : Nat} (hb : b < 32) {is : List Instr} {s : State}
    {Q : State → Prop} (hw : (⟨S, 65536⟩ : Region) ∈ s₀.wr) (hI : DInv s₀ S b s)
    (k : ∀ s', DInv s₀ S (b + 1) s' → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Xmss.digitByte b ++ is)) s Q := by
  have eD : Layout.oDigits = 1856 := rfl
  have eM : Layout.oMsg = 1984 := rfl
  have hws : (⟨S, 65536⟩ : Region) ∈ s.wr := by rw [hI.wr]; exact hw
  have hmb : s.mem (at' S (Layout.oMsg + b)) = s₀.mem (at' S (Layout.oMsg + b)) :=
    byte_frame hI.frame (dig_region S (by omega) (by omega) (.inr (by omega)))
  obtain ⟨x, hx⟩ : ∃ x, x = msgByte s₀.mem S b := ⟨_, rfl⟩
  have hx256 : x < 256 := by rw [hx]; exact (s₀.mem _).isLt
  simp only [Impl.SlhDsa.AArch64.Xmss.digitByte, List.cons_append, List.nil_append]
  refine wp_ldrb (a := at' S (Layout.oMsg + b)) (by omega) (by rw [hI.x19])
    (in_scr' hws (by omega)) fun s₁ u₁ => ?_
  have r1 : s₁.gpr .x9 = BitVec.ofNat 64 x := by rw [u₁.gpr, hmb, byte64, hx]; rfl
  refine wp_lsr (by decide) fun s₂ u₂ => wp_and fun s₃ u₃ => ?_
  have r2 : s₃.gpr .x10 = BitVec.ofNat 64 (x / 16) := by
    rw [u₃.other _ (by decide), u₂.gpr, r1, shr_ofNat _ _ (by omega)]
  have r3 : s₃.gpr .x9 = BitVec.ofNat 64 (x % 16) := by
    rw [u₃.gpr, u₂.other _ (by decide), r1, u₂.other _ (by decide), u₁.other _ (by decide), hI.x11,
      and15 _ (by omega)]
  have b3 : s₃.gpr .x19 = S := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.x19]
  have w3 : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr]
  refine wp_strb (a := at' S (Layout.oDigits + 2 * b)) (by omega) (by rw [b3])
    (in_scr (by rw [w3]; exact hw) (by omega)) fun s₄ u₄ => ?_
  refine wp_strb (a := at' S (Layout.oDigits + 2 * b + 1)) (by omega) (by rw [u₄.gpr, b3])
    (in_scr (by rw [u₄.wr, w3]; exact hw) (by omega)) fun s₅ u₅ => ?_
  refine wp_addr fun s₆ u₆ => wp_addr fun s₇ u₇ => k s₇ ?_
  have hm₇ : s₇.mem = (s.mem.write (at' S (Layout.oDigits + 2 * b)) 1 (BitVec.ofNat 8 (x / 16))).write
      (at' S (Layout.oDigits + 2 * b + 1)) 1 (BitVec.ofNat 8 (x % 16)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.gpr, r3, u₄.mem, r2, u₃.mem, u₂.mem, u₁.mem, setw8, setw8]
  have hg : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → s₇.gpr r = s.gpr r := fun r h9 h10 h12 => by
    rw [u₇.other _ h12, u₆.other _ h12, u₅.gpr, u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9]
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide), hI.x19],
    by rw [hg _ (by decide) (by decide) (by decide), hI.x11], ?_,
    fun r ⟨h9, h10, _, h12, _⟩ => by rw [hg r h9 h10 h12, hI.other r (by assumption)],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp],
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, w3], by rw [u₇.v, u₆.v, u₅.v, u₄.v, u₃.v, u₂.v, u₁.v, hI.v],
    fun j hj => ?_, ?_⟩
  · rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₄.gpr, r2, r3, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.x12, BitVec.add_assoc, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add]
    simp only [dsum, msgByte] at hx ⊢; rw [hx]
  · rw [hm₇]
    by_cases h1 : j = 2 * b + 1
    · subst h1; rw [← Nat.add_assoc, write1_self]; simp only [nibD]
      rw [ite_eq_right (by omega), show (2 * b + 1) / 2 = b by omega, ← hx]
    · rw [write1_other _ _ (at_ne S (by omega) (by omega) (by omega))]
      by_cases h0 : j = 2 * b
      · subst h0; rw [write1_self]; simp only [nibD]
        rw [ite_eq_left (by omega), show 2 * b / 2 = b by omega, ← hx]
      · rw [write1_other _ _ (at_ne S (by omega) (by omega) (by omega)), hI.dig j (by omega)]
  · rw [hm₇]
    have hc : ∀ i < 2, Region.Contains ⟨at' S Layout.oDigits, 2 * (b + 1)⟩ (at' S (Layout.oDigits + 2 * b + i)) 1 :=
      fun i hi => Offset.contains S (by omega) (by omega) (by omega)
    refine ((hI.frame.sub fun r hr => ?_).write (List.mem_singleton_self _) _ ?_).write
      (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · have := hc 0 (by decide); rwa [Nat.add_zero] at this
    · exact hc 1 (by decide)

/-- The stores of bytes `b` to `b + c - 1` of the message. -/
theorem bytes_ok {s₀ : State} {S : Addr} (n : Nat) (hn : n ≤ 32) (hw : (⟨S, 65536⟩ : Region) ∈ s₀.wr) :
    ∀ c b, b + c = n → ∀ {s : State} {is : List Instr} {Q : State → Prop}, DInv s₀ S b s →
      (∀ s', DInv s₀ S n s' → WP isa (.block is) s' Q) →
      WP isa (.block ((List.range' b c).flatMap Impl.SlhDsa.AArch64.Xmss.digitByte ++ is)) s Q
  | 0, b, hbc, s, is, Q, hI, k => by
    have : b = n := by omega
    subst this; exact k s hI
  | c + 1, b, hbc, s, is, Q, hI, k => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    exact digitByte_ok (by omega) hw hI fun s' hI' => bytes_ok n hn hw c (b + 1) (by omega) hI' k

theorem sub_ofNat' {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- After the digits and the checksum, from `s₀`. -/
structure DOut (s₀ : State) (S : Addr) (n : Nat) (s : State) : Prop where
  other : ∀ r, DRegs r → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  v : s.v = s₀.v
  dig : ∀ j < 2 * n, s.mem (at' S (Layout.oDigits + j)) = BitVec.ofNat 8 (nibD s₀.mem S j)
  csum : ∀ j < 3, s.mem (at' S (Layout.oDigits + 2 * n + j)) =
    BitVec.ofNat 8 ((Proof.SlhDsa.csumDigits (30 * n - dsum s₀.mem S n)).getD j 0)
  frame : Frame [⟨at' S Layout.oDigits, 2 * n + 3⟩] s₀.mem s.mem

/-- The tail of `Xmss.digits`: the checksum's three digits. -/
theorem tail_ok {s₀ : State} {S : Addr} {n : Nat} (hn : n ≤ 32) (hw : (⟨S, 65536⟩ : Region) ∈ s₀.wr)
    {s : State} {is : List Instr} {Q : State → Prop} (hI : DInv s₀ S n s)
    (k : ∀ s', DOut s₀ S n s' → WP isa (.block is) s' Q) :
    WP isa (.block (([.movz .x .x13 (BitVec.ofNat 16 (15 * 2 * n)) 0, .sub .x .x13 .x13 .x12,
      .lsr .x .x10 .x13 8, .logic .and .x .x10 .x10 .x11, .strb .x10 .x19 (Layout.oDigits + 2 * n),
      .lsr .x .x10 .x13 4, .logic .and .x .x10 .x10 .x11, .strb .x10 .x19 (Layout.oDigits + 2 * n + 1),
      .logic .and .x .x10 .x13 .x11, .strb .x10 .x19 (Layout.oDigits + 2 * n + 2)] : List Instr) ++ is)) s Q := by
  have eD : Layout.oDigits = 1856 := rfl
  have hws : (⟨S, 65536⟩ : Region) ∈ s.wr := by rw [hI.wr]; exact hw
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = 30 * n - dsum s₀.mem S n := ⟨_, rfl⟩
  have hd := dsum_le s₀.mem S n
  have hcs64 : cs < 2 ^ 64 := by omega
  simp only [List.cons_append, List.nil_append]
  refine wp_movz fun s₁ u₁ => wp_subr fun s₂ u₂ => ?_
  have r2 : s₂.gpr .x13 = BitVec.ofNat 64 cs := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x12, hcs, ← sub_ofNat' (by omega) (by omega)]
    congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have g2 : ∀ r, r ≠ .x13 → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other _ h, u₁.other _ h]
  refine wp_lsr (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => ?_
  have a4 : s₄.gpr .x10 = BitVec.ofNat 64 (cs / 2 ^ 8 % 16) := by
    rw [u₄.gpr, u₃.gpr, r2, u₃.other _ (by decide), g2 _ (by decide), hI.x11, shr_ofNat _ _ hcs64,
      and15 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hcs64)]
  refine wp_strb (a := at' S (Layout.oDigits + 2 * n)) (by omega)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), g2 _ (by decide), hI.x19])
    (in_scr (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hws) (by omega)) fun s₅ u₅ => ?_
  refine wp_lsr (by decide) fun s₆ u₆ => wp_and fun s₇ u₇ => ?_
  have g5 : ∀ r, r ≠ .x10 → s₅.gpr r = s.gpr r ∨ r = .x13 := fun r h => by
    by_cases h13 : r = .x13
    · exact .inr h13
    · left; rw [u₅.gpr, u₄.other _ h, u₃.other _ h, g2 _ h13]
  have x13₅ : s₅.gpr .x13 = BitVec.ofNat 64 cs := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), r2]
  have a7 : s₇.gpr .x10 = BitVec.ofNat 64 (cs / 2 ^ 4 % 16) := by
    rw [u₇.gpr, u₆.gpr, x13₅, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      g2 _ (by decide), hI.x11, shr_ofNat _ _ hcs64, and15 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hcs64)]
  have b7 : s₇.gpr .x19 = S := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      g2 _ (by decide), hI.x19]
  refine wp_strb (a := at' S (Layout.oDigits + 2 * n + 1)) (by omega) (by rw [b7])
    (in_scr (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hws) (by omega)) fun s₈ u₈ => ?_
  refine wp_and fun s₉ u₉ => ?_
  have a9 : s₉.gpr .x10 = BitVec.ofNat 64 (cs % 16) := by
    rw [u₉.gpr, u₈.gpr, u₇.other .x13 (by decide), u₆.other .x13 (by decide), x13₅, u₇.other .x11 (by decide),
      u₆.other .x11 (by decide), u₅.gpr, u₄.other .x11 (by decide), u₃.other .x11 (by decide), g2 .x11 (by decide),
      hI.x11, and15 _ hcs64]
  refine wp_strb (a := at' S (Layout.oDigits + 2 * n + 2)) (by omega)
    (by rw [u₉.other _ (by decide), u₈.gpr, b7])
    (in_scr (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hws) (by omega))
    fun s₁₀ u₁₀ => k s₁₀ ?_
  have hm : s₁₀.mem = ((s.mem.write (at' S (Layout.oDigits + 2 * n)) 1 (BitVec.ofNat 8 (cs / 2 ^ 8 % 16))).write
      (at' S (Layout.oDigits + 2 * n + 1)) 1 (BitVec.ofNat 8 (cs / 2 ^ 4 % 16))).write
      (at' S (Layout.oDigits + 2 * n + 2)) 1 (BitVec.ofNat 8 (cs % 16)) := by
    rw [u₁₀.mem, a9, u₉.mem, u₈.mem, a7, u₇.mem, u₆.mem, u₅.mem, a4, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      setw8, setw8, setw8]
  have hg : ∀ r, DRegs r → s₁₀.gpr r = s.gpr r := fun r ⟨h9, h10, h11, h12, h13⟩ => by
    rw [u₁₀.gpr, u₉.other _ h10, u₈.gpr, u₇.other _ h10, u₆.other _ h10, u₅.gpr, u₄.other _ h10,
      u₃.other _ h10, g2 _ h13]
  refine ⟨fun r hr => by rw [hg r hr, hI.other r hr],
    by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp],
    by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [u₁₀.v, u₉.v, u₈.v, u₇.v, u₆.v, u₅.v, u₄.v, u₃.v, u₂.v, u₁.v, hI.v], fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [hm, write1_other _ _ (at_ne S (by omega) (by omega) (by omega)),
      write1_other _ _ (at_ne S (by omega) (by omega) (by omega)),
      write1_other _ _ (at_ne S (by omega) (by omega) (by omega)), hI.dig j hj]
  · rw [hm, ← hcs]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · rw [write1_other _ _ (at_ne S (by omega) (by omega) (by omega)),
        write1_other _ _ (at_ne S (by omega) (by omega) (by omega)), Nat.add_zero, write1_self]; rfl
    · rw [write1_other _ _ (at_ne S (by omega) (by omega) (by omega)), write1_self]; rfl
    · rw [write1_self]; rfl
  · rw [hm]
    have hc : ∀ i < 3, Region.Contains ⟨at' S Layout.oDigits, 2 * n + 3⟩ (at' S (Layout.oDigits + 2 * n + i)) 1 :=
      fun i hi => Offset.contains S (by omega) (by omega) (by omega)
    refine (((hI.frame.sub fun r hr => ?_).write (List.mem_singleton_self _) _ ?_).write
      (List.mem_singleton_self _) _ (hc 1 (by decide))).write (List.mem_singleton_self _) _ (hc 2 (by decide))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · have := hc 0 (by decide); rwa [Nat.add_zero] at this

/-! ## The digits -/

theorem getD_app_l {l l' : List Nat} {i : Nat} (h : i < l.length) : (l ++ l').getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_r {l l' : List Nat} {i : Nat} (h : l.length ≤ i) :
    (l ++ l').getD i 0 = l'.getD (i - l.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem nibbles_length (X : List Byte) (n : Nat) : (Proof.SlhDsa.nibbles X n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Proof.SlhDsa.nibbles] at ih ⊢
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil]
    omega

theorem nibbles_snoc (X : List Byte) (n : Nat) :
    Proof.SlhDsa.nibbles X (n + 1) = Proof.SlhDsa.nibbles X n ++ [(X.getD n 0).toNat / 16, (X.getD n 0).toNat % 16] := by
  simp only [Proof.SlhDsa.nibbles]
  rw [List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Digit `c` of the nibbles. -/
theorem nibbles_getD (X : List Byte) {n c : Nat} (hc : c < 2 * n) :
    (Proof.SlhDsa.nibbles X n).getD c 0 =
      if c % 2 = 0 then (X.getD (c / 2) 0).toNat / 16 else (X.getD (c / 2) 0).toNat % 16 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [nibbles_snoc]
    by_cases h : c < 2 * n
    · rw [getD_app_l (by rw [nibbles_length]; exact h), ih h]
    · rw [getD_app_r (by rw [nibbles_length]; omega), nibbles_length]
      rcases (show c - 2 * n = 0 ∨ c - 2 * n = 1 by omega) with h2 | h2
      · rw [h2, ite_eq_left (by omega), show c / 2 = n by omega]; rfl
      · rw [h2, ite_eq_right (by omega), show c / 2 = n by omega]; rfl

/-- The checksum's sum over the nibbles of the message: `30n − dsum`. -/
theorem nibbles_csum (m : Mem) (S : Addr) {N : Nat} (hN : N ≤ 32) :
    ∀ n ≤ N, ((Proof.SlhDsa.nibbles (bytesAt m (at' S Layout.oMsg) N) n).map (fun mi => 15 - mi)).sum =
      30 * n - dsum m S n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nibbles_snoc, List.map_append, List.sum_append, ih (by omega), getD_bytesAt _ _ (by omega), at_add]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dsum]
    have := dsum_le m S n
    have := (m (at' S (Layout.oMsg + n))).isLt
    simp only [msgByte] at *
    omega

theorem len_eq {p : Params} (hz : Sz p) : p.len = 2 * p.n + 3 := hz.len

variable {p : Params}

/-- `Xmss.digits`: from the `n` bytes at `S + oMsg` (`x19 = S`), their WOTS⁺
digits to the `len` bytes at `S + oDigits`; only `x9` to `x13` change. -/
theorem digits_ok (hz : Sz p) {s : State} {S : Addr} {is : List Instr} {Q : State → Prop}
    (hS : s.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ i < p.len, digitAt s'.mem S i = (wotsDigits p (bytesAt s.mem (at' S Layout.oMsg) p.n)).getD i 0) →
      Frame [⟨at' S Layout.oDigits, p.len⟩] s.mem s'.mem →
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → s'.rd = s.rd → s'.wr = s.wr → s'.v = s.v → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Xmss.digits ⟨p.n, p.len⟩ ++ is)) s Q := by
  have hn32 := hz.n32
  have hl := hz.len
  simp only [Impl.SlhDsa.AArch64.Xmss.digits, List.cons_append, List.append_assoc, List.range_eq_range']
  refine wp_movz fun s₁ u₁ => wp_movz fun s₂ u₂ => ?_
  have h0 : DInv s S 0 s₂ := ⟨by rw [u₂.other _ (by decide), u₁.other _ (by decide), hS], u₂.gpr,
    by rw [u₂.other _ (by decide), u₁.gpr]; rfl,
    fun r ⟨_, _, h11, h12, _⟩ => by rw [u₂.other _ h11, u₁.other _ h12],
    by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.v, u₁.v],
    fun j hj => absurd hj (by omega), by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩
  refine bytes_ok p.n hn32 hw p.n 0 (by omega) h0 fun s₃ h₃ => ?_
  rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append,
    ← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append]
  refine tail_ok hn32 hw h₃ fun s' h' => k s' (fun i hi => ?_) (by rw [hl]; exact h'.frame)
    (fun r h9 h10 h11 h12 h13 => h'.other r ⟨h9, h10, h11, h12, h13⟩) h'.sp h'.rd h'.wr h'.v
  rw [Proof.SlhDsa.wotsDigits_eq p hz.lgw hz.nv]
  simp only [digitAt]
  by_cases h : i < 2 * p.n
  · rw [h'.dig i h, getD_app_l (by rw [nibbles_length]; exact h), nibbles_getD _ h,
      getD_bytesAt _ _ (by omega), at_add]
    have hlt : nibD s.mem S i < 256 := by
      have := (s.mem (at' S (Layout.oMsg + i / 2))).isLt
      simp only [nibD, msgByte]; split <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    simp only [nibD, msgByte]
  · rw [getD_app_r (by rw [nibbles_length]; omega), nibbles_length, nibbles_csum s.mem S hn32 p.n (Nat.le_refl _),
      show Layout.oDigits + i = Layout.oDigits + 2 * p.n + (i - 2 * p.n) by omega, h'.csum _ (by omega),
      BitVec.toNat_ofNat]
    have : (Proof.SlhDsa.csumDigits (30 * p.n - dsum s.mem S p.n)).getD (i - 2 * p.n) 0 < 16 := by
      simp only [Proof.SlhDsa.csumDigits]
      rcases (show i - 2 * p.n = 0 ∨ i - 2 * p.n = 1 ∨ i - 2 * p.n = 2 by omega) with e | e | e <;>
        rw [e] <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega
    omega

end VG.Proof.SlhDsa.AArch64.Xmss
