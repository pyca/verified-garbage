module

public import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: the recombination

* `xb_ok`: the base of `X`'s array `j`, from `s6` and `s11`;
* `exportM2_ok`: `m₂`'s `q_len` bytes, most significant first, from `Q`'s
  array 4 into `X`'s array 1.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Crt VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

theorem xb_cons (rd : Reg) (j : Nat) : xb rd (j + 1) = xb rd j ++ ([.add rd rd .s11] : List Instr) := by
  simp only [xb, List.replicate_succ', List.cons_append]

/-- `xb rd j`: the base of `X`'s array `j`, `X` at `s6` and its arrays' size
in `s11`. -/
theorem xb_ok {t : State} {BX : Addr} {w : Nat} {rd : Reg} (hrd : rd ≠ .s11)
    (h6 : t.gpr .s6 = BX) (h11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (xb rd j)) t fun t' =>
      (t'.gpr rd = off BX (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    simp only [xb, List.replicate_zero]
    apply WP.of_runBlock
    refine ⟨t.write rd (off BX (slot w 0)), ?_, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
    rw [runBlock_cons, exec_addi_nat (show hdrBytes < 2048 by decide), runStep_some, runBlock_nil, h6]
    simp [off, slot]
  | j + 1 => by
    rw [xb_cons, WP.block_append_iff]
    refine WP.mono (xb_ok hrd h6 h11 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr (r := .s11) (by simpa using Ne.symm hrd)).trans h11]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega]

/-- `exportM2`: `m₂`'s `L = q_len` bytes (the header's word `oQLen`) from
`Q`'s array 4 (at `BQ`), most significant first, into `X`'s array 1. -/
theorem exportM2_ok {s : State} {BQ BX : Addr} {ZQ ZX wQ wX L : Nat} (hq : Scr s BQ ZQ) (hx : Scr s BX ZX)
    (h7 : s.gpr .a7 = off BQ (slot wQ 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (wQ + 2)))
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hL : word s.mem BX oQLen = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLq : L ≤ 8 * wQ) (hLx : L ≤ 8 * wX) (hZQ : slot wQ 24 ≤ ZQ) (hZX : slot wX 8 ≤ ZX)
    (hsep : ∀ x, ofs BX x < ZX → ZQ ≤ ofs BQ x) :
    WP isa exportM2 s fun t =>
      ((∀ i < L, t.mem (off BX (slot wX 1 + i)) = s.mem (off BQ (slot wQ 4 + (L - 1 - i)))) ∧
        Outside BX (slot wX 1) L s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnq := hq.nowrap
  have hnx := hx.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have e4 := e wQ 4; have e8 := e wQ 24; have x1 := e wX 1; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  unfold exportM2
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) h7 h5 4) fun s₁ ⟨⟨a4, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4, .t5] (Q := fun s₂ => s₂.gpr .t4 = off BQ (slot wQ 4 + (L - 1)) ∧
    s₂.gpr .t5 = BitVec.ofNat 64 L ∧ s₂.mem = s₁.mem) ?_ (by rfl) (by rfl)) fun s₂ ⟨⟨b4, b5, m2⟩, k2⟩ => ?_
  · have hL' : s₁.mem.readW (off BX 56) 64 = BitVec.ofNat 64 L := by rw [m1]; exact hL
    brun [a4, (k1.gpr (r := .s6) (by decide)).trans h6, oQLen, (hx.congr k1.2.2).ld (show 56 + 8 ≤ ZX by omega_arith),
      (hx.congr k1.2.2).al8 (show 56 + 8 ≤ ZX by omega_arith) (by decide), hL', off_add, BitVec.add_zero]
    rw [off_sub _ (by omega_arith)]; congr 2; omega_arith
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k1.trans k2).gpr (by decide) |>.trans h6)
    ((k1.trans k2).gpr (by decide) |>.trans h11) 1) fun s₃ ⟨⟨b3, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have b4' : s₃.gpr .t4 = off BQ (slot wQ 4 + (L - 1)) := (k3.gpr (by decide)).trans b4
  have b5' : s₃.gpr .t5 = BitVec.ofNat 64 L := (k3.gpr (by decide)).trans b5
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t4 = off BQ (slot wQ 4 + (L - 1) - j) ∧ t.gpr .t3 = off BX (slot wX 1 + j) ∧
      Outside BX (slot wX 1) j s.mem t.mem ∧
      (∀ i < j, t.mem (off BX (slot wX 1 + i)) = s.mem (off BQ (slot wQ 4 + (L - 1 - i)))) ∧
      Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .b .s0 .t4 0, .store .b .s0 .t3 0, .addi .t3 .t3 1,
      .addi .t4 .t4 (-1)] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := L) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t4, t3, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b4']; rfl, by rw [b3]; rfl, by rw [m3, m2, m1]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega_arith), k13.mono (by decide)⟩ b5') fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hrd : InRegions (t.rd ++ t.wr) (off BQ (slot wQ 4 + (L - 1) - j)) 1 := by
    rw [tk.2.1, tk.2.2]; exact hq.ld (show slot wQ 4 + (L - 1) - j + 1 ≤ ZQ by omega_arith)
  have hst : WP isa (.block [.load .b .s0 .t4 0, .store .b .s0 .t3 0, .addi .t3 .t3 1,
      .addi .t4 .t4 (-1), .addi .t5 .t5 (-1)]) t fun t' => t' = (((({ (t.write .s0
        ((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64)) with
        mem := t.mem.write (off BX (slot wX 1 + j)) 1
          (((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64).setWidth 8) } :
          State).write .t3 (off BX (slot wX 1 + j + 1))).write .t4
            (off BQ (slot wQ 4 + (L - 1) - j) - BitVec.ofNat 64 1)).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [t4, t3, hrd, (hx.congr tk.2.2).st (d := slot wX 1 + j) (n := 1) (by omega_arith), add_ofNat_zero]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem BX (d := slot wX 1 + j)
    (((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64).setWidth 8) (by omega_arith)
  have harr : t.mem (off BQ (slot wQ 4 + (L - 1) - j)) = s.mem (off BQ (slot wQ 4 + (L - 1) - j)) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    have := hsep (off BQ (slot wQ 4 + (L - 1) - j)) (by omega_arith)
    rw [show ofs BQ (off BQ (slot wQ 4 + (L - 1) - j)) = slot wQ 4 + (L - 1) - j from
      ofs_off0 BQ (by omega_arith)] at this
    omega_arith
  refine ⟨⟨?_, by gsimp; rw [Nat.add_assoc], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; rw [off_sub _ (by omega_arith), show slot wQ 4 + (L - 1) - j - 1 = slot wQ 4 + (L - 1) - (j + 1) by omega_arith]
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 BX (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self, show slot wQ 4 + (L - 1 - i) = slot wQ 4 + (L - 1) - i by omega_arith, ← harr, read_one']
  · exact Keep.trans' tk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-! ## `recombineP` -/

/-- The borrow of `T = A - B mod 2^N` and `P` added back under it: `(A + P -
B) mod P`. -/
theorem subAdd_val {A Bv P T T' N c : Nat} (hA : A < P) (hB : Bv < P) (hP : P < 2 ^ N) (hc : c ≤ 1)
    (hT : T < 2 ^ N) (h : T + Bv = A + 2 ^ N * c) (h' : T' = (T + (if 0 < c then P else 0)) % 2 ^ N) :
    T' = (A + P - Bv) % P := by
  rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
  · simp only [Nat.lt_irrefl, ite_false, Nat.add_zero] at h'
    rw [Nat.mul_zero, Nat.add_zero] at h
    rw [h', Nat.mod_eq_of_lt hT, show A + P - Bv = (A - Bv) + P by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · simp only [Nat.zero_lt_one, ite_true] at h'
    rw [Nat.mul_one] at h
    rw [h', show T + P = (A + P - Bv) + 2 ^ N by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]

/-- Two Montgomery products, the second by `R² mod P`: `a q mod P`. -/
theorem mont_chain {P R a q x5 x4 : Nat} (hR : Nat.Coprime R P) (h5 : x5 * R % P = a * q % P)
    (h4 : x4 * R % P = x5 * (R * R % P) % P) (h4P : x4 < P) : x4 = a * q % P := by
  have e : x4 * R % P = a * q * R % P := by
    rw [h4, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, h5, Nat.mod_mul_mod]
  rw [← Nat.mod_eq_of_lt h4P]
  exact VG.Proof.Bignum.mont_cancel hR e

/-- The registers `recSub` writes. -/
def subRegs : List Reg := [.a0, .a5, .a6, .a7, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `recombineP`'s middle: `(m₁ + p - r) mod p` into array 3, from `m₁` in
array 4 and `r` in array 1, both below `p` (array 0), changing only arrays 3
and 4 (above `m₁`). -/
theorem recSub_ok {s : State} {B : Addr} {Z w Pv m1 r : Nat} (hs : Scr s B Z) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (hra : s.gpr .ra = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hP : wordsVal s.mem B (slot w 0) w = Pv) (hr : wordsVal s.mem B (slot w 1) w = r)
    (hm1 : wordsVal s.mem B (slot w 4) w = m1) (hrP : r < Pv) (hm1P : m1 < Pv) :
    WP isa (.seq (.block (base .t3 4 ++ ([.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0,
        .store .d .s0 .t3 0] : List Instr) ++ base .a5 4 ++ base .a6 3 ++ base .a7 1))
      (.seq subMod64 (.seq (.block (([.addi .a7 .ra 0] : List Instr) ++ base .t3 3 ++ base .t4 0))
        ModArith.addMask64))) s fun t =>
      (wordsVal t.mem B (slot w 3) w = (m1 + Pv - r) % Pv ∧ Arrays B w [3, 4] s.mem t.mem ∧
        t.gpr .a7 = off B (slot w 0)) ∧ Keep subRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 4) fun s₁ ⟨⟨a3, m1'⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t3, .s0] (Q := fun s₂ => s₂.gpr .t3 = off B (slot w 4 + 8 * w) ∧
      s₂.mem = s₁.mem.writeW (off B (slot w 4 + 8 * w)) (0 : BitVec 64)) ?_ (by rfl) (by rfl)) fun s₂ ⟨⟨b3, m2⟩, k2⟩ => ?_
  · have q : off B (slot w 4 + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w 4 + 8 * w) := by
      rw [off_sub _ (by omega_arith)]; congr 2
    brun [a3, (k1.gpr (r := .s5) (by decide)).trans h5, off_add, q,
      (hs.congr k1.2.2).st (show slot w 4 + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k1.2.2).al8 (show slot w 4 + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith), BitVec.add_zero, fin64_exec_li_zero]
  have k12 := k1.trans k2
  have g7 : ∀ {t : State} {rs : List Reg}, Keep rs s t → Reg.a7 ∉ rs → t.gpr .a7 = off B (slot w 0) :=
    fun k h => (k.gpr h).trans h7
  have g5 : ∀ {t : State} {rs : List Reg}, Keep rs s t → Reg.s5 ∉ rs → t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) :=
    fun k h => (k.gpr h).trans h5
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) (g7 k12 (by decide)) (g5 k12 (by decide)) 4)
    fun s₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) (g7 k13 (by decide)) (g5 k13 (by decide)) 3)
    fun s₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (Pub.base_ok (rd := .a7) (by decide) (g7 k14 (by decide)) (g5 k14 (by decide)) 1)
    fun s₅ ⟨⟨a7, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have m15 : s₅.mem = s.mem.writeW (off B (slot w 4 + 8 * w)) (0 : BitVec 64) := by rw [m5, m4, m3, m2, m1']
  have hwo : Mont.Outside B (slot w 4 + 8 * w) 8 s.mem s₅.mem := by
    rw [m15]; exact writeW_outside s.mem B (d := slot w 4 + 8 * w) (0 : BitVec 64) (by omega_arith)
  have a5' : s₅.gpr .a5 = off B (slot w 4) := ((k4.trans k5).gpr (by decide)).trans a5
  have a6' : s₅.gpr .a6 = off B (slot w 3) := (k5.gpr (by decide)).trans a6
  have t0' : s₅.gpr .t0 = BitVec.ofNat 64 w := (k15.gpr (by decide)).trans ht0
  refine WP.seq (WP.mono (subMod64_ok (dA := slot w 4) (dT := slot w 3) (dM := slot w 1) (hs.congr k15.2.2)
    a5' a6' a7 t0' hw hw' (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (Or.inl (by omega_arith)) (Or.inr (by omega_arith))) fun s₆ ⟨⟨c, hc, hsum, h4⟩, o6, k6⟩ => ?_)
  have k16 := k15.trans k6
  have wtop : Mont.word s₅.mem B (slot w 4 + 8 * w) = 0 := by rw [m15]; exact word_writeW_self _ _ _ _
  have vA : wordsVal s₅.mem B (slot w 4) w = m1 := by
    rw [Mont.Outside.wordsVal hwo (Or.inl (by omega_arith)) (by omega_arith), hm1]
  have vM : wordsVal s₅.mem B (slot w 1) w = r := by
    rw [Mont.Outside.wordsVal hwo (Or.inl (by omega_arith)) (by omega_arith), hr]
  rw [vA, vM] at hsum
  rw [wtop] at h4
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7] (Q := fun s₇ => s₇.gpr .a7 = off B (slot w 0) ∧ s₇.mem = s₆.mem) ?_
    (by rfl) (by rfl)) fun s₇ ⟨⟨b7, m7⟩, k7⟩ => ?_
  · brun [(k16.gpr (r := .ra) (by decide)).trans hra, add_ofNat_zero]
  have k17 := k16.trans k7
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) b7 (g5 k17 (by decide)) 3) fun s₈ ⟨⟨c3, m8⟩, k8⟩ => ?_
  have k18 := k17.trans k8
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k8.gpr (by decide)).trans b7) (g5 k18 (by decide)) 0)
    fun s₉ ⟨⟨c4, m9⟩, k9⟩ => ?_
  have k19 := k18.trans k9
  have s4' : s₉.gpr .s4 = if decide (0 < c) then BitVec.allOnes 64 else 0 := by
    rw [((k7.trans k8).trans k9).gpr (by decide), h4]
    simp only [decide_eq_true_eq, show (0 : BitVec 64).toNat = 0 from rfl]
  refine WP.mono (ModArith.addMask64_ok (dT := slot w 3) (dM := slot w 0) (hs.congr k19.2.2)
    ((k9.gpr (by decide)).trans c3) c4 ((k19.gpr (by decide)).trans ht0) s4' (by omega_arith) (by omega_arith) hw hw'
    (by omega_arith) (by omega_arith) (Or.inr (by omega_arith))) fun t ⟨hv, o10, k10⟩ => ?_
  have m69 : s₉.mem = s₆.mem := by rw [m9, m8, m7]
  rw [m69] at hv
  have vP : wordsVal s₆.mem B (slot w 0) w = Pv := by
    rw [Mont.Outside.wordsVal o6 (Or.inl (by omega_arith)) (by omega_arith),
      Mont.Outside.wordsVal hwo (Or.inl (by omega_arith)) (by omega_arith), hP]
  rw [vP] at hv
  refine ⟨⟨?_, ?_, (k10.gpr (by decide)).trans ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans b7))⟩,
    (k19.trans k10).mono (by decide)⟩
  · refine subAdd_val (N := 64 * w) (c := c) (T := wordsVal s₆.mem B (slot w 3) w) hm1P hrP
      (hP ▸ wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _) hsum ?_
    rw [hv]; simp only [decide_eq_true_eq]
  · rw [m69] at o10
    exact ((Arrays.of_outside (j := 4) (by simp) hwo (by omega_arith) (by omega_arith)).trans
      (Arrays.of_outside (j := 3) (by simp) o6 (Nat.le_refl _) (by omega_arith))).trans
      (Arrays.of_outside (j := 3) (by simp) o10 (Nat.le_refl _) (by omega_arith))

/-- Two numbers of `k` words that agree word by word. -/
theorem wordsVal_of_words {m m' : Mem} {B B' : Addr} : ∀ {d d' k : Nat},
    (∀ i < k, Mont.word m B (d + 8 * i) = Mont.word m' B' (d' + 8 * i)) → wordsVal m B d k = wordsVal m' B' d' k
  | _, _, 0, _ => rfl
  | d, d', k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    simp only [wordsVal]
    rw [h0, wordsVal_of_words (d := d + 8) (d' := d' + 8) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega, show d' + 8 * (i + 1) = d' + 8 + 8 * i by omega] at this]

/-- The registers `recMont` writes. -/
def recMRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `recombineP`'s end: `qInv` (`w` words of `X`'s array 7) into array 6,
then `a qInv R⁻¹ mod p` into array 5 and `a qInv mod p` into array 4, from
`a` in array 3 and `R² mod p` in array 7. -/
theorem recMont_ok {s : State} {B BX : Addr} {Z ZX w wX Pv a QI : Nat} (hs : Scr s B Z) (hx : Scr s BX ZX)
    (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x) (hZ : slot w 8 ≤ Z) (hZX : slot wX 8 ≤ ZX) (hwX : w ≤ wX)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hP : wordsVal s.mem B (slot w 0) w = Pv) (hodd : Pv % 2 = 1)
    (ha : wordsVal s.mem B (slot w 3) w = a)
    (hRR : wordsVal s.mem B (slot w 7) w = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv)
    (hQ : wordsVal s.mem BX (slot wX 7) w = QI) (hQP : QI < Pv) :
    WP isa (.seq (.block (base .t3 6 ++ xb .t4 7)) (.seq copyN (.seq (montOp 5 3 6) (montOp 4 5 7)))) s
      fun t => (wordsVal t.mem B (slot w 4) w = a * QI % Pv ∧ Arrays B w [2, 3, 4, 5, 6] s.mem t.mem) ∧
        Keep recMRegs s t := by
  have hnw := hs.nowrap
  have hnx := hx.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have e0 := e w 0; have e3 := e w 3; have e6 := e w 6; have e7 := e w 7; have e8 := e w 8
  have x7 := e wX 7; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  have hfit : ∀ j < 8, slot w j + 8 * w ≤ 2 ^ 64 := fun j hj => by
    have := slot_le (w := w) hj; omega_arith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 6) fun s₁ ⟨⟨b3, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h6) ((k1.gpr (by decide)).trans h11) 7)
    fun s₂ ⟨⟨b4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copyWords_ok (dS := slot wX 7) (dD := slot w 6) (hx.congr k12.2.2) (hs.congr k12.2.2)
    b4 ((k2.gpr (by decide)).trans b3) ((k12.gpr (by decide)).trans ht0) (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) hsep) fun s₃ ⟨⟨_, hc, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have m02 : s₂.mem = s.mem := by rw [m2, m1]
  rw [m02] at hc o3
  have r3 : Arrays B w [6] s.mem s₃.mem := Arrays.of_outside (j := 6) (by simp) o3 (Nat.le_refl _) (by omega_arith)
  have q6 : wordsVal s₃.mem B (slot w 6) w = QI := (wordsVal_of_words hc).trans hQ
  have p3 : wordsVal s₃.mem B (slot w 0) w = Pv :=
    (Pub.arrays_V r3 (j := 0) (by decide) (hfit 0 (by decide))).trans hP
  have a3 : wordsVal s₃.mem B (slot w 3) w = a :=
    (Pub.arrays_V r3 (j := 3) (by decide) (hfit 3 (by decide))).trans ha
  have rr3 : wordsVal s₃.mem B (slot w 7) w = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv :=
    (Pub.arrays_V r3 (j := 7) (by decide) (hfit 7 (by decide))).trans hRR
  have w03 : Mont.word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    r3.word0_of_not_mem (by decide) (by decide) (by omega_arith) (by omega_arith)
  have hP0 : 0 < Pv := by omega_arith
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 5) (a := 3) (b := 6) (hs.congr k13.2.2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans h5) ((k13.gpr (by decide)).trans ht0)
    (by rw [show word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) from w03, k13.gpr (by decide)]; exact hinv) (by rw [q6, p3]; exact hQP))
    fun s₄ ⟨⟨x5P, x5R, r4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  rw [p3, a3, q6] at x5R
  rw [p3] at x5P
  have p4 : wordsVal s₄.mem B (slot w 0) w = Pv :=
    (Pub.arrays_V r4 (j := 0) (by decide) (hfit 0 (by decide))).trans p3
  have rr4 : wordsVal s₄.mem B (slot w 7) w = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv :=
    (Pub.arrays_V r4 (j := 7) (by decide) (hfit 7 (by decide))).trans rr3
  have w04 : Mont.word s₄.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    (r4.word0_of_not_mem (by decide) (by decide) (by omega_arith) (by omega_arith)).trans w03
  refine WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hs.congr k14.2.2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k14.gpr (by decide)).trans h7)
    ((k14.gpr (by decide)).trans h5) ((k14.gpr (by decide)).trans ht0)
    (by rw [show word s₄.mem B (slot w 0) = Mont.word s.mem B (slot w 0) from w04, k14.gpr (by decide)]; exact hinv) (by rw [rr4, p4]; exact Nat.mod_lt _ hP0))
    fun t ⟨⟨x4P, x4R, r5⟩, k5⟩ => ⟨⟨?_, ?_⟩, (k14.trans k5).mono (by decide)⟩
  · rw [p4, rr4] at x4R
    rw [p4] at x4P
    exact mont_chain (VG.Proof.Bignum.coprime_pow2 hodd _) x5R x4R x4P
  · exact (r3.mono (by decide)).trans ((r4.mono (by decide)).trans (r5.mono (by decide)))

end VG.Proof.Bignum.RISCV64.Crt
