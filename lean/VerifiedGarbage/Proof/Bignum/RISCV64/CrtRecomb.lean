module

public import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtR2
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
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

/-- `copyWords` within one working space, `w` words from `dS` (`t4`) to `dD`
(`t3`) apart from them, with `w` in `t0`. -/
theorem copySame_ok {s : State} {B : Addr} {Z dS dD w : Nat} (hs : Scr s B Z)
    (h4 : s.gpr .t4 = off B dS) (h3 : s.gpr .t3 = off B dD) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0) (hS : dS + 8 * w ≤ Z)
    (hD : dD + 8 * w ≤ Z) (hSD : dS + 8 * w ≤ dD ∨ dD + 8 * w ≤ dS) :
    WP isa Precompute.copyWords s fun t =>
      ((∀ i < w, Mont.word t.mem B (dD + 8 * i) = Mont.word s.mem B (dS + 8 * i)) ∧
        Mont.Outside B dD (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  unfold Precompute.copyWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h0, add_ofNat_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i5, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dD + 8 * i) ∧ t.gpr .t4 = off B (dS + 8 * i) ∧ Mont.Outside B dD (8 * i) s.mem t.mem ∧
      (∀ k < i, Mont.word t.mem B (dD + 8 * k) = Mont.word s.mem B (dS + 8 * k)) ∧ Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith)
      (by omega_arith) Inv (fun i hi t ⟨j3, j4, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr (r := .t3) (by decide), h3]; rfl, by rw [k₁.gpr (r := .t4) (by decide), h4]; rfl,
      by rw [← im]; exact Mont.Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), k₁.mono (by decide)⟩ i5)
    fun t ⟨_, _, tout, tc, tk⟩ => ⟨⟨fun k hk => tc k hk, tout⟩, tk⟩
  have hsrc : Mont.word t.mem B (dS + 8 * i) = Mont.word s.mem B (dS + 8 * i) :=
    Mont.Outside.word jout (by omega_arith) (by omega_arith)
  have hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
      .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ (t.write .s0 (Mont.word t.mem B (dS + 8 * i))) with
        mem := t.mem.writeW (off B (dD + 8 * i)) (Mont.word t.mem B (dS + 8 * i)) } :
        State).write .t3 (off B (dD + 8 * i + 8))).write .t4
          (off B (dS + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
    brun [j3, j4, (hs.congr jk.2.2).ld (show dS + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).st (show dD + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show dS + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      (hs.congr jk.2.2).al8 (show dD + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := dD + 8 * i) (Mont.word t.mem B (dS + 8 * i)) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega_arith],
    by gsimp; rw [show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (Mont.Outside.mono jout (Nat.le_refl _) (by omega_arith)).trans
      (Mont.Outside.mono hw (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [Mont.Outside.word hw (by omega_arith) (by omega_arith)]; exact jc k hk
    · rw [Mont.word_writeW_self, hsrc]
  · exact Keep.trans' jk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

theorem bytesAt_congr {m m' : Mem} {D : Addr} {L : Nat} (h : ∀ i < L, m' (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i)) :
    Spec.Rsa.bytesAt m' D L = Spec.Rsa.bytesAt m D L := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `a; b; c; d` and then `e`. -/
theorem seq4_then {a b c d e : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (k : ∀ t, P t → WP isa e t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q := by
  rw [WP.seq_iff] at h ⊢; refine WP.mono h fun t₁ h₁ => ?_
  rw [WP.seq_iff] at h₁ ⊢; refine WP.mono h₁ fun t₂ h₂ => ?_
  rw [WP.seq_iff] at h₂ ⊢; refine WP.mono h₂ fun t₃ h₃ => ?_
  exact WP.seq (WP.mono h₃ k)

theorem word0_odd {m : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) (h : wordsVal m B d w % 2 = 1) :
    (Mont.word m B d).toNat % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [wordsVal] at h
  rwa [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left] at h

/-- The registers `recombineP` writes. -/
def recPRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s7, .s8, .s9,
    .s10]

/-- `recombineP`, in `p`'s working space (`B`, of 24 arrays, `p` odd in
array 0 and `m₁ < p` in array 4), with `X` at `s6` (`BX`) apart from it,
`m₂`'s `q_len` bytes in `X`'s array 1 and `qInv < p` in its array 7: `h =
(m₁ - m₂ mod p) qInv mod p` in array 4, changing only arrays 1–23. -/
theorem recombineP_ok {s : State} {B BX : Addr} {Z ZX w wX L Pv m1 QI : Nat}
    (hs : Scr s B Z) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (hZ : slot w 24 ≤ Z) (hZX : slot wX 8 ≤ ZX) (hwX : w ≤ wX) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (hra : s.gpr .ra = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hL : Mont.word s.mem BX oQLen = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLx : L ≤ 8 * wX)
    (hP : wordsVal s.mem B (slot w 0) w = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hm1 : wordsVal s.mem B (slot w 4) w = m1) (hm1P : m1 < Pv)
    (hQ : wordsVal s.mem BX (slot wX 7) w = QI) (hQP : QI < Pv) :
    WP isa recombineP s fun t =>
      (wordsVal t.mem B (slot w 4) w =
          (m1 + Pv - Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off BX (slot wX 1)) L) % Pv) % Pv * QI % Pv ∧
        Win.WinO B w s.mem t.mem ∧ t.gpr .a7 = off B (slot w 0)) ∧ Keep recPRegs s t := by
  have hnw := hs.nowrap
  have hnx := hx.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have e0 := e w 0; have e1 := e w 1; have e4 := e w 4; have e7 := e w 7; have e8 := e w 8
  have e24 := e w 24
  have x1 := e wX 1; have x7 := e wX 7; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  -- What the arrays 1–23 of `P` leave alone.
  have xo : ∀ {m m' : Mem}, Win.WinO B w m m' → ∀ x, ofs BX x < ZX → m' x = m x := fun o x hx' =>
    o x (Or.inr (by have := hsep x hx'; omega_arith))
  have xw : ∀ {m m' : Mem}, Win.WinO B w m m' → wordsVal m' BX (slot wX 7) w = wordsVal m BX (slot wX 7) w :=
    fun o => wordsVal_of_words fun i hi => Mem.readW_congr fun j hj => xo o _ (by
      rw [ofs_off BX (d := slot wX 7 + 8 * i) (i := j) (by omega_arith)]; omega_arith)
  have xb' : ∀ {m m' : Mem}, Win.WinO B w m m' →
      Spec.Rsa.bytesAt m' (off BX (slot wX 1)) L = Spec.Rsa.bytesAt m (off BX (slot wX 1)) L :=
    fun o => bytesAt_congr fun i hi => xo o _ (by
      rw [ofs_off BX (d := slot wX 1) (i := i) (by omega_arith)]; omega_arith)
  unfold recombineP
  -- `s10 := q_len`.
  refine WP.seq (WP.mono (WP.keep [.s10] (Q := fun s₁ => s₁.gpr .s10 = BitVec.ofNat 64 L ∧ s₁.mem = s.mem) ?_
    (by rfl) (by rfl)) fun s₁ ⟨⟨c10, m1'⟩, k1⟩ => ?_)
  · have hL' : s.mem.readW (off BX 56) 64 = BitVec.ofNat 64 L := hL
    brun [h6, oQLen, hx.ld (show 56 + 8 ≤ ZX by omega_arith), hx.al8 (show 56 + 8 ≤ ZX by omega_arith) (by decide),
      hL']
  -- `t1 := -p⁻¹ mod 2⁶⁴`; the bases of arrays 1–3.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (minv_ok (d := slot w 0) (hs.congr k1.2.2) ((k1.gpr (by decide)).trans h7) (by omega_arith)
    (by omega_arith) (by rw [m1']; exact word0_odd (by omega_arith) (hP ▸ hodd))) fun s₂ ⟨⟨hinv, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) 1) fun s₃ ⟨⟨a2, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans h5) 2) fun s₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k14.gpr (by decide)).trans h7)
    ((k14.gpr (by decide)).trans h5) 3) fun s₅ ⟨⟨a6, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have m05 : s₅.mem = s.mem := by rw [m5, m4, m3, m2, m1']
  have c5 : Win.WCtx s₅ B Z w Pv := ⟨hs.congr k15.2.2, hw2, hw', hZ, (k15.gpr (by decide)).trans h7,
    (k15.gpr (by decide)).trans h5, (k15.gpr (by decide)).trans ht0,
    by rw [m05, ((k3.trans k4).trans k5).gpr (by decide)]; rw [m1'] at hinv; exact hinv, by rw [m05]; exact hP⟩
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (Win.r2Prime_ok (tmp := 5) c5 ((k4.trans k5).gpr (by decide) |>.trans a2)
    ((k5.gpr (by decide)).trans a5) a6 (by decide) (by decide) hP2 hodd)
    fun s₆ ⟨⟨c6, r6, f6, o6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  have hfit : ∀ j < 24, slot w j + 8 * w ≤ 2 ^ 64 := fun j hj => by
    have := Win.slot_lt (w := w) hj; omega_arith
  have m4₆ : wordsVal s₆.mem B (slot w 4) w = m1 := by
    rw [← hm1, ← m05]; exact f6 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  -- `R² mod p` into array 7.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c6.a7 c6.s5 7) fun s₇ ⟨⟨b3, m7⟩, k7⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k7.gpr (by decide)).trans c6.a7)
    ((k7.gpr (by decide)).trans c6.s5) 1) fun s₈ ⟨⟨b4, m8⟩, k8⟩ => ?_
  have k78 := k7.trans k8
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 1) (dD := slot w 7) (c6.scr.congr k78.2.2) b4
    ((k8.gpr (by decide)).trans b3) ((k78.gpr (by decide)).trans c6.t0) (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))) fun s₉ ⟨⟨hc9, o9⟩, k9⟩ => ?_)
  have m68 : s₈.mem = s₆.mem := by rw [m8, m7]
  rw [m68] at hc9 o9
  have w9 : Win.WinO B w s₆.mem s₉.mem := Mont.Outside.mono o9 (by omega_arith) (by omega_arith)
  have k69 := k78.trans k9
  have c9 : Win.WCtx s₉ B Z w Pv := c6.of k69 (by decide) w9
  have v9 : ∀ j < 24, (j = 0 ∨ j = 4) → wordsVal s₉.mem B (slot w j) w = wordsVal s₆.mem B (slot w j) w :=
    fun j hj hj' => Mont.Outside.wordsVal o9 (by
      have := Win.slot_lt (w := w) (show 4 < 7 by decide)
      rcases hj' with rfl | rfl <;> omega_arith) (hfit j hj)
  have rr9 : wordsVal s₉.mem B (slot w 7) w = 2 ^ (128 * w) % Pv := (wordsVal_of_words hc9).trans r6
  -- `m₂ mod p` into array 1.
  refine WP.seq (WP.mono (xb_ok (rd := .s9) (by decide) ((k16.trans k69).gpr (by decide) |>.trans h6)
    ((k16.trans k69).gpr (by decide) |>.trans h11) 1) fun s₁₀ ⟨⟨b9, m10⟩, k10⟩ => ?_)
  have k110 := (k16.trans k69).trans k10
  have c10' : Win.WCtx s₁₀ B Z w Pv := c9.regs k10 (by decide) m10
  have n10 : wordsVal s₁₀.mem B (slot w 0) w = Pv := c10'.n
  have k1to10 := (((((k2.trans k3).trans k4).trans k5).trans k6).trans k69).trans k10
  refine WP.seq (WP.mono (ModArith.reduce64_ok (D := off BX (slot wX 1)) (L := L) c10'.scr (by omega_arith) hw'
    (by omega_arith) c10'.a7 c10'.s5 c10'.t0 (by rw [n10]; omega_arith) (by rw [b9]; exact (BitVec.add_zero _).symm)
    ((k1to10.gpr (by decide)).trans c10) hL1 (by omega_arith)
    (fun i hi => by
      rw [k110.2.1, k110.2.2, show off (off BX (slot wX 1)) i = off BX (slot wX 1 + i) from off_add _ _ _]
      exact hx.ld (by omega_arith))
    (fun i hi x hxZ hxe => by
      have := hsep x (by
        rw [← hxe]
        show ofs BX (off BX (slot wX 1) + BitVec.ofNat 64 i) < ZX
        rw [ofs_off BX (d := slot wX 1) (i := i) (by omega_arith)]; omega_arith)
      omega_arith)) fun s₁₁ ⟨⟨r11, o11⟩, k11⟩ => ?_)
  have k111 := k110.trans k11
  rw [n10] at r11
  have w11 : Win.WinO B w s₁₀.mem s₁₁.mem := Mont.Outside.mono o11 (Nat.le_refl _) (by omega_arith)
  have c11 : Win.WCtx s₁₁ B Z w Pv := c10'.of k11 (by decide) w11
  have w911 : Win.WinO B w s₉.mem s₁₁.mem := by rw [← m10]; exact w11
  have w06 : Win.WinO B w s.mem s₆.mem := by rw [← m05]; exact o6
  have ws11 : Win.WinO B w s.mem s₁₁.mem := w06.trans (w9.trans w911)
  have v11 : ∀ j < 24, 4 ≤ j → wordsVal s₁₁.mem B (slot w j) w = wordsVal s₁₀.mem B (slot w j) w :=
    fun j hj hj' => Mont.Outside.wordsVal o11 (by
      have := Win.slot_lt (w := w) (show 3 < 4 by decide)
      have := Nat.mul_le_mul_right (8 * (w + 2)) hj'
      unfold slot at *; omega_arith) (hfit j hj)
  rw [xb' (w06.trans (w9.trans (by rw [m10]; exact Mont.Outside.refl _ _ _ _)))] at r11
  -- `(m₁ + p - m₂ mod p) mod p` into array 3.
  refine seq4_then (recSub_ok (Pv := Pv) (m1 := m1) c11.scr (by omega_arith) (by omega_arith) hw' c11.a7
    ((k111.gpr (by decide)).trans hra) c11.s5 c11.t0 c11.n r11
    (by rw [v11 4 (by decide) (by decide), m10, v9 4 (by decide) (Or.inr rfl), m4₆])
    (Nat.mod_lt _ (by omega_arith)) hm1P) fun s₁₂ ⟨⟨a12, r12, h712⟩, k12'⟩ => ?_
  have k112 := k111.trans k12'
  -- `h = a qInv mod p` into array 4.
  have u12 : ∀ j < 24, j ≠ 3 → j ≠ 4 → wordsVal s₁₂.mem B (slot w j) w = wordsVal s₁₁.mem B (slot w j) w :=
    fun j hj h3 h4 => Pub.arrays_V r12 (by simp; omega_arith) (hfit j hj)
  have ws12 : Win.WinO B w s.mem s₁₂.mem :=
    ws11.trans (Win.win_of_arrays r12 (by decide))
  refine WP.mono (recMont_ok (a := (m1 + Pv - _ % Pv) % Pv) (QI := QI) (hs.congr k112.2.2) (hx.congr k112.2.2)
    hsep (by omega_arith) hZX hwX hw2 hw' h712 (by
      rw [k12'.gpr (by decide)]; exact c11.s5) (by rw [k12'.gpr (by decide)]; exact c11.t0)
    ((k112.gpr (by decide)).trans h6) ((k112.gpr (by decide)).trans h11) ?_
    (by rw [u12 0 (by decide) (by decide) (by decide)]; exact c11.n) hodd a12 ?_
    (by rw [xw ws12]; exact hQ) hQP) fun t ⟨⟨ht4, rt⟩, kt⟩ => ⟨⟨ht4, ws12.trans (Win.win_of_arrays rt (by decide)), ?_⟩,
      (k112.trans kt).mono (by decide)⟩
  · rw [show Mont.word s₁₂.mem B (slot w 0) = Mont.word s₁₁.mem B (slot w 0) from
      r12.word0_of_not_mem (by decide) (by decide) (by omega_arith) (by omega_arith), k12'.gpr (by decide)]
    exact c11.inv
  · rw [u12 7 (by decide) (by decide) (by decide), v11 7 (by decide) (by decide), m10, rr9, ← Nat.pow_add]
    congr 2; omega_arith
  · rw [kt.gpr (by decide)]; exact h712

/-! ## `recombineX` -/

/-- A number of `w` words, zero-extended to `W`. -/
theorem wordsVal_widen {m m' : Mem} {B B' : Addr} : ∀ {d d' w W : Nat},
    (∀ i < w, Mont.word m B (d + 8 * i) = Mont.word m' B' (d' + 8 * i)) →
    (∀ i, w ≤ i → i < W → Mont.word m B (d + 8 * i) = 0) → w ≤ W → wordsVal m B d W = wordsVal m' B' d' w
  | d, _, 0, W, _, hz, _ => ModArith.ma_wordsVal_zero fun i hi => hz i (Nat.zero_le _) hi
  | d, d', w + 1, W + 1, h, hz, hw => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    simp only [wordsVal]
    rw [h0, wordsVal_widen (d := d + 8) (d' := d' + 8) (w := w) (W := W)
      (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega, show d' + 8 * (i + 1) = d' + 8 + 8 * i by omega] at this)
      (fun i h1 h2 => by
        have := hz (i + 1) (by omega) (by omega)
        rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega] at this) (by omega)]
  | _, _, _ + 1, 0, _, _, hw => absurd hw (by omega)

theorem wX_val {W : Nat} (h : W < 2 ^ 31) :
    (BitVec.ofNat 64 (8 * (W + 2)) - BitVec.ofNat 64 16) >>> 3 = BitVec.ofNat 64 W := by
  rw [show BitVec.ofNat 64 (8 * (W + 2)) - BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * W) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith, ofNat_shr3 _ (by omega_arith)]
  congr 1; omega

/-- The registers `widen` writes. -/
def widenRegs : List Reg := [.a7, .ra, .s5, .t0, .t2, .t3, .t4, .t5, .s0, .s8, .s9]

/-- `widen oB oLen xj`: the prime working space's array 4 (at the header's
`oB`, of `wordsOf l` words for the length `l` at `oLen`) into `X`'s array
`xj`, zero-extended to `X`'s `W` words. -/
theorem widen_ok {s : State} {S Bp : Addr} {ZX Zp wX l oB oLen xj : Nat} (hx : Scr s S ZX) (hp : Scr s Bp Zp)
    (hsep : ∀ x, ofs Bp x < Zp → ZX ≤ ofs S x)
    (h6 : s.gpr .s6 = S) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hB : oB + 8 ≤ ZX) (hB8 : oB % 8 = 0) (hB' : oB < 2048) (hL : oLen + 8 ≤ ZX) (hL8 : oLen % 8 = 0)
    (hL' : oLen < 2048) (hbase : Mont.word s.mem S oB = Bp) (hlen : Mont.word s.mem S oLen = BitVec.ofNat 64 l)
    (hl1 : 1 ≤ l) (hl' : l ≤ 1024) (hxj : xj < 8) (hZX : slot wX 8 ≤ ZX) (hZp : slot (wordsOf l) 8 ≤ Zp)
    (hwX : wordsOf l ≤ wX) (hwX' : wX < 2 ^ 31) :
    WP isa (widen oB oLen xj) s fun t =>
      (wordsVal t.mem S (slot wX xj) wX = wordsVal s.mem Bp (slot (wordsOf l) 4) (wordsOf l) ∧
        Mont.Outside S (slot wX xj) (8 * wX) s.mem t.mem) ∧ Keep widenRegs s t := by
  have hnx := hx.nowrap
  have hnp := hp.nowrap
  have wb := wordsOf_bounds hl1 hl'
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have p4 := e (wordsOf l) 4; have p8 := e (wordsOf l) 8
  have xj8 := slot_le (w := wX) hxj
  have xal := slot_al8 wX xj
  have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  unfold widen
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (setupP_ok hx (h6.trans (BitVec.add_zero S).symm) hB hB8 hB' hL hL8 hL' hbase hlen hl1 hl')
    fun s₁ ⟨⟨a7, _, a5, a0, _, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .s9) (by decide) a7 a5 4) fun s₂ ⟨⟨b9, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.s8] (Q := fun s₃ => s₃.gpr .s8 = BitVec.ofNat 64 (wordsOf l) ∧ s₃.mem = s₂.mem) ?_
    (by rfl) (by rfl)) fun s₃ ⟨⟨b8, m3⟩, k3⟩ => ?_
  · brun [(k2.gpr (by decide)).trans a0, add_ofNat_zero]
  have k13 := k12.trans k3
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k13.gpr (by decide)).trans h6) ((k13.gpr (by decide)).trans h11)
    xj) fun s₄ ⟨⟨b3, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (WP.keep [.t0] (Q := fun s₅ => s₅.gpr .t0 = BitVec.ofNat 64 wX ∧ s₅.mem = s₄.mem) ?_
    (by rfl) (by rfl)) fun s₅ ⟨⟨c0, m5⟩, k5⟩ => ?_
  · simp only [Crt.wX]
    brun [(k14.gpr (by decide)).trans h11, wX_val hwX']
  have k15 := k14.trans k5
  have m05 : s₅.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  refine WP.seq (WP.mono (zeroWords_ok (d := slot wX xj) (hx.congr k15.2.2) ((k5.gpr (by decide)).trans b3) c0
    (by omega_arith) hwX' (by omega_arith) (by omega_arith)) fun s₆ ⟨⟨_, hz, o6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k16.gpr (by decide)).trans h6) ((k16.gpr (by decide)).trans h11)
    xj) fun s₇ ⟨⟨d3, m7⟩, k7⟩ => ?_
  refine WP.mono (WP.keep [.t4, .t0] (Q := fun s₈ => s₈.gpr .t4 = off Bp (slot (wordsOf l) 4) ∧
      s₈.gpr .t0 = BitVec.ofNat 64 (wordsOf l) ∧ s₈.mem = s₇.mem) ?_ (by rfl) (by rfl)) fun s₈ ⟨⟨d4, d0, m8⟩, k8⟩ => ?_
  · brun [((((k3.trans k4).trans k5).trans k6).trans k7).gpr (r := .s9) (by decide) |>.trans b9,
      ((((k4.trans k5).trans k6).trans k7)).gpr (r := .s8) (by decide) |>.trans b8, add_ofNat_zero]
  have k18 := (k16.trans k7).trans k8
  refine WP.mono (copyWords_ok (dS := slot (wordsOf l) 4) (dD := slot wX xj) (hp.congr k18.2.2) (hx.congr k18.2.2)
    d4 ((k8.gpr (by decide)).trans d3) d0 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hsep) fun t ⟨⟨_, hc, o9⟩, k9⟩ => ⟨⟨?_, ?_⟩, (k18.trans k9).mono (by decide)⟩
  · have m68 : s₈.mem = s₆.mem := by rw [m8, m7]
    rw [m68] at hc o9
    refine wordsVal_widen (fun i hi => (hc i hi).trans ?_) (fun i h1 h2 => ?_) hwX
    · have : Mont.word s₆.mem Bp (slot (wordsOf l) 4 + 8 * i) = Mont.word s₅.mem Bp (slot (wordsOf l) 4 + 8 * i) :=
        Outside.word_sep o6 (B := Bp) (Z := Zp) (Zp := ZX) (fun x hx' => hsep x hx') (by omega_arith)
          (by omega_arith) hnp
      rw [this, m05]
    · rw [Mont.Outside.word o9 (Or.inr (by omega_arith)) (by omega_arith)]; exact hz i h2
  · rw [m05] at o6
    rw [show s₈.mem = s₆.mem by rw [m8, m7]] at o9
    exact o6.trans (Mont.Outside.mono o9 (Nat.le_refl _) (by omega_arith))

/-- The low word of `2^(64 W) - 1`: all ones. -/
theorem word0_ones {m : Mem} {B : Addr} {d W : Nat} (hW : 1 ≤ W) (h : wordsVal m B d W = 2 ^ (64 * W) - 1) :
    (Mont.word m B d).toNat = 2 ^ 64 - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega⟩
  simp only [wordsVal] at h
  have hp : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
  have hw := (Mont.word m B d).isLt
  rw [show 64 * (k + 1) = 64 + 64 * k by omega, Nat.pow_add] at h
  have := Nat.mul_le_mul_left (2 ^ 64) hp
  omega_arith

/-- Montgomery multiplication modulo `M = R - 1`, `R ≡ 1`: the product,
when it is below `M`. -/
theorem mont_ones {R x a : Nat} (hR : 2 ≤ R - 1) (hx : x < R - 1) (h : x * R % (R - 1) = a % (R - 1))
    (ha : a < R - 1) : x = a := by
  have e : x * R = x + (R - 1) * x := by
    rw [show x * R = x * (R - 1) + x by
      rw [← Nat.mul_add_one, show R - 1 + 1 = R by omega], Nat.add_comm, Nat.mul_comm]
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt ha] at h
  exact h

/-- The registers `recombineX` writes. -/
def recXRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .ra, .s5, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4,
    .s8, .s9]

/-- `recombineX`: in `X` (at `S`, `s6`, of `W` words, `M = 2^(64 W) - 1` in
array 0 and `q` in array 5), `h` (`P`'s array 4) into array 7 and `m₂`
(`Q`'s array 4) into array 6, zero-extended, then `q h + m₂` into array 4,
when it is below `M`. -/
theorem recombineX_ok {s : State} {S BP BQ : Addr} {ZX ZP ZQ wX lp lq qv : Nat}
    (hx : Scr s S ZX) (hp : Scr s BP ZP) (hq : Scr s BQ ZQ)
    (sepP : ∀ x, ofs BP x < ZP → ZX ≤ ofs S x) (sepQ : ∀ x, ofs BQ x < ZQ → ZX ≤ ofs S x)
    (h6 : s.gpr .s6 = S) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hZX : slot wX 8 ≤ ZX) (hw2 : 2 ≤ wX) (hw' : wX < 2 ^ 31)
    (hbP : Mont.word s.mem S oBP = BP) (hlP : Mont.word s.mem S oPLen = BitVec.ofNat 64 lp)
    (hbQ : Mont.word s.mem S oBQ = BQ) (hlQ : Mont.word s.mem S oQLen = BitVec.ofNat 64 lq)
    (hp1 : 1 ≤ lp) (hp' : lp ≤ 1024) (hq1 : 1 ≤ lq) (hq' : lq ≤ 1024)
    (hZP : slot (wordsOf lp) 8 ≤ ZP) (hZQ : slot (wordsOf lq) 8 ≤ ZQ)
    (hwP : wordsOf lp ≤ wX) (hwQ : wordsOf lq ≤ wX)
    (hM : wordsVal s.mem S (slot wX 0) wX = 2 ^ (64 * wX) - 1) (h5 : wordsVal s.mem S (slot wX 5) wX = qv)
    (hH : wordsVal s.mem BP (slot (wordsOf lp) 4) (wordsOf lp) < 2 ^ (64 * wX) - 1)
    (hlt : qv * wordsVal s.mem BP (slot (wordsOf lp) 4) (wordsOf lp) +
      wordsVal s.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) < 2 ^ (64 * wX) - 1) :
    WP isa recombineX s fun t =>
      (wordsVal t.mem S (slot wX 4) wX = qv * wordsVal s.mem BP (slot (wordsOf lp) 4) (wordsOf lp) +
          wordsVal s.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) ∧
        Arrays S wX [2, 3, 4, 6, 7] s.mem t.mem) ∧ Keep recXRegs s t := by
  have hnx := hx.nowrap
  have hnq := hq.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have x0 := e wX 0; have x4 := e wX 4; have x6 := e wX 6; have x7 := e wX 7; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  have hfit : ∀ j < 8, slot wX j + 8 * wX ≤ 2 ^ 64 := fun j hj => by
    have := slot_le (w := wX) hj; omega_arith
  have hR : 2 ≤ 2 ^ (64 * wX) - 1 := by
    have : 2 ^ 64 ≤ 2 ^ (64 * wX) := Nat.pow_le_pow_right (by decide) (by omega)
    omega_arith
  unfold recombineX
  -- `h` into array 7.
  have hoff : ∀ o, o + 8 ≤ 256 → o + 8 ≤ ZX := fun o ho => by omega_arith
  refine WP.seq (WP.mono (widen_ok (xj := 7) hx hp sepP h6 h11 (hoff _ (by decide)) (by decide) (by decide)
    (hoff _ (by decide)) (by decide) (by decide) hbP hlP hp1 hp' (by decide) hZX hZP hwP hw') fun s₁ ⟨⟨v7, o1⟩, k1⟩ => ?_)
  have hd : ∀ {d}, d + 8 ≤ 256 → Mont.word s₁.mem S d = Mont.word s.mem S d := fun hd' =>
    Mont.Outside.word o1 (Or.inl (by omega_arith)) (by omega_arith)
  -- `m₂` into array 6.
  refine WP.seq (WP.mono (widen_ok (xj := 6) (hx.congr k1.2.2) (hq.congr k1.2.2) sepQ ((k1.gpr (by decide)).trans h6)
    ((k1.gpr (by decide)).trans h11) (hoff _ (by decide)) (by decide) (by decide) (hoff _ (by decide)) (by decide)
    (by decide) ((hd (by decide)).trans hbQ) ((hd (by decide)).trans hlQ) hq1 hq' (by decide) hZX hZQ hwQ hw')
    fun s₂ ⟨⟨v6, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have r1 : Arrays S wX [7] s.mem s₁.mem := Arrays.of_outside (j := 7) (by simp) o1 (Nat.le_refl _) (by omega_arith)
  have r2 : Arrays S wX [6] s₁.mem s₂.mem := Arrays.of_outside (j := 6) (by simp) o2 (Nat.le_refl _) (by omega_arith)
  have mq : wordsVal s₁.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) = wordsVal s.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) :=
    wordsVal_of_words fun i hi => Pub.Outside.word_apart o1 sepQ (by omega_arith)
      (by have := slot_le (w := wordsOf lq) (show 4 < 8 by decide); omega_arith) hnq
  rw [mq] at v6
  have v7' : wordsVal s₂.mem S (slot wX 7) wX = wordsVal s.mem BP (slot (wordsOf lp) 4) (wordsOf lp) :=
    (Pub.arrays_V r2 (j := 7) (by decide) (hfit 7 (by decide))).trans v7
  have r12 : Arrays S wX [6, 7] s.mem s₂.mem := (r1.mono (by simp)).trans (r2.mono (by simp))
  have m0 : wordsVal s₂.mem S (slot wX 0) wX = 2 ^ (64 * wX) - 1 :=
    (Pub.arrays_V r12 (j := 0) (by decide) (hfit 0 (by decide))).trans hM
  have q5 : wordsVal s₂.mem S (slot wX 5) wX = qv :=
    (Pub.arrays_V r12 (j := 5) (by decide) (hfit 5 (by decide))).trans h5
  -- `X`'s registers, `t1 := 1 = -M⁻¹ mod 2⁶⁴`.
  have e0' : slot wX 0 = hdrBytes := by simp [slot]
  refine WP.seq (WP.mono (WP.keep [.a7, .ra, .s5, .t0, .t1] (Q := fun s₃ => s₃.gpr .a7 = off S (slot wX 0) ∧
      s₃.gpr .s5 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ s₃.gpr .t0 = BitVec.ofNat 64 wX ∧ s₃.gpr .t1 = 1 ∧
      s₃.mem = s₂.mem) ?_ (by rfl) (by rfl)) fun s₃ ⟨⟨c7, c5, c0, c1, m3⟩, k3⟩ => ?_)
  · simp only [Crt.wX]
    rw [e0']
    brun [exec_addi_nat (show hdrBytes < 2048 by decide), (k12.gpr (r := .s6) (by decide)).trans h6,
      (k12.gpr (r := .s11) (by decide)).trans h11, add_ofNat_zero, wX_val hw', r2_exec_li_one]
  have k13 := k12.trans k3
  rw [← m3] at m0 q5 v7' v6
  -- `q h mod M = q h` into array 4.
  have w0 : (Mont.word s₃.mem S (slot wX 0)).toNat = 2 ^ 64 - 1 := word0_ones (by omega) m0
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hx.congr k13.2.2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZX c7 c5 c0
    (by rw [show (word s₃.mem S (slot wX 0)).toNat = 2 ^ 64 - 1 from w0, c1]; decide)
    (by rw [v7', m0]; exact hH)) fun s₄ ⟨⟨x4P, x4R, r4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  rw [m0] at x4P
  rw [m0, q5, v7'] at x4R
  have x4 : wordsVal s₄.mem S (slot wX 4) wX = qv * wordsVal s.mem BP (slot (wordsOf lp) 4) (wordsOf lp) :=
    mont_ones hR x4P x4R (by omega_arith)
  have v6' : wordsVal s₄.mem S (slot wX 6) wX = wordsVal s.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) :=
    (Pub.arrays_V r4 (j := 6) (by decide) (hfit 6 (by decide))).trans v6
  -- `+ m₂`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k14.gpr (by decide)).trans h6) ((k14.gpr (by decide)).trans h11) 4)
    fun s₅ ⟨⟨b3, m5⟩, k5⟩ => ?_
  refine WP.mono (xb_ok (rd := .t4) (by decide) (((k14.trans k5).gpr (by decide)).trans h6)
    (((k14.trans k5).gpr (by decide)).trans h11) 6) fun s₆ ⟨⟨b4, m6⟩, k6⟩ => ?_
  refine WP.mono (WP.keep [.s4] (Q := fun s₇ => s₇.gpr .s4 = BitVec.allOnes 64 ∧ s₇.mem = s₆.mem) ?_
    (by rfl) (by rfl)) fun s₇ ⟨⟨b5, m7⟩, k7⟩ => ?_
  · brun [Win.exec_li_m1]
  have k17 := ((k14.trans k5).trans k6).trans k7
  have m47 : s₇.mem = s₄.mem := by rw [m7, m6, m5]
  refine WP.mono (ModArith.addMask64_ok (b := true) (dT := slot wX 4) (dM := slot wX 6) (hx.congr k17.2.2)
    ((k6.trans k7).gpr (by decide) |>.trans b3) ((k7.gpr (by decide)).trans b4) ((((k4.trans k5).trans k6).trans k7).gpr (by decide) |>.trans c0)
    b5 (slot_al8 _ _) (slot_al8 _ _) (by omega) hw' (by omega_arith) (by omega_arith) (Or.inl (by omega_arith)))
    fun t ⟨hv, o8, k8⟩ => ⟨⟨?_, ?_⟩, (k17.trans k8).mono (by decide)⟩
  · rw [m47, x4, v6'] at hv
    rw [hv]; simp only [↓reduceIte]; exact Nat.mod_eq_of_lt (by omega_arith)
  · rw [m47] at o8
    rw [← m3] at r12
    exact ((r12.mono (js' := [2, 3, 4, 6, 7]) (by decide)).trans (r4.mono (by decide))).trans
      ((Arrays.of_outside (js := [4]) (j := 4) (by simp) o8 (Nat.le_refl _) (by omega_arith)).mono (by decide))

/-! ## The output -/

/-- The registers `final` writes. -/
def outRegs : List Reg := [.a7, .s5, .s9, .s10, .s11, .s0, .a0, .t4, .t3, .t5]

/-- The block before `output`, then `output`: `X`'s array 4 (`k = n_len`
bytes of it, most significant first) to `out` under the header's mask, and
`a0 :=` 1 if it is set, else 0. -/
theorem final_ok {s : State} {S O : Addr} {ZX wX k : Nat} {b : Bool} (hx : Scr s S ZX)
    (ho : ∀ i < k, InRegions s.wr (off O i) 1) (hno : O.toNat + k ≤ 2 ^ 64)
    (h6 : s.gpr .s6 = S) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hO : Mont.word s.mem S oOut = O) (hk : Mont.word s.mem S oNLen = BitVec.ofNat 64 k)
    (hm : Mont.word s.mem S oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (hk1 : 1 ≤ k) (hkw : k ≤ 8 * wX) (hZX : slot wX 8 ≤ ZX)
    (hsep : ∀ x, ofs O x < k → ZX ≤ ofs S x) :
    WP isa (.seq (.block [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut,
        .load .d .s11 .s6 oNLen, .load .d .s9 .s6 oMask]) output) s fun t =>
      ((∀ i < k, t.mem (off O i) = if b then s.mem (off S (slot wX 4 + (k - 1 - i))) else 0) ∧
        Mont.Outside O 0 k s.mem t.mem ∧ t.gpr .a0 = BitVec.ofNat 64 (if b then 1 else 0)) ∧
      Keep outRegs s t := by
  have hnx := hx.nowrap
  have x8 : slot wX 8 = hdrBytes + 8 * (8 * (wX + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have e0' : slot wX 0 = hdrBytes := by simp [slot]
  have z : off S 0 = S := BitVec.add_zero S
  have hO' : s.mem.readW S 64 = O := by rw [← z]; exact hO
  have l0 : InRegions (s.rd ++ s.wr) S 8 := by rw [← z]; exact hx.ld (by omega_arith)
  have hk' : s.mem.readW (off S 16) 64 = BitVec.ofNat 64 k := hk
  have hm' : s.mem.readW (off S 88) 64 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) := hm
  refine WP.seq (WP.mono (WP.keep [.a7, .s5, .s10, .s11, .s9] (Q := fun s₁ => s₁.gpr .a7 = off S (slot wX 0) ∧
      s₁.gpr .s5 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ s₁.gpr .s10 = off O 0 ∧ s₁.gpr .s11 = BitVec.ofNat 64 k ∧
      s₁.gpr .s9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) ∧ s₁.mem = s.mem) ?_ (by rfl) (by rfl))
    fun s₁ ⟨⟨c7, c5, c10, c11, c9, m1⟩, k1⟩ => ?_)
  · rw [e0']
    brun [exec_addi_nat (show hdrBytes < 2048 by decide), h6, h11, add_ofNat_zero, oOut, oNLen, oMask,
      l0, hx.al, hx.ld (show 16 + 8 ≤ ZX by omega_arith), hx.al8 (show 16 + 8 ≤ ZX by omega_arith) (by decide),
      hx.ld (show 88 + 8 ≤ ZX by omega_arith), hx.al8 (show 88 + 8 ≤ ZX by omega_arith) (by decide), hO', hk', hm']
  refine WP.mono (Pub.output_ok (hx.congr k1.2.2) (by rw [k1.2.2]; exact ho) hno c7 c5 c11 c10 c9 hk1 hkw hZX hsep)
    fun t ⟨⟨hb, hout, ha⟩, kt⟩ => ⟨⟨fun i hi => by rw [hb i hi, m1], by rw [m1] at hout; exact hout, ha⟩,
      (k1.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.RISCV64.Crt
