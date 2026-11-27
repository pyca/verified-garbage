module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPower
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Bignum.RISCV64.CrtMid2`, which this module and modules that import it used -/

section

/-! ### `Bignum.RISCV64.CrtRecomb`, which only this module used -/

section

/-!
# The RSA private-key operation on RISC-V: the recombination

* `xb_ok`: the base of `X`'s array `j`, from `s6` and `s11`;
* `recombineP_ok`: `h = (m₁ - m₂ mod p) qInv mod p` in `p`'s working space;
* `widen_ok` and `recombineX_ok`: `q h + m₂` in `X`.
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
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega_using []]

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
  obtain e : x4 * R % P = a * q * R % P := by
    rw [h4, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, h5, Nat.mod_mul_mod]
  rw [← Nat.mod_eq_of_lt h4P]
  exact VG.Proof.Bignum.mont_cancel hR e

/-- The registers `recSub` writes. -/
def subRegs : List Reg := [.a0, .a5, .a6, .a7, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `recombineP`'s middle: `(m₁ + p - r) mod p` into array 3, from `m₁` in
array 9 and `r` in array 4, both below `p` (array 0), changing only arrays 3
and 9 (above `m₁`). -/
theorem recSub_ok {s : State} {B : Addr} {Z w Pv m1 r : Nat} (hs : Scr s B Z) (hZ : slot w 10 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (hra : s.gpr .ra = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hP : wordsVal s.mem B (slot w 0) w = Pv) (hr : wordsVal s.mem B (slot w 4) w = r)
    (hm1 : wordsVal s.mem B (slot w 9) w = m1) (hrP : r < Pv) (hm1P : m1 < Pv) :
    WP isa (.seq (.block (base .t3 9 ++ ([.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0,
        .store .d .s0 .t3 0] : List Instr) ++ base .a5 9 ++ base .a6 3 ++ base .a7 4))
      (.seq subMod64 (.seq (.block (([.addi .a7 .ra 0] : List Instr) ++ base .t3 3 ++ base .t4 0))
        ModArith.addMask64))) s fun t =>
      (wordsVal t.mem B (slot w 3) w = (m1 + Pv - r) % Pv ∧ Arrays B w [3, 9] s.mem t.mem ∧
        t.gpr .a7 = off B (slot w 0)) ∧ Keep subRegs s t := by
  have hnw := hs.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8; have e9 := e 9; have e10 := e 10
  have hh : hdrBytes = 256 := rfl
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 9) fun s₁ ⟨⟨a3, m1'⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t3, .s0] (Q := fun s₂ => s₂.gpr .t3 = off B (slot w 9 + 8 * w) ∧
      s₂.mem = s₁.mem.writeW (off B (slot w 9 + 8 * w)) (0 : BitVec 64)) ?_ (by rfl) (by rfl)) fun s₂ ⟨⟨b3, m2⟩, k2⟩ => ?_
  · have q : off B (slot w 9 + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w 9 + 8 * w) := by
      rw [off_sub _ (by omega_arith)]; congr 2
    brun [a3, (k1.gpr (r := .s5) (by decide)).trans h5, off_add, q,
      (hs.congr k1.2.2).st (show slot w 9 + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k1.2.2).al8 (show slot w 9 + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith), BitVec.add_zero, fin64_exec_li_zero]
  obtain k12 := k1.trans k2
  obtain g7 : ∀ {t : State} {rs : List Reg}, Keep rs s t → Reg.a7 ∉ rs → t.gpr .a7 = off B (slot w 0) :=
    fun k h => (k.gpr h).trans h7
  obtain g5 : ∀ {t : State} {rs : List Reg}, Keep rs s t → Reg.s5 ∉ rs → t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) :=
    fun k h => (k.gpr h).trans h5
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) (g7 k12 (by decide)) (g5 k12 (by decide)) 9)
    fun s₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) (g7 k13 (by decide)) (g5 k13 (by decide)) 3)
    fun s₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  refine WP.mono (Pub.base_ok (rd := .a7) (by decide) (g7 k14 (by decide)) (g5 k14 (by decide)) 4)
    fun s₅ ⟨⟨a7, m5⟩, k5⟩ => ?_
  obtain k15 := k14.trans k5
  obtain m15 : s₅.mem = s.mem.writeW (off B (slot w 9 + 8 * w)) (0 : BitVec 64) := by rw [m5, m4, m3, m2, m1']
  obtain hwo : Mont.Outside B (slot w 9 + 8 * w) 8 s.mem s₅.mem := by
    rw [m15]; exact writeW_outside s.mem B (d := slot w 9 + 8 * w) (0 : BitVec 64) (by omega_arith)
  obtain a5' : s₅.gpr .a5 = off B (slot w 9) := ((k4.trans k5).gpr (by decide)).trans a5
  obtain a6' : s₅.gpr .a6 = off B (slot w 3) := (k5.gpr (by decide)).trans a6
  obtain t0' : s₅.gpr .t0 = BitVec.ofNat 64 w := (k15.gpr (by decide)).trans ht0
  refine WP.seq (WP.mono (subMod64_ok (dA := slot w 9) (dT := slot w 3) (dM := slot w 4) (hs.congr k15.2.2)
    a5' a6' a7 t0' hw hw' (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (Or.inl (by omega_arith)) (Or.inl (by omega_arith))) fun s₆ ⟨⟨c, hc, hsum, h4⟩, o6, k6⟩ => ?_)
  obtain k16 := k15.trans k6
  obtain wtop : Mont.word s₅.mem B (slot w 9 + 8 * w) = 0 := by rw [m15]; exact word_writeW_self _ _ _ _
  obtain vA : wordsVal s₅.mem B (slot w 9) w = m1 := by
    rw [Mont.Outside.wordsVal hwo (Or.inl (by omega_arith)) (by omega_arith), hm1]
  obtain vM : wordsVal s₅.mem B (slot w 4) w = r := by
    rw [Mont.Outside.wordsVal hwo (Or.inl (by omega_arith)) (by omega_arith), hr]
  rw [vA, vM] at hsum
  rw [wtop] at h4
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7] (Q := fun s₇ => s₇.gpr .a7 = off B (slot w 0) ∧ s₇.mem = s₆.mem) ?_
    (by rfl) (by rfl)) fun s₇ ⟨⟨b7, m7⟩, k7⟩ => ?_
  · brun [(k16.gpr (r := .ra) (by decide)).trans hra, add_ofNat_zero]
  obtain k17 := k16.trans k7
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) b7 (g5 k17 (by decide)) 3) fun s₈ ⟨⟨c3, m8⟩, k8⟩ => ?_
  obtain k18 := k17.trans k8
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k8.gpr (by decide)).trans b7) (g5 k18 (by decide)) 0)
    fun s₉ ⟨⟨c4, m9⟩, k9⟩ => ?_
  obtain k19 := k18.trans k9
  obtain s4' : s₉.gpr .s4 = if decide (0 < c) then BitVec.allOnes 64 else 0 := by
    rw [((k7.trans k8).trans k9).gpr (by decide), h4]
    simp only [decide_eq_true_eq, show (0 : BitVec 64).toNat = 0 from rfl]
  refine WP.mono (ModArith.addMask64_ok (dT := slot w 3) (dM := slot w 0) (hs.congr k19.2.2)
    ((k9.gpr (by decide)).trans c3) c4 ((k19.gpr (by decide)).trans ht0) s4' (by omega_arith) (by omega_arith) hw hw'
    (by omega_arith) (by omega_arith) (Or.inr (by omega_arith))) fun t ⟨hv, o10, k10⟩ => ?_
  obtain m69 : s₉.mem = s₆.mem := by rw [m9, m8, m7]
  rw [m69] at hv
  obtain vP : wordsVal s₆.mem B (slot w 0) w = Pv := by
    rw [Mont.Outside.wordsVal o6 (Or.inl (by omega_arith)) (by omega_arith),
      Mont.Outside.wordsVal hwo (Or.inl (by omega_arith)) (by omega_arith), hP]
  rw [vP] at hv
  refine ⟨⟨?_, ?_, (k10.gpr (by decide)).trans ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans b7))⟩,
    (k19.trans k10).mono (by decide)⟩
  · refine subAdd_val (N := 64 * w) (c := c) (T := wordsVal s₆.mem B (slot w 3) w) hm1P hrP
      (hP ▸ wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _) hsum ?_
    rw [hv]; simp only [decide_eq_true_eq]
  · rw [m69] at o10
    exact ((Arrays.of_outside (j := 9) (by simp) hwo (by omega_arith) (by omega_arith)).trans
      (Arrays.of_outside (j := 3) (by simp) o6 (Nat.le_refl _) (by omega_arith))).trans
      (Arrays.of_outside (j := 3) (by simp) o10 (Nat.le_refl _) (by omega_arith))

/-- Two numbers of `k` words that agree word by word. -/
theorem wordsVal_of_words {m m' : Mem} {B B' : Addr} : ∀ {d d' k : Nat},
    (∀ i < k, Mont.word m B (d + 8 * i) = Mont.word m' B' (d' + 8 * i)) → wordsVal m B d k = wordsVal m' B' d' k
  | _, _, 0, _ => rfl
  | d, d', k + 1, h => by
    obtain h0 := h 0 (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    simp only [wordsVal]
    rw [h0, wordsVal_of_words (d := d + 8) (d' := d' + 8) fun i hi => by
      have := h (i + 1) (by omega_using [hi])
      rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega_using [], show d' + 8 * (i + 1) = d' + 8 + 8 * i by omega_using []] at this]

/-- The registers `recMont` writes. -/
def recMRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `recombineP`'s end: `qInv` (`w` words of `X`'s array 7) into array 6,
then `a qInv R⁻¹ mod p` into array 5 and `a qInv mod p` into array 4, from
`a` in array 3 and `R² mod p` in array 1. -/
theorem recMont_ok {s : State} {B BX : Addr} {Z ZX w wX Pv a QI : Nat} (hs : Scr s B Z) (hx : Scr s BX ZX)
    (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x) (hZ : slot w 8 ≤ Z) (hZX : slot wX 8 ≤ ZX) (hwX : w ≤ wX)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hP : wordsVal s.mem B (slot w 0) w = Pv) (hodd : Pv % 2 = 1)
    (ha : wordsVal s.mem B (slot w 3) w = a)
    (hRR : wordsVal s.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv)
    (hQ : wordsVal s.mem BX (slot wX 7) w = QI) (hQP : QI < Pv) :
    WP isa (.seq (.block (base .t3 6 ++ xb .t4 7)) (.seq copyN (.seq (montOp 5 3 6) (montOp 4 5 1)))) s
      fun t => (wordsVal t.mem B (slot w 4) w = a * QI % Pv ∧ Arrays B w [2, 3, 4, 5, 6] s.mem t.mem) ∧
        Keep recMRegs s t := by
  have hnw := hs.nowrap
  have hnx := hx.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain e0 := e w 0; have e3 := e w 3; have e6 := e w 6; have e7 := e w 7; have e8 := e w 8
  obtain x7 := e wX 7; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  obtain hfit : ∀ j < 8, slot w j + 8 * w ≤ 2 ^ 64 := fun j hj => by
    have := slot_le (w := w) hj; omega_arith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 6) fun s₁ ⟨⟨b3, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h6) ((k1.gpr (by decide)).trans h11) 7)
    fun s₂ ⟨⟨b4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.seq (WP.mono (copyWords_ok (dS := slot wX 7) (dD := slot w 6) (hx.congr k12.2.2) (hs.congr k12.2.2)
    b4 ((k2.gpr (by decide)).trans b3) ((k12.gpr (by decide)).trans ht0) (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) hsep) fun s₃ ⟨⟨_, hc, o3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  obtain m02 : s₂.mem = s.mem := by rw [m2, m1]
  rw [m02] at hc o3
  obtain r3 : Arrays B w [6] s.mem s₃.mem := Arrays.of_outside (j := 6) (by simp) o3 (Nat.le_refl _) (by omega_arith)
  obtain q6 : wordsVal s₃.mem B (slot w 6) w = QI := (wordsVal_of_words hc).trans hQ
  obtain p3 : wordsVal s₃.mem B (slot w 0) w = Pv :=
    (Pub.arrays_V r3 (j := 0) (by decide) (hfit 0 (by decide))).trans hP
  obtain a3 : wordsVal s₃.mem B (slot w 3) w = a :=
    (Pub.arrays_V r3 (j := 3) (by decide) (hfit 3 (by decide))).trans ha
  obtain rr3 : wordsVal s₃.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv :=
    (Pub.arrays_V r3 (j := 1) (by decide) (hfit 1 (by decide))).trans hRR
  obtain w03 : Mont.word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    r3.word0_of_not_mem (by decide) (by decide) (by omega_arith) (by omega_arith)
  obtain hP0 : 0 < Pv := by omega_arith
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 5) (a := 3) (b := 6) (hs.congr k13.2.2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans h5) ((k13.gpr (by decide)).trans ht0)
    (by rw [show word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) from w03, k13.gpr (by decide)]; exact hinv) (by rw [q6, p3]; exact hQP))
    fun s₄ ⟨⟨x5P, x5R, r4⟩, k4⟩ => ?_)
  obtain k14 := k13.trans k4
  rw [p3, a3, q6] at x5R
  rw [p3] at x5P
  obtain p4 : wordsVal s₄.mem B (slot w 0) w = Pv :=
    (Pub.arrays_V r4 (j := 0) (by decide) (hfit 0 (by decide))).trans p3
  obtain rr4 : wordsVal s₄.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv :=
    (Pub.arrays_V r4 (j := 1) (by decide) (hfit 1 (by decide))).trans rr3
  obtain w04 : Mont.word s₄.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    (r4.word0_of_not_mem (by decide) (by decide) (by omega_arith) (by omega_arith)).trans w03
  refine WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 1) (hs.congr k14.2.2) (by decide) (by decide)
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
  obtain hpre : WP isa (.block [.addi .t5 .t0 0]) s fun s₁ =>
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
  obtain hsrc : Mont.word t.mem B (dS + 8 * i) = Mont.word s.mem B (dS + 8 * i) :=
    Mont.Outside.word jout (by omega_arith) (by omega_arith)
  obtain hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
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
  obtain hw := writeW_outside t.mem B (d := dD + 8 * i) (Mont.word t.mem B (dS + 8 * i)) (by omega_arith)
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
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_using [hw]⟩
  simp only [wordsVal] at h
  rwa [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left] at h

/-- The registers `recombineP` writes. -/
def recPRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s7, .s8, .s9,
    .s10]

/-- `recombineP` up to `reduceIn`, then `c`. -/
abbrev recPA (c : Prog isa) : Prog isa :=
  .seq (.block (base .t3 9 ++ base .t4 4)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3)) c))

/-- `recombineP` up to `reduceIn`: `m₁` copied into array 9, and the context
of `p`'s Montgomery arithmetic. -/
theorem recPA_ok {s : State} {B : Addr} {Z w Pv m1 : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s B Z) (hZ : slot w 24 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hP : wordsVal s.mem B (slot w 0) w = Pv) (hodd : Pv % 2 = 1)
    (hm1 : wordsVal s.mem B (slot w 4) w = m1)
    (hc : ∀ s₇, Win.WCtx s₇ B Z w Pv → Keep recPRegs s s₇ → Win.WinO B w s.mem s₇.mem →
      wordsVal s₇.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w →
      wordsVal s₇.mem B (slot w 9) w = m1 → WP isa c s₇ Q) :
    WP isa (recPA c) s Q := by
  have hnw := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain e0 := e w 0; have e1 := e w 1; have e4 := e w 4; have e9 := e w 9; have e10 := e w 10
  obtain e24 := e w 24
  have hh : hdrBytes = 256 := rfl
  obtain hfit : ∀ j < 24, slot w j + 8 * w ≤ 2 ^ 64 := fun j hj => by
    have := Win.slot_lt (w := w) hj; omega_arith
  -- `m₁` into array 9.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 9) fun s₁ ⟨⟨b3, m1'⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) 4) fun s₂ ⟨⟨b4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  obtain m02 : s₂.mem = s.mem := by rw [m2, m1']
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 4) (dD := slot w 9) (hs.congr k12.2.2) b4
    ((k2.gpr (by decide)).trans b3) ((k12.gpr (by decide)).trans ht0) (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))) fun s₃ ⟨⟨hc3, o3⟩, k3⟩ => ?_)
  rw [m02] at hc3 o3
  obtain k13 := k12.trans k3
  obtain w03 : Win.WinO B w s.mem s₃.mem := Mont.Outside.mono o3 (by omega_arith) (by omega_arith)
  obtain v3 : ∀ j < 24, j ≠ 9 → wordsVal s₃.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun j hj h9 => Mont.Outside.wordsVal o3 (by
      rcases Nat.lt_or_gt_of_ne h9 with h | h
      · have := Win.slot_lt (w := w) h; omega_arith
      · have := Win.slot_lt (w := w) h; omega_arith) (hfit j hj)
  obtain m9₃ : wordsVal s₃.mem B (slot w 9) w = m1 := (wordsVal_of_words hc3).trans hm1
  -- `t1 := -p⁻¹ mod 2⁶⁴`; the bases of arrays 1–3.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  obtain p3 : wordsVal s₃.mem B (slot w 0) w = Pv := (v3 0 (by decide) (by decide)).trans hP
  refine WP.mono (minv_ok (d := slot w 0) (hs.congr k13.2.2) ((k13.gpr (by decide)).trans h7) (by omega_arith)
    (by omega_arith) (word0_odd (by omega_arith) (p3 ▸ hodd))) fun s₄ ⟨⟨hinv, m4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k14.gpr (by decide)).trans h7)
    ((k14.gpr (by decide)).trans h5) 1) fun s₅ ⟨⟨_, m5⟩, k5⟩ => ?_
  obtain k15 := k14.trans k5
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k15.gpr (by decide)).trans h7)
    ((k15.gpr (by decide)).trans h5) 2) fun s₆ ⟨⟨_, m6⟩, k6⟩ => ?_
  obtain k16 := k15.trans k6
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k16.gpr (by decide)).trans h7)
    ((k16.gpr (by decide)).trans h5) 3) fun s₇ ⟨⟨_, m7⟩, k7⟩ => ?_
  obtain k17 := k16.trans k7
  obtain m37 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  obtain c7 : Win.WCtx s₇ B Z w Pv := ⟨hs.congr k17.2.2, hw2, hw', hZ, (k17.gpr (by decide)).trans h7,
    (k17.gpr (by decide)).trans h5, (k17.gpr (by decide)).trans ht0,
    by rw [m37, ((k5.trans k6).trans k7).gpr (by decide)]; exact hinv, by rw [m37]; exact p3⟩
  obtain w07 : Win.WinO B w s.mem s₇.mem := by rw [m37]; exact w03
  exact hc s₇ c7 (k17.mono (by decide)) w07 (by rw [m37]; exact v3 1 (by decide) (by decide)) (by rw [m37]; exact m9₃)

/-- `recombineP` up to `reduceIn`'s chunks: the registers there. -/
theorem recPC_ok {s : State} {B BX : Addr} {Z ZX w wX k Pv : Nat}
    (hs : Scr s B Z) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (hZ : slot w 24 ≤ Z) (hZX : slot wX 8 ≤ ZX) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (hra : s.gpr .ra = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hkw : Mont.word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hXZ : slot wX 6 + 8 * (w * Win.nChunks ((k + 7) / 8) w) ≤ ZX)
    (hP : wordsVal s.mem B (slot w 0) w = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hR2 : wordsVal s.mem B (slot w 1) w = 2 ^ (128 * w) % Pv) :
    WP isa (recPA (Win.reduceInP (.block []))) s fun u =>
      u.gpr .a7 = off B (slot w 0) ∧ u.gpr .ra = off B (slot w 0) ∧ u.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      u.gpr .t0 = BitVec.ofNat 64 w ∧ u.gpr .s6 = BX ∧ u.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)) ∧
      u.gpr .s9 = off BX (slot wX 6 + 8 * (w * 0)) ∧
      u.gpr .s10 = BitVec.ofNat 64 ((k + 7) / 8) - BitVec.ofNat 64 (w * 0) := by
  have hnx := hx.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain x8 := e wX 8; have e0 := e w 0; have e1 := e w 1; have e24 := e w 24
  have hh : hdrBytes = 256 := rfl
  refine recPA_ok (m1 := wordsVal s.mem B (slot w 4) w) hs hZ hw2 hw' h7 h5 ht0 hP hodd rfl
    fun s₇ c7 k17 w07 R1 _ => ?_
  refine Win.reduceInA_ok (k := k) c7 ((k17.gpr (by decide)).trans hra) (hx.congr k17.2.2) hsep
    ((k17.gpr (by decide)).trans h6) ((k17.gpr (by decide)).trans h11)
    (by rw [Outside.word_sep (Win.PFr.of_win w07) hsep (by omega_arith)
      (show oNLen + 8 ≤ ZX by unfold oNLen; omega_arith) hnx]; exact hkw) hk hk' hXZ hP2 hodd
    (by show wordsVal s₇.mem B (slot w 1) w = _; rw [R1, hR2]) fun u I => ⟨[], u, .block rfl, ?_⟩
  obtain kk := k17.trans I.keep
  exact ⟨I.ctx.a7, I.ra, I.ctx.s5, I.ctx.t0, (kk.gpr (by decide)).trans h6, (kk.gpr (by decide)).trans h11,
    I.s9, I.s10⟩

/-- `recombineP`, in `p`'s working space (`B`, of 24 arrays, `p` odd in
array 0, `R² mod p` in array 1 and `m₁ < p` in array 4), with `X` at `s6`
(`BX`) apart from it, `m₂` in the first `w n` words of `X`'s array 6 (`n`
chunks of the `⌈k / 8⌉` words, `k` in `X`'s header) and `qInv < p` in its
array 7: `h = (m₁ - m₂ mod p) qInv mod p` in array 4, changing only arrays
1–23. -/
theorem recombineP_ok {s : State} {B BX : Addr} {Z ZX w wX k Pv m1 M2 QI : Nat}
    (hs : Scr s B Z) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (hZ : slot w 24 ≤ Z) (hZX : slot wX 8 ≤ ZX) (hwX : w ≤ wX) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h7 : s.gpr .a7 = off B (slot w 0)) (hra : s.gpr .ra = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hkw : Mont.word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hXZ : slot wX 6 + 8 * (w * Win.nChunks ((k + 7) / 8) w) ≤ ZX)
    (hP : wordsVal s.mem B (slot w 0) w = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hR2 : wordsVal s.mem B (slot w 1) w = 2 ^ (128 * w) % Pv)
    (hm1 : wordsVal s.mem B (slot w 4) w = m1) (hm1P : m1 < Pv)
    (hM2 : wordsVal s.mem BX (slot wX 6) (w * Win.nChunks ((k + 7) / 8) w) = M2)
    (hQ : wordsVal s.mem BX (slot wX 7) w = QI) (hQP : QI < Pv) :
    WP isa recombineP s fun t =>
      (wordsVal t.mem B (slot w 4) w = (m1 + Pv - M2 % Pv) % Pv * QI % Pv ∧
        Win.WinO B w s.mem t.mem ∧ t.gpr .a7 = off B (slot w 0)) ∧ Keep recPRegs s t := by
  have hnw := hs.nowrap
  have hnx := hx.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain e0 := e w 0; have e1 := e w 1; have e4 := e w 4; have e7 := e w 7; have e8 := e w 8
  obtain e9 := e w 9; have e10 := e w 10; have e24 := e w 24
  obtain x7 := e wX 7; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  obtain hfit : ∀ j < 24, slot w j + 8 * w ≤ 2 ^ 64 := fun j hj => by
    have := Win.slot_lt (w := w) hj; omega_arith
  -- What the arrays 1–23 of `P` leave alone in `X`.
  obtain xo : ∀ {m m' : Mem}, Win.WinO B w m m' → ∀ x, ofs BX x < ZX → m' x = m x := fun o x hx' =>
    o x (Or.inr (by have := hsep x hx'; omega_arith))
  obtain xw : ∀ {m m' : Mem}, Win.WinO B w m m' → wordsVal m' BX (slot wX 7) w = wordsVal m BX (slot wX 7) w :=
    fun o => wordsVal_of_words fun i hi => Mem.readW_congr fun j hj => xo o _ (by
      rw [ofs_off BX (d := slot wX 7 + 8 * i) (i := j) (by omega_arith)]; omega_arith)
  unfold recombineP
  refine recPA_ok hs hZ hw2 hw' h7 h5 ht0 hP hodd hm1 fun s₇ c7 k17 w07 R1 m9₇ => ?_
  -- `m₂ mod p` into array 4.
  refine WP.seq (WP.mono (Win.reduceIn_ok (k := k) (Cv := M2) c7 ((k17.gpr (by decide)).trans hra)
    (hx.congr k17.2.2) hsep ((k17.gpr (by decide)).trans h6) ((k17.gpr (by decide)).trans h11)
    (by rw [Outside.word_sep (Win.PFr.of_win w07) hsep (by omega_arith)
      (show oNLen + 8 ≤ ZX by unfold oNLen; omega_arith) hnx]; exact hkw) hk hk' hXZ hP2 hodd
    (by show wordsVal s₇.mem B (slot w 1) w = _
        rw [R1, hR2])
    (by rw [Win.x_wv' (Win.PFr.of_win w07) hsep (by omega_arith) hnx hXZ]; exact hM2))
    fun s₈ ⟨⟨c8, _, r8, p18, f8, o8⟩, k8⟩ => ?_)
  obtain k18 := k17.trans k8
  obtain w08 : Win.WinO B w s.mem s₈.mem := w07.trans o8
  obtain m9₈ : wordsVal s₈.mem B (slot w 9) w = m1 := by
    rw [show wordsVal s₈.mem B (slot w 9) w = Win.A s₈.mem B w 9 from rfl, f8 9 (by decide) (by decide),
      show Win.A s₇.mem B w 9 = wordsVal s₇.mem B (slot w 9) w from rfl, m9₇]
  -- `(m₁ + p - m₂ mod p) mod p` into array 3.
  refine seq4_then (recSub_ok (Pv := Pv) (m1 := m1) (r := M2 % Pv) c8.scr (by omega_arith) (by omega_arith) hw'
    c8.a7 ((k18.gpr (by decide)).trans hra) c8.s5 c8.t0 c8.n r8 m9₈
    (Nat.mod_lt _ (by omega_arith)) hm1P) fun s₉ ⟨⟨a9, r9, h79⟩, k9⟩ => ?_
  obtain k19 := k18.trans k9
  obtain u9 : ∀ j < 24, j ≠ 3 → j ≠ 9 → wordsVal s₉.mem B (slot w j) w = wordsVal s₈.mem B (slot w j) w :=
    fun j hj h3 h9 => Pub.arrays_V r9 (by simp; omega_arith) (hfit j hj)
  obtain w09 : Win.WinO B w s.mem s₉.mem := w08.trans (Win.win_of_arrays r9 (by decide))
  -- `h = a qInv mod p` into array 4.
  refine WP.mono (recMont_ok (a := (m1 + Pv - M2 % Pv) % Pv) (QI := QI) (hs.congr k19.2.2) (hx.congr k19.2.2)
    hsep (by omega_arith) hZX hwX hw2 hw' h79 (by rw [k9.gpr (by decide)]; exact c8.s5)
    (by rw [k9.gpr (by decide)]; exact c8.t0)
    ((k19.gpr (by decide)).trans h6) ((k19.gpr (by decide)).trans h11) ?_
    (by rw [u9 0 (by decide) (by decide) (by decide)]; exact c8.n) hodd a9 ?_
    (by rw [xw w09]; exact hQ) hQP) fun t ⟨⟨ht4, rt⟩, kt⟩ =>
      ⟨⟨ht4, w09.trans (Win.win_of_arrays rt (by decide)), ?_⟩, (k19.trans kt).mono (by decide)⟩
  · rw [show Mont.word s₉.mem B (slot w 0) = Mont.word s₈.mem B (slot w 0) from
      r9.word0_of_not_mem (by decide) (by decide) (by omega_arith) (by omega_arith), k9.gpr (by decide)]
    exact c8.inv
  · rw [u9 1 (by decide) (by decide) (by decide), show wordsVal s₈.mem B (slot w 1) w = Win.A s₈.mem B w 1 from rfl,
      p18, show Win.A s₇.mem B w 1 = wordsVal s₇.mem B (slot w 1) w from rfl, R1, hR2,
      ← Nat.pow_add]
    congr 2; omega_arith
  · rw [kt.gpr (by decide)]; exact h79

/-! ## `recombineX` -/

/-- A number of `w` words, zero-extended to `W`. -/
theorem wordsVal_widen {m m' : Mem} {B B' : Addr} : ∀ {d d' w W : Nat},
    (∀ i < w, Mont.word m B (d + 8 * i) = Mont.word m' B' (d' + 8 * i)) →
    (∀ i, w ≤ i → i < W → Mont.word m B (d + 8 * i) = 0) → w ≤ W → wordsVal m B d W = wordsVal m' B' d' w
  | d, _, 0, W, _, hz, _ => ModArith.ma_wordsVal_zero fun i hi => hz i (Nat.zero_le _) hi
  | d, d', w + 1, W + 1, h, hz, hw => by
    obtain h0 := h 0 (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    simp only [wordsVal]
    rw [h0, wordsVal_widen (d := d + 8) (d' := d' + 8) (w := w) (W := W)
      (fun i hi => by
        have := h (i + 1) (by omega_using [hi])
        rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega_using [], show d' + 8 * (i + 1) = d' + 8 + 8 * i by omega_using []] at this)
      (fun i h1 h2 => by
        have := hz (i + 1) (by omega_using [h1]) (by omega_using [h2])
        rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega_using []] at this) (by omega_using [hw])]
  | _, _, _ + 1, 0, _, _, hw => absurd hw (by omega_using [])

theorem wX_val {W : Nat} (h : W < 2 ^ 31) :
    (BitVec.ofNat 64 (8 * (W + 2)) - BitVec.ofNat 64 16) >>> 3 = BitVec.ofNat 64 W := by
  rw [show BitVec.ofNat 64 (8 * (W + 2)) - BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * W) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith, ofNat_shr3 _ (by omega_arith)]
  congr 1; omega_using []

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
  obtain wb := wordsOf_bounds hl1 hl'
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain p4 := e (wordsOf l) 4; have p8 := e (wordsOf l) 8
  obtain xj8 := slot_le (w := wX) hxj
  obtain xal := slot_al8 wX xj
  obtain x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  unfold widen
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (setupP_ok hx (h6.trans (BitVec.add_zero S).symm) hB hB8 hB' hL hL8 hL' hbase hlen hl1 hl')
    fun s₁ ⟨⟨a7, _, a5, a0, _, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .s9) (by decide) a7 a5 4) fun s₂ ⟨⟨b9, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (WP.keep [.s8] (Q := fun s₃ => s₃.gpr .s8 = BitVec.ofNat 64 (wordsOf l) ∧ s₃.mem = s₂.mem) ?_
    (by rfl) (by rfl)) fun s₃ ⟨⟨b8, m3⟩, k3⟩ => ?_
  · brun [(k2.gpr (by decide)).trans a0, add_ofNat_zero]
  obtain k13 := k12.trans k3
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k13.gpr (by decide)).trans h6) ((k13.gpr (by decide)).trans h11)
    xj) fun s₄ ⟨⟨b3, m4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  refine WP.mono (WP.keep [.t0] (Q := fun s₅ => s₅.gpr .t0 = BitVec.ofNat 64 wX ∧ s₅.mem = s₄.mem) ?_
    (by rfl) (by rfl)) fun s₅ ⟨⟨c0, m5⟩, k5⟩ => ?_
  · simp only [Crt.wX]
    brun [(k14.gpr (by decide)).trans h11, wX_val hwX']
  obtain k15 := k14.trans k5
  obtain m05 : s₅.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  refine WP.seq (WP.mono (zeroWords_ok (d := slot wX xj) (hx.congr k15.2.2) ((k5.gpr (by decide)).trans b3) c0
    (by omega_arith) hwX' (by omega_arith) (by omega_arith)) fun s₆ ⟨⟨_, hz, o6⟩, k6⟩ => ?_)
  obtain k16 := k15.trans k6
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k16.gpr (by decide)).trans h6) ((k16.gpr (by decide)).trans h11)
    xj) fun s₇ ⟨⟨d3, m7⟩, k7⟩ => ?_
  refine WP.mono (WP.keep [.t4, .t0] (Q := fun s₈ => s₈.gpr .t4 = off Bp (slot (wordsOf l) 4) ∧
      s₈.gpr .t0 = BitVec.ofNat 64 (wordsOf l) ∧ s₈.mem = s₇.mem) ?_ (by rfl) (by rfl)) fun s₈ ⟨⟨d4, d0, m8⟩, k8⟩ => ?_
  · brun [((((k3.trans k4).trans k5).trans k6).trans k7).gpr (r := .s9) (by decide) |>.trans b9,
      ((((k4.trans k5).trans k6).trans k7)).gpr (r := .s8) (by decide) |>.trans b8, add_ofNat_zero]
  obtain k18 := (k16.trans k7).trans k8
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
  obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega_using [hW]⟩
  simp only [wordsVal] at h
  have hp : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
  obtain hw := (Mont.word m B d).isLt
  rw [show 64 * (k + 1) = 64 + 64 * k by omega_using [], Nat.pow_add] at h
  have := Nat.mul_le_mul_left (2 ^ 64) hp
  omega_arith

/-- Montgomery multiplication modulo `M = R - 1`, `R ≡ 1`: the product,
when it is below `M`. -/
theorem mont_ones {R x a : Nat} (hR : 2 ≤ R - 1) (hx : x < R - 1) (h : x * R % (R - 1) = a % (R - 1))
    (ha : a < R - 1) : x = a := by
  obtain e : x * R = x + (R - 1) * x := by
    rw [show x * R = x * (R - 1) + x by
      rw [← Nat.mul_add_one, show R - 1 + 1 = R by omega_using [hR]], Nat.add_comm, Nat.mul_comm]
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
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain x0 := e wX 0; have x4 := e wX 4; have x6 := e wX 6; have x7 := e wX 7; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  obtain hfit : ∀ j < 8, slot wX j + 8 * wX ≤ 2 ^ 64 := fun j hj => by
    have := slot_le (w := wX) hj; omega_arith
  obtain hR : 2 ≤ 2 ^ (64 * wX) - 1 := by
    have : 2 ^ 64 ≤ 2 ^ (64 * wX) := Nat.pow_le_pow_right (by decide) (by omega_using [hw2])
    omega_arith
  unfold recombineX
  -- `h` into array 7.
  obtain hoff : ∀ o, o + 8 ≤ 256 → o + 8 ≤ ZX := fun o ho => by omega_arith
  refine WP.seq (WP.mono (widen_ok (xj := 7) hx hp sepP h6 h11 (hoff _ (by decide)) (by decide) (by decide)
    (hoff _ (by decide)) (by decide) (by decide) hbP hlP hp1 hp' (by decide) hZX hZP hwP hw') fun s₁ ⟨⟨v7, o1⟩, k1⟩ => ?_)
  obtain hd : ∀ {d}, d + 8 ≤ 256 → Mont.word s₁.mem S d = Mont.word s.mem S d := fun hd' =>
    Mont.Outside.word o1 (Or.inl (by omega_arith)) (by omega_arith)
  -- `m₂` into array 6.
  refine WP.seq (WP.mono (widen_ok (xj := 6) (hx.congr k1.2.2) (hq.congr k1.2.2) sepQ ((k1.gpr (by decide)).trans h6)
    ((k1.gpr (by decide)).trans h11) (hoff _ (by decide)) (by decide) (by decide) (hoff _ (by decide)) (by decide)
    (by decide) ((hd (by decide)).trans hbQ) ((hd (by decide)).trans hlQ) hq1 hq' (by decide) hZX hZQ hwQ hw')
    fun s₂ ⟨⟨v6, o2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  obtain r1 : Arrays S wX [7] s.mem s₁.mem := Arrays.of_outside (j := 7) (by simp) o1 (Nat.le_refl _) (by omega_arith)
  obtain r2 : Arrays S wX [6] s₁.mem s₂.mem := Arrays.of_outside (j := 6) (by simp) o2 (Nat.le_refl _) (by omega_arith)
  obtain mq : wordsVal s₁.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) = wordsVal s.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) :=
    wordsVal_of_words fun i hi => Pub.Outside.word_apart o1 sepQ (by omega_arith)
      (by have := slot_le (w := wordsOf lq) (show 4 < 8 by decide); omega_arith) hnq
  rw [mq] at v6
  obtain v7' : wordsVal s₂.mem S (slot wX 7) wX = wordsVal s.mem BP (slot (wordsOf lp) 4) (wordsOf lp) :=
    (Pub.arrays_V r2 (j := 7) (by decide) (hfit 7 (by decide))).trans v7
  obtain r12 : Arrays S wX [6, 7] s.mem s₂.mem := (r1.mono (by simp)).trans (r2.mono (by simp))
  obtain m0 : wordsVal s₂.mem S (slot wX 0) wX = 2 ^ (64 * wX) - 1 :=
    (Pub.arrays_V r12 (j := 0) (by decide) (hfit 0 (by decide))).trans hM
  obtain q5 : wordsVal s₂.mem S (slot wX 5) wX = qv :=
    (Pub.arrays_V r12 (j := 5) (by decide) (hfit 5 (by decide))).trans h5
  -- `X`'s registers, `t1 := 1 = -M⁻¹ mod 2⁶⁴`.
  obtain e0' : slot wX 0 = hdrBytes := by simp [slot]
  refine WP.seq (WP.mono (WP.keep [.a7, .ra, .s5, .t0, .t1] (Q := fun s₃ => s₃.gpr .a7 = off S (slot wX 0) ∧
      s₃.gpr .s5 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ s₃.gpr .t0 = BitVec.ofNat 64 wX ∧ s₃.gpr .t1 = 1 ∧
      s₃.mem = s₂.mem) ?_ (by rfl) (by rfl)) fun s₃ ⟨⟨c7, c5, c0, c1, m3⟩, k3⟩ => ?_)
  · simp only [Crt.wX]
    rw [e0']
    brun [exec_addi_nat (show hdrBytes < 2048 by decide), (k12.gpr (r := .s6) (by decide)).trans h6,
      (k12.gpr (r := .s11) (by decide)).trans h11, add_ofNat_zero, wX_val hw', r2_exec_li_one]
  obtain k13 := k12.trans k3
  rw [← m3] at m0 q5 v7' v6
  -- `q h mod M = q h` into array 4.
  obtain w0 : (Mont.word s₃.mem S (slot wX 0)).toNat = 2 ^ 64 - 1 := word0_ones (by omega_using [hw2]) m0
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hx.congr k13.2.2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZX c7 c5 c0
    (by rw [show (word s₃.mem S (slot wX 0)).toNat = 2 ^ 64 - 1 from w0, c1]; decide)
    (by rw [v7', m0]; exact hH)) fun s₄ ⟨⟨x4P, x4R, r4⟩, k4⟩ => ?_)
  obtain k14 := k13.trans k4
  rw [m0] at x4P
  rw [m0, q5, v7'] at x4R
  obtain x4 : wordsVal s₄.mem S (slot wX 4) wX = qv * wordsVal s.mem BP (slot (wordsOf lp) 4) (wordsOf lp) :=
    mont_ones hR x4P x4R (by omega_arith)
  obtain v6' : wordsVal s₄.mem S (slot wX 6) wX = wordsVal s.mem BQ (slot (wordsOf lq) 4) (wordsOf lq) :=
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
  obtain k17 := ((k14.trans k5).trans k6).trans k7
  obtain m47 : s₇.mem = s₄.mem := by rw [m7, m6, m5]
  refine WP.mono (ModArith.addMask64_ok (b := true) (dT := slot wX 4) (dM := slot wX 6) (hx.congr k17.2.2)
    ((k6.trans k7).gpr (by decide) |>.trans b3) ((k7.gpr (by decide)).trans b4) ((((k4.trans k5).trans k6).trans k7).gpr (by decide) |>.trans c0)
    b5 (slot_al8 _ _) (slot_al8 _ _) (by omega_using [hw2]) hw' (by omega_arith) (by omega_arith) (Or.inl (by omega_arith)))
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
  obtain e0' : slot wX 0 = hdrBytes := by simp [slot]
  obtain z : off S 0 = S := BitVec.add_zero S
  obtain hO' : s.mem.readW S 64 = O := by rw [← z]; exact hO
  obtain l0 : InRegions (s.rd ++ s.wr) S 8 := by rw [← z]; exact hx.ld (by omega_arith)
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

/-! ## The blocks that load the header's words -/

/-- `widen`'s first block: the prime's working space's registers, its array 4
in `s9`, its words in `s8`, `X`'s array `xj` in `t3` and `W` in `t0`. -/
theorem wd1_ok {s : State} {S Bp : Addr} {ZX wX l oB oLen xj : Nat} (hx : Scr s S ZX)
    (h6 : s.gpr .s6 = S) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hB : oB + 8 ≤ ZX) (hB8 : oB % 8 = 0) (hB' : oB < 2048) (hL : oLen + 8 ≤ ZX) (hL8 : oLen % 8 = 0)
    (hL' : oLen < 2048) (hbase : Mont.word s.mem S oB = Bp) (hlen : Mont.word s.mem S oLen = BitVec.ofNat 64 l)
    (hl1 : 1 ≤ l) (hl' : l ≤ 1024) (hwX' : wX < 2 ^ 31) :
    WP isa (.block (setupP oB oLen ++ base .s9 4 ++ ([.addi .s8 .t0 0] : List Instr) ++ xb .t3 xj ++ Crt.wX)) s fun t =>
      (t.gpr .a7 = off Bp (slot (wordsOf l) 0) ∧ t.gpr .ra = off Bp (slot (wordsOf l) 0) ∧
        t.gpr .s5 = BitVec.ofNat 64 (8 * (wordsOf l + 2)) ∧ t.gpr .s9 = off Bp (slot (wordsOf l) 4) ∧
        t.gpr .s8 = BitVec.ofNat 64 (wordsOf l) ∧ t.gpr .t3 = off S (slot wX xj) ∧ t.gpr .t0 = BitVec.ofNat 64 wX) ∧
      Keep widenRegs s t := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (setupP_ok hx (h6.trans (BitVec.add_zero S).symm) hB hB8 hB' hL hL8 hL' hbase hlen hl1 hl')
    fun s₁ ⟨⟨a7, ara, a5, a0, _, _⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .s9) (by decide) a7 a5 4) fun s₂ ⟨⟨b9, _⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (WP.keep [.s8] (Q := fun s₃ => s₃.gpr .s8 = BitVec.ofNat 64 (wordsOf l)) ?_
    (by rfl) (by rfl)) fun s₃ ⟨b8, k3⟩ => ?_
  · brun [(k2.gpr (by decide)).trans a0, add_ofNat_zero]
  obtain k13 := k12.trans k3
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k13.gpr (by decide)).trans h6) ((k13.gpr (by decide)).trans h11)
    xj) fun s₄ ⟨⟨b3, _⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  refine WP.mono (WP.keep [.t0] (Q := fun s₅ => s₅.gpr .t0 = BitVec.ofNat 64 wX) ?_
    (by rfl) (by rfl)) fun s₅ ⟨c0, k5⟩ => ?_
  · simp only [Crt.wX]
    brun [(k14.gpr (by decide)).trans h11, wX_val hwX']
  obtain k15 := k14.trans k5
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, c0⟩, k15.mono (by decide)⟩
  · rw [(k2.trans (k3.trans (k4.trans k5))).gpr (by decide)]; exact a7
  · rw [(k2.trans (k3.trans (k4.trans k5))).gpr (by decide)]; exact ara
  · rw [(k2.trans (k3.trans (k4.trans k5))).gpr (by decide)]; exact a5
  · rw [(k3.trans (k4.trans k5)).gpr (by decide)]; exact b9
  · rw [(k4.trans k5).gpr (by decide)]; exact b8
  · rw [k5.gpr (by decide)]; exact b3

/-- The block before `output`: `X`'s array 0 and arrays' size, `out`, its
length and the mask. -/
theorem fin1_ok {s : State} {S O : Addr} {ZX wX k : Nat} (hx : Scr s S ZX)
    (h6 : s.gpr .s6 = S) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hO : Mont.word s.mem S oOut = O) (hk : Mont.word s.mem S oNLen = BitVec.ofNat 64 k) (hZX : 96 ≤ ZX) :
    WP isa (.block [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut,
        .load .d .s11 .s6 oNLen, .load .d .s9 .s6 oMask]) s fun t =>
      (t.gpr .a7 = off S (slot wX 0) ∧ t.gpr .s5 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ t.gpr .s10 = off O 0 ∧
        t.gpr .s11 = BitVec.ofNat 64 k ∧ t.gpr .s6 = S) ∧ Keep [.a7, .s5, .s10, .s11, .s9] s t := by
  have hh : hdrBytes = 256 := rfl
  obtain e0' : slot wX 0 = hdrBytes := by simp [slot]
  obtain z : off S 0 = S := BitVec.add_zero S
  obtain hO' : s.mem.readW S 64 = O := by rw [← z]; exact hO
  obtain l0 : InRegions (s.rd ++ s.wr) S 8 := by rw [← z]; exact hx.ld (by omega_arith)
  have hk' : s.mem.readW (off S 16) 64 = BitVec.ofNat 64 k := hk
  refine WP.keep [.a7, .s5, .s10, .s11, .s9] (Q := fun s₁ => s₁.gpr .a7 = off S (slot wX 0) ∧
      s₁.gpr .s5 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ s₁.gpr .s10 = off O 0 ∧ s₁.gpr .s11 = BitVec.ofNat 64 k ∧
      s₁.gpr .s6 = S) ?_ (by rfl) (by rfl)
  rw [e0']
  brun [exec_addi_nat (show hdrBytes < 2048 by decide), h6, h11, add_ofNat_zero, oOut, oNLen, oMask,
    l0, hx.al, hx.ld (show 16 + 8 ≤ ZX by omega_arith), hx.al8 (show 16 + 8 ≤ ZX by omega_arith) (by decide),
    hx.ld (show 88 + 8 ≤ ZX by omega_arith), hx.al8 (show 88 + 8 ≤ ZX by omega_arith) (by decide), hO', hk']

end VG.Proof.Bignum.RISCV64.Crt

end

end

/-!
# The RSA private-key operation on RISC-V: the recombination

`mid2_ok`: from the powers (`M1`), `m₂` into `X`'s array 6, `h = (m₁ - m₂)
qInv mod p` in `p`'s working space, `q h + m₂` in `X`, and it written to
`out` under the mask.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays Frm)
open VG.Impl.Bignum.RISCV64.PublicChecked (output)

theorem off_off' (S : Addr) (a i : Nat) : Mont.off (Mont.off S a) i = Mont.off S (a + i) := by
  simp only [Mont.off, BitVec.add_assoc, BitVec.ofNat_add]

/-- `h` and the result. -/
abbrev vh (s₀ : State) : Nat := (vm1 s₀ + mP s₀ - vm2 s₀ % mP s₀) % mP s₀ * mQI s₀ % mP s₀
abbrev vr (s₀ : State) : Nat := if cb s₀ then mQ s₀ * vh s₀ + vm2 s₀ else 0

/-- After `widen` and `setupP`: `m₂` in `X`'s array 6, `p`'s working
space's registers. -/
structure Y2 (s₀ s t : State) : Prop where
  s6 : t.gpr .s6 = cS s₀
  s11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  R : PR s₀ (oPa s₀) (cpL s₀) t
  x0 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 0) (cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  x5 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 5) (cwX s₀) = mQ s₀
  x7 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 7) (cwX s₀) = mQI s₀
  p0 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (cwP s₀) = mP s₀
  p4 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (cwP s₀) = vm1 s₀
  p1 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 1) (cwP s₀) = 2 ^ (128 * cwP s₀) % mP s₀
  q4 : wordsVal t.mem (Mont.off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (cwQ s₀) = vm2 s₀
  x6 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vm2 s₀
  msk : Mont.word t.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  fr : Frm (cS s₀) (midR (cZ s₀)) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- After `recombineP`: `h` in `p`'s array 4. -/
structure Y3 (s₀ s t : State) : Prop where
  s6 : t.gpr .s6 = cS s₀
  s11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x0 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 0) (cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  x5 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 5) (cwX s₀) = mQ s₀
  h4 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (cwP s₀) = vh s₀
  q4 : wordsVal t.mem (Mont.off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (cwQ s₀) = vm2 s₀
  msk : Mont.word t.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  fr : Frm (cS s₀) (midR (cZ s₀)) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- After `recombineX`: `q h + m₂` in `X`'s array 4. -/
structure Y4 (s₀ s t : State) : Prop where
  s6 : t.gpr .s6 = cS s₀
  s11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x4 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 4) (cwX s₀) = mQ s₀ * vh s₀ + vm2 s₀
  msk : Mont.word t.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  fr : Frm (cS s₀) (midR (cZ s₀)) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem m2A_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (M : M1 s₀ s t) (hc : ∀ u, Y2 s₀ s u → u.gpr .t2 = BitVec.ofNat 64 (wordsOf (cpL s₀)) → WP isa c u Q) :
    WP isa (.seq (widen oBQ oQLen 6) (.seq (.block (setupP oBP oPLen)) c)) t Q := by
  have hn := hP.nw
  have room := hP.room
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  obtain eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eX2 := e (cwX s₀) 2
  obtain eP0 := e (cwP s₀) 0; have eP1 := e (cwP s₀) 1; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  obtain eP24 := e (cwP s₀) 24
  obtain eQ0 := e (cwQ s₀) 0; have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ24 := e (cwQ s₀) 24
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  obtain fP8 := e (wordsOf (cpL s₀)) 8; have fQ8 := e (wordsOf (cqL s₀)) 8
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
  have hwP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have hwQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  obtain hwPK : cwP s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  obtain hwQK : cwQ s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  obtain hpw : cpL s₀ ≤ 8 * cwP s₀ := by have := wordsOf_ge (l := cpL s₀); omega_arith
  obtain hqw : cqL s₀ ≤ 8 * cwQ s₀ := by have := wordsOf_ge (l := cqL s₀); omega_arith
  obtain hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  obtain hZ256 : 256 ≤ cZ s₀ := by omega_arith
  have hm : oMask = 88 := rfl
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQIP, mQIb⟩ := masked_facts hP
  have k0 := hF.keep
  obtain hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (Nat.le_of_lt mQb)
  obtain hd : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid M.fr hZ256 hd
  obtain hS : Scr t (cS s₀) (cZ s₀) := hF.scr.congr M.keep.2.2
  -- `m₂` into `X`'s array 6, zero-extended.
  refine WP.seq (WP.mono (widen_ok (xj := 6) (l := cqL s₀) (Scr.le hS (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
    (Scr.sub hS (show oQa s₀ + slot (cwQ s₀) 24 ≤ cZ s₀ by omega_arith)
      (by have := slot_al (cwX s₀) 8; have := slot_al (cwP s₀) 24; omega_arith) (by omega_arith))
    (sepBX (by omega_arith) (by omega_arith) (by omega_arith)) M.s6 M.s11
    (by unfold oBQ; omega_arith) (by decide) (by decide) (by unfold oQLen; omega_arith) (by decide) (by decide)
    ((hd _ (by unfold oBQ; omega_arith)).trans hF.hBQ) ((hd _ (by unfold oQLen; omega_arith)).trans hF.hQL)
    q1 (by omega_arith) (by decide) (by omega_arith) (by omega_arith) (by omega_arith) hwX)
    fun t₁ ⟨⟨hx6, O1⟩, k1⟩ => ?_)
  obtain hx6' : wordsVal t₁.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vm2 s₀ := hx6.trans M.q4
  obtain hd1 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₁.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d h' => by rw [Mont.Outside.word O1 (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d h'
  obtain k01 := M.keep.trans k1
  -- `p`'s working space again.
  refine WP.seq (WP.mono (setupP_ok (l := cpL s₀) (Bp := Mont.off (cS s₀) (oPa s₀)) (hF.scr.congr k01.2.2)
    (by rw [k1.gpr (by decide), M.s6]; exact z0 _) (by unfold oBP; omega_arith) (by decide) (by decide)
    (by unfold oPLen; omega_arith) (by decide) (by decide) (by rw [hd1 _ (by unfold oBP; omega_arith)]; exact hF.hBP)
    (by rw [hd1 _ (by unfold oPLen; omega_arith)]; exact hF.hPL) p1 (by omega_arith))
    fun t₂ ⟨⟨p7, pra, p5, p0', _, m2⟩, k2⟩ => ?_)
  obtain k02 := k01.trans k2
  obtain pv : ∀ j, j + 1 ≤ 24 → wordsVal t₂.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) j) (cwP s₀) =
      wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) j) (cwP s₀) := fun j hj => by
    have := Win.slot_lt (w := cwP s₀) (show j < 24 by omega_arith)
    rw [m2, wordsVal_off, wordsVal_off, Mont.Outside.wordsVal O1 (Or.inr (by omega_arith)) (by omega_arith)]
  obtain xv : ∀ j, j < 8 → j ≠ 6 → wordsVal t₂.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) =
      wordsVal t.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) := fun j hj h1 => by
    have := VG.Proof.Bignum.slot_le (w := cwX s₀) hj
    have := VG.Proof.Bignum.slot_sep (w := cwX s₀) h1
    rw [m2, Mont.Outside.wordsVal O1 (by omega_arith) (by omega_arith)]
  refine hc t₂ ⟨(k02.gpr (by decide)).trans hF.s6, (k02.gpr (by decide)).trans hF.s11, ⟨p7, pra, p5, p0'⟩,
    by rw [xv 0 (by decide) (by decide)]; exact M.x0, by rw [xv 5 (by decide) (by decide)]; exact M.x5,
    by rw [xv 7 (by decide) (by decide)]; exact M.x7, by rw [pv 0 (by decide)]; exact M.p0,
    by rw [pv 4 (by decide)]; exact M.p4, by rw [pv 1 (by decide)]; exact M.p1, ?_, by rw [m2]; exact hx6', ?_,
    M.fr.trans (frm_mid (by rw [m2] at *; exact O1) (by omega_arith) (by omega_arith)), k02.2.1,
    k02.2.2⟩ (by assumption)
  · rw [m2, wordsVal_off, Mont.Outside.wordsVal O1 (Or.inr (by omega_arith)) (by omega_arith), ← wordsVal_off]
    exact M.q4
  · rw [m2, Mont.Outside.word O1 (Or.inl (by omega_arith)) (by omega_arith)]; exact M.msk

theorem m2B_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (Y : Y2 s₀ s t) (hc : ∀ u, Y3 s₀ s u → WP isa c u Q) : WP isa (.seq recombineP c) t Q := by
  have hn := hP.nw
  have room := hP.room
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  obtain eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eX2 := e (cwX s₀) 2
  obtain eP0 := e (cwP s₀) 0; have eP1 := e (cwP s₀) 1; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  obtain eP24 := e (cwP s₀) 24
  obtain eQ0 := e (cwQ s₀) 0; have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ24 := e (cwQ s₀) 24
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  obtain fP8 := e (wordsOf (cpL s₀)) 8; have fQ8 := e (wordsOf (cqL s₀)) 8
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
  have hwP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have hwQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  obtain hwPK : cwP s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  obtain hwQK : cwQ s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  obtain hpw : cpL s₀ ≤ 8 * cwP s₀ := by have := wordsOf_ge (l := cpL s₀); omega_arith
  obtain hqw : cqL s₀ ≤ 8 * cwQ s₀ := by have := wordsOf_ge (l := cqL s₀); omega_arith
  obtain hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  obtain hZ256 : 256 ≤ cZ s₀ := by omega_arith
  have hm : oMask = 88 := rfl
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQIP, mQIb⟩ := masked_facts hP
  have k0 := hF.keep
  obtain hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (Nat.le_of_lt mQb)
  obtain hd : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid Y.fr hZ256 hd
  obtain hS2 : Scr t (cS s₀) (cZ s₀) := hF.scr.congr Y.wr
  obtain hK : 1 ≤ (ck s₀ + 7) / 8 := by omega_arith
  obtain n1 := Win.le_nChunks_mul (K := (ck s₀ + 7) / 8) (w := cwP s₀) (by omega_arith)
  obtain n2 := Win.nChunks_mul_lt (K := (ck s₀ + 7) / 8) (w := cwP s₀) (by omega_arith) hK
  rw [Nat.mul_comm] at n1 n2
  obtain hm2K : vm2 s₀ < 2 ^ (64 * ((ck s₀ + 7) / 8)) :=
    Nat.lt_of_lt_of_le hm2b (pow256_le (by omega_arith))
  refine WP.seq (WP.mono (recombineP_ok (Pv := mP s₀) (m1 := vm1 s₀) (QI := mQI s₀) (k := ck s₀) (M2 := vm2 s₀)
    (Scr.sub hS2 (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith) (slot_al _ _) (by omega_arith))
    (Scr.le hS2 (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
    (sepXB (Nat.le_refl _) (by omega_arith) (by omega_arith)) (Nat.le_refl _) (Nat.le_refl _) (by omega_arith) hwP2
    (by omega_arith) Y.R.a7 Y.R.ra Y.R.s5 Y.R.t0 Y.s6 Y.s11
    ((hd _ (by unfold oNLen; omega_arith)).trans hF.hNL) (by omega_arith) (by omega_arith) (by omega_arith)
    Y.p0 mP1 mPo Y.p1 Y.p4 (Nat.mod_lt _ (by omega_arith))
    (wordsVal_trunc Y.x6 (Nat.lt_of_lt_of_le hm2K (Nat.pow_le_pow_right (by decide) (by omega_arith)))
      (by omega_arith))
    (wordsVal_trunc Y.x7 (Nat.lt_of_lt_of_le mQIb (pow256_le hpw)) (by omega_arith)) mQIP)
    fun t₃ ⟨⟨h4, O3, _⟩, k3⟩ => ?_)
  obtain O3' : Mont.Outside (cS s₀) (oPa s₀ + slot (cwP s₀) 1) (23 * (8 * (cwP s₀ + 2))) t.mem t₃.mem :=
    out_reb O3 (by omega_arith) (by omega_arith)
  obtain xv3 : ∀ j, j < 8 → wordsVal t₃.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) =
      wordsVal t.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) := fun j hj => by
    have := VG.Proof.Bignum.slot_le (w := cwX s₀) hj
    rw [Mont.Outside.wordsVal O3' (Or.inl (by omega_arith)) (by omega_arith)]
  refine hc t₃ ⟨(k3.gpr (by decide)).trans Y.s6, (k3.gpr (by decide)).trans Y.s11,
    by rw [xv3 0 (by decide)]; exact Y.x0, by rw [xv3 5 (by decide)]; exact Y.x5, h4, ?_, ?_,
    Y.fr.trans (frm_mid O3' (by omega_arith) (by omega_arith)), k3.2.1.trans Y.rd, k3.2.2.trans Y.wr⟩
  · rw [wordsVal_off, Mont.Outside.wordsVal O3' (Or.inr (by omega_arith)) (by omega_arith), ← wordsVal_off]
    exact Y.q4
  · rw [Mont.Outside.word O3' (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.msk

theorem m2C_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (Y : Y3 s₀ s t) (hc : ∀ u, Y4 s₀ s u → WP isa c u Q) : WP isa (.seq recombineX c) t Q := by
  have hn := hP.nw
  have room := hP.room
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  obtain eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eX2 := e (cwX s₀) 2
  obtain eP0 := e (cwP s₀) 0; have eP1 := e (cwP s₀) 1; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  obtain eP24 := e (cwP s₀) 24
  obtain eQ0 := e (cwQ s₀) 0; have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ24 := e (cwQ s₀) 24
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  obtain fP8 := e (wordsOf (cpL s₀)) 8; have fQ8 := e (wordsOf (cqL s₀)) 8
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
  have hwP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have hwQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  obtain hwPK : cwP s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  obtain hwQK : cwQ s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  obtain hpw : cpL s₀ ≤ 8 * cwP s₀ := by have := wordsOf_ge (l := cpL s₀); omega_arith
  obtain hqw : cqL s₀ ≤ 8 * cwQ s₀ := by have := wordsOf_ge (l := cqL s₀); omega_arith
  obtain hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  obtain hZ256 : 256 ≤ cZ s₀ := by omega_arith
  have hm : oMask = 88 := rfl
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQIP, mQIb⟩ := masked_facts hP
  have k0 := hF.keep
  obtain hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (Nat.le_of_lt mQb)
  obtain hd3 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid Y.fr hZ256 hd
  obtain hS3 : Scr t (cS s₀) (cZ s₀) := hF.scr.congr Y.wr
  obtain hvh : vh s₀ < mP s₀ := Nat.mod_lt _ (by omega_arith)
  obtain hm2Q : vm2 s₀ < mQ s₀ := Nat.mod_lt _ (by omega_arith)
  obtain hPQ : mQ s₀ * mP s₀ < 2 ^ (64 * cwX s₀) - 1 := by
    rw [Nat.mul_comm]; exact pq_lt mPb mQb pk qk (by omega_arith)
  obtain hlt : mQ s₀ * vh s₀ + vm2 s₀ < mQ s₀ * mP s₀ := by
    have := Nat.mul_le_mul_left (mQ s₀) (show vh s₀ + 1 ≤ mP s₀ by omega_arith)
    rw [Nat.mul_succ] at this; omega_arith
  obtain hvP : vh s₀ < mQ s₀ * mP s₀ := Nat.lt_of_lt_of_le hvh (Nat.le_mul_of_pos_left _ (by omega_arith))
  refine WP.seq (WP.mono (recombineX_ok (lp := cpL s₀) (lq := cqL s₀) (qv := mQ s₀)
    (Scr.le hS3 (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
    (Scr.sub hS3 (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith) (slot_al _ _) (by omega_arith))
    (Scr.sub hS3 (show oQa s₀ + slot (cwQ s₀) 24 ≤ cZ s₀ by omega_arith)
      (by have := slot_al (cwX s₀) 8; have := slot_al (cwP s₀) 24; omega_arith) (by omega_arith))
    (sepBX (Nat.le_refl _) (by omega_arith) (by omega_arith)) (sepBX (by omega_arith) (by omega_arith) (by omega_arith))
    Y.s6 Y.s11 (Nat.le_refl _) (by omega_arith) hwX
    ((hd3 _ (by unfold oBP; omega_arith)).trans hF.hBP) ((hd3 _ (by unfold oPLen; omega_arith)).trans hF.hPL)
    ((hd3 _ (by unfold oBQ; omega_arith)).trans hF.hBQ) ((hd3 _ (by unfold oQLen; omega_arith)).trans hF.hQL)
    p1 (by omega_arith) q1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    Y.x0 Y.x5
    (by
      have e1 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (wordsOf (cpL s₀)) 4) (wordsOf (cpL s₀)) = vh s₀ := Y.h4
      rw [e1]; omega_arith)
    (by
      have e1 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (wordsOf (cpL s₀)) 4) (wordsOf (cpL s₀)) = vh s₀ := Y.h4
      have e2 : wordsVal t.mem (Mont.off (cS s₀) (oQa s₀)) (slot (wordsOf (cqL s₀)) 4) (wordsOf (cqL s₀)) =
        vm2 s₀ := Y.q4
      rw [e1, e2]; omega_arith))
    fun t₄ ⟨⟨x4, A4⟩, k4⟩ => ?_)
  rw [Y.h4, Y.q4] at x4
  refine hc t₄ ⟨(k4.gpr (by decide)).trans Y.s6, (k4.gpr (by decide)).trans Y.s11, x4, ?_,
    Y.fr.trans (frm_mid_chk (frm_arrs A4 fun j hj => by simp at hj; omega_arith) (by omega_arith)),
    k4.2.1.trans Y.rd, k4.2.2.trans Y.wr⟩
  rw [show Mont.word t₄.mem (cS s₀) oMask = Mont.word t.mem (cS s₀) oMask from A4.word_eq (fun j hj => Or.inl (by
      have := VG.Proof.Bignum.hdr_lt_slot (cwX s₀) j (i := 11) (by decide); omega_arith)) (by omega_arith)]
  exact Y.msk

/-- The block before `output`. -/
abbrev finBlk : List Instr := [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut,
  .load .d .s11 .s6 oNLen, .load .d .s9 .s6 oMask]

theorem m2D_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (Y : Y4 s₀ s t)
    (hc : ∀ u, Spec.Rsa.bytesAt u.mem (s₀.gpr .a0) (ck s₀) = Spec.Rsa.i2osp (vr s₀) (ck s₀) →
      u.gpr .a0 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) →
      (∀ i < 13, u.mem.readW (Mont.off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)) →
      u.gpr .s6 = cS s₀ → u.wr = s₀.wr → WP isa c u Q) :
    WP isa (.seq (.block finBlk) (.seq output c)) t Q := by
  have hn := hP.nw
  have room := hP.room
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  obtain eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eX2 := e (cwX s₀) 2
  obtain eP0 := e (cwP s₀) 0; have eP1 := e (cwP s₀) 1; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  obtain eP24 := e (cwP s₀) 24
  obtain eQ0 := e (cwQ s₀) 0; have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ24 := e (cwQ s₀) 24
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  obtain fP8 := e (wordsOf (cpL s₀)) 8; have fQ8 := e (wordsOf (cqL s₀)) 8
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
  have hwP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have hwQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  obtain hwPK : cwP s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  obtain hwQK : cwQ s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  obtain hpw : cpL s₀ ≤ 8 * cwP s₀ := by have := wordsOf_ge (l := cpL s₀); omega_arith
  obtain hqw : cqL s₀ ≤ 8 * cwQ s₀ := by have := wordsOf_ge (l := cqL s₀); omega_arith
  obtain hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  obtain hZ256 : 256 ≤ cZ s₀ := by omega_arith
  have hm : oMask = 88 := rfl
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQIP, mQIb⟩ := masked_facts hP
  have k0 := hF.keep
  obtain hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (Nat.le_of_lt mQb)
  have k0 := hF.keep
  obtain hd4 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid Y.fr hZ256 hd
  obtain hS4 : Scr t (cS s₀) (cZ s₀) := hF.scr.congr Y.wr
  refine wp_reassoc2 (WP.seq (WP.mono (final_ok (O := s₀.gpr .a0) (k := ck s₀) (b := cb s₀)
    (Scr.le hS4 (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith)) (by rw [Y.wr, k0.2.2]; exact hP.out) hP.nwO
    Y.s6 Y.s11 ((hd4 _ (by unfold oOut; omega_arith)).trans hF.hOut) ((hd4 _ (by unfold oNLen; omega_arith)).trans hF.hNL)
    Y.msk (by omega_arith) (by omega_arith) (Nat.le_refl _) (fun x hx => by have := hP.sepO x hx; omega_arith))
    fun t₅ ⟨⟨ob, O5, a0₅⟩, k5⟩ => ?_))
  have x4 := Y.x4
  obtain w5 : ∀ d, d + 8 ≤ 256 → Mont.word t₅.mem (cS s₀) d = Mont.word t.mem (cS s₀) d := fun d hd =>
    (Mem.readW_congr fun j hj => (O5 _ (Or.inr (by
      by_contra hc
      obtain h1 : Mont.ofs (cS s₀) (Mont.off (cS s₀) d + BitVec.ofNat 64 j) = d + j :=
        Mont.ofs_off _ (by omega_arith)
      obtain h2 : cZ s₀ ≤ Mont.ofs (cS s₀) (Mont.off (cS s₀) d + BitVec.ofNat 64 j) :=
        hP.sepO _ (by change Mont.ofs (s₀.gpr .a0) _ < ck s₀; omega_arith)
      omega_arith))).symm).symm
  refine hc t₅ ?_ a0₅ (fun i hi => ?_) ((k5.gpr (by decide)).trans Y.s6) ((k5.2.2.trans Y.wr).trans k0.2.2)
  · cases hb : cb s₀
    · rw [show vr s₀ = 0 by simp [vr, hb], VG.Proof.Bignum.i2osp_zero']
      exact Pub.zero_bytes fun i hi => by rw [ob i hi]; simp [hb]
    · have hvk : mQ s₀ * vh s₀ + vm2 s₀ < 256 ^ ck s₀ := by
        obtain ⟨_, _, _, hpq', hp1', _, hq1', _⟩ := mask_true hP.k64
          (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb
        obtain hN := os2ip_lt' (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀)) (VG.Proof.Bignum.bytesAt_length _ _ _)
        unfold vh vm1 vm2 mQ mP mQI
        simp only [hb, ↓reduceIte]
        have := VG.Proof.Bignum.crt_recombine_bound (p := vP s₀) (q := vQ s₀) (mp := vC s₀ ^ vDP s₀ % vP s₀)
          (mq := vC s₀ ^ vDQ s₀ % vQ s₀) (qi := vQI s₀) (Nat.lt_trans Nat.zero_lt_one hp1')
          (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one hq1'))
        rw [hpq'] at this
        omega_arith
      rw [show vr s₀ = mQ s₀ * vh s₀ + vm2 s₀ by simp [vr, hb]]
      exact Pub.out_bytes (B := cS s₀) (d := slot (cwX s₀) 4) (w := cwX s₀) (by omega_arith)
        (by rw [← Pre.wordsVal_eq_wv]; exact x4) hvk fun i hi => by rw [ob i hi]; simp [hb]
  · have e : Mont.off (savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := off_off' _ _ _
    have := hF.sav i hi
    rw [e] at this ⊢
    change Mont.word t₅.mem (cS s₀) (112 + 8 * i) = _
    rw [w5 _ (by omega_arith), hd4 _ (by unfold oMask; omega_arith)]
    exact this

theorem mid2_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (M : M1 s₀ s t)
    (hc : ∀ u, Spec.Rsa.bytesAt u.mem (s₀.gpr .a0) (ck s₀) = Spec.Rsa.i2osp (vr s₀) (ck s₀) →
      u.gpr .a0 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) →
      (∀ i < 13, u.mem.readW (Mont.off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)) →
      u.gpr .s6 = cS s₀ → u.wr = s₀.wr → WP isa c u Q) :
    WP isa (.seq (widen oBQ oQLen 6) (.seq (.block (setupP oBP oPLen)) (.seq recombineP (.seq recombineX
      (.seq (.block finBlk) (.seq output c)))))) t Q :=
  m2A_ok hP hF M fun _ Y2 _ => m2B_ok hP hF Y2 fun _ Y3 => m2C_ok hP hF Y3 fun _ Y4 => m2D_ok hP hF Y4 hc

end VG.Proof.Bignum.RISCV64.Crt

end

end

/-!
# The RSA private-key operation on RISC-V: correctness

`crt` saves the callee-saved registers, stores its arguments and sets up `X`
(`front_ok`), computes the result (`mid1_ok`, `mid2_ok`) and restores the
registers (`fn_correct`); `crtP` does the same from the cached `R²` of
each prime (`fn_correctP`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 13, r = Crt.saved i := by decide

theorem a0_not_saved : ∀ i < 13, Reg.a0 ≠ Crt.saved i := by decide

theorem toNat_flag (b : Bool) : BitVec.ofNat 64 (if b then 1 else 0) = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

/-- `crtG pc`: with `pc`, given the cached values (`R2F`). -/
theorem crt_wp (pc : Bool) (s : State) {X : List Region} (h : preCore (baseRd s ++ X) s)
    (hR2 : pc = true → R2F s) : WP isa (crtG pc) s fun t => abiPreserved s t ∧ postCore s t := by
  suffices main : WP isa (crtG pc) s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ postCore s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hP := pre_factsG h
  have hn := hP.nw
  have hpre := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -,
    -, -, -, -, -, -, -, hsl, alS, -⟩ := hpre
  simp only [Spec.Rsa.scratchWords] at hsl
  have hZ : 256 ≤ cZ s := by show 256 ≤ (stackArg s 9).toNat * 8; omega_arith
  have alS' : (cS s).toNat % 8 = 0 := alS
  unfold crtG
  refine WP.seq (WP.mono (front_okG (pc := pc) s h) fun s₁ ⟨hF, hR⟩ => ?_)
  refine mid1G_ok hP hF (fun hp => ⟨hR2 hp, hR hp⟩) fun t M => ?_
  refine mid2_ok hP hF M fun u ub u0 usav u6 uwr => ?_
  have hin : ∀ i < 13, InRegions u.wr (Mont.off (savW (cS s)) (8 * i)) 8 := fun i hi => by
    rw [uwr, hwr]
    show InRegions _ (cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega_arith) (by omega_arith)⟩
  have hal : ∀ i < 13, (Mont.off (savW (cS s)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    show (cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine WP.mono (restore_ok u (S := cS s) (v := fun i => s.gpr (Crt.saved i)) u6 hin hal usav)
    fun w ⟨wrs, wot, wm, _, _, _⟩ => ⟨⟨fun r hr => ?_, wrs 11 (by decide)⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact wrs i hi
  · show Spec.Rsa.written w.mem (s.gpr .a0) (ck s) ((w.gpr .a0).setWidth 32) _
    rw [wm, wot .a0 a0_not_saved, u0]
    refine VG.Proof.Bignum.crtWritten_of (VG.Proof.Bignum.bytesAt_length _ _ _) ub (toNat_flag _)
      (fun hv => ?_) (fun hv => ?_)
    · have hcb : cb s = (decide (vC s < vN s) && decide (vQI s < vP s) && decide (vP s * vQ s = vN s)) := by
        simp only [cb, crtMask, hv, Bool.true_and]
      refine ⟨?_, ?_⟩
      · rw [hcb]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
      · unfold vr
        cases hb : cb s
        · rfl
        · obtain ⟨_, _, _, _, hp1', _, _, _⟩ := mask_true hP.k64
            (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk)
            hb
          simp only [↓reduceIte, VG.Proof.Bignum.crtResult]
          rw [VG.Proof.Bignum.crt_coefficient_natural (Nat.lt_trans Nat.zero_lt_one hp1')]
          unfold vh vm1 vm2 mQ mP mQI
          simp only [hb, ↓reduceIte]
          exact Nat.add_comm _ _
    · have hcb : cb s = false := by simp only [cb, crtMask, hv, Bool.false_and]
      exact ⟨hcb, by unfold vr; rw [hcb]; rfl⟩

/-- A cache of two numbers of `a` and `b` words, as their words. -/
theorem cache_words {m : Mem} {P : Addr} {a b X Y : Nat}
    (h : Spec.Rsa.wordsAt m P (a + b) = Spec.Rsa.toWords X a ++ Spec.Rsa.toWords Y b)
    (hX : X < 2 ^ (64 * a)) (hY : Y < 2 ^ (64 * b)) :
    wordsVal m P 0 a = X ∧ wordsVal m P (8 * a) b = Y := by
  rw [Pre.wordsVal_eq_wv, Pre.wordsVal_eq_wv]
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, List.range_add, List.map_append, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_eq_of_lt hX]
    refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
    show (m.readW (P + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
    rw [Nat.zero_add, h1 i (List.mem_range.mpr hi), BitVec.toNat_ofNat]
  · rw [← Nat.mod_eq_of_lt hY]
    refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
    have := h2 i (List.mem_range.mpr hi)
    simp only [Function.comp_apply] at this
    show (m.readW (P + BitVec.ofNat 64 (8 * a + 8 * i)) 64).toNat = _
    rw [show 8 * a + 8 * i = 8 * (a + i) by omega_arith, this, BitVec.toNat_ofNat]

theorem primeWords_eq (n : Nat) : Spec.Rsa.primeWords n = wordsOf n := by
  unfold wordsOf Spec.Rsa.primeWords Spec.Rsa.modulusWords; split <;> omega_arith

/-- `R2F` from `fnContractP`'s precondition. -/
theorem r2F_of {s : State} (h : fnContractP.pre s) : R2F s where
  hS := h.2.2.2.1
  al := h.2.2.2.2.1
  rd i hi := by
    have hi' : i < wordsOf (s.gpr .a7).toNat + wordsOf (stackArg s 1).toNat := hi
    have := h.2.2.2.1; simp only at this
    exact ⟨r2R s, List.mem_append_left _ (by rw [h.1.1]; exact List.mem_append_right _ (List.mem_singleton_self _)),
      Offset.contains_base _ (show 8 * i + 8 ≤ 8 * (wordsOf (s.gpr .a7).toNat + wordsOf (stackArg s 1).toNat) by
        omega_arith) (by omega_arith)⟩
  sep x hx := Pub.sep_of_disjoint h.2.2.1 x hx
  val hb := by
    have hw := h.2.2.2.2.2.1
    simp only [Spec.Rsa.primeR2, VG.Proof.Bignum.bytesAt_length, primeWords_eq] at hw
    have hP := pre_factsG h.1
    obtain ⟨mP1, _, mQ1, _, mPb, mQb, _, _⟩ := masked_facts hP
    have eP : mP s = vP s := by simp only [mP, hb, ↓reduceIte]
    have eQ : mQ s = vQ s := by simp only [mQ, hb, ↓reduceIte]
    rw [eP] at mP1 mPb; rw [eQ] at mQ1 mQb
    have dP : cwP s = wordsOf (cpL s) := rfl
    have dQ : cwQ s = wordsOf (cqL s) := rfl
    have hpw : cpL s ≤ 8 * cwP s := by have := wordsOf_ge (l := cpL s); omega_arith
    have hqw : cqL s ≤ 8 * cwQ s := by have := wordsOf_ge (l := cqL s); omega_arith
    exact cache_words hw
      (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mP1)) (Nat.lt_of_lt_of_le mPb (pow256_le hpw)))
      (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mQ1)) (Nat.lt_of_lt_of_le mQb (pow256_le hqw)))
  pq := h.2.2.2.2.2.2

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa crt s tr t ∧ abiPreserved s t ∧ fnContract.post s t :=
  crt_wp false s (X := []) (by rw [List.append_nil]; exact h) nofun

theorem fn_correctP (s : State) (h : fnContractP.pre s) :
    ∃ tr t, Exec isa crtP s tr t ∧ abiPreserved s t ∧ fnContractP.post s t :=
  crt_wp true s h.1 fun _ => r2F_of h

end VG.Proof.Bignum.RISCV64.Crt
