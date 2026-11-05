module

-- separate module: built alongside Power, which it does not import

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Ffdh.RISCV64
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's exchange on RISC-V: the mask of a degenerate shared value

`eqMask_ok`: `eqMask j k` ands into `s4` the mask of arrays `j` and `k`
being equal: the `or` of their words' `xor`s is zero exactly when every word
is equal (`wordsVal_eq_iff`). `pMinus1_ok`: `p − 1` into array 6, p odd.
`zMask_ok`: `s9 :=` the mask of `z ∉ {0, 1, p − 1}` for z in array 4.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- The mask of `b`: all ones if `b`, else 0. -/
abbrev bmask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- Two numbers of 64-bit words are equal exactly when their words are. -/
theorem wordsVal_eq_iff (m : Mem) (B : Addr) (da db : Nat) :
    ∀ n, wordsVal m B da n = wordsVal m B db n ↔ ∀ k < n, word m B (da + 8 * k) = word m B (db + 8 * k)
  | 0 => ⟨fun _ _ h => absurd h (by omega_arith), fun _ => rfl⟩
  | n + 1 => by
    rw [wordsVal_succ_top, wordsVal_succ_top]
    have ha := wordsVal_lt m B da n
    have hb := wordsVal_lt m B db n
    constructor
    · intro h
      have hd : (word m B (da + 8 * n)).toNat = (word m B (db + 8 * n)).toNat := by
        have := congrArg (· / 2 ^ (64 * n)) h
        rwa [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.zero_add, Nat.zero_add] at this
      rw [hd, Nat.add_right_cancel_iff] at h
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (wordsVal_eq_iff m B da db n).mp h k hk
      · exact BitVec.eq_of_toNat_eq hd
    · intro h
      rw [(wordsVal_eq_iff m B da db n).mpr fun k hk => h k (by omega_arith), h n (by omega_arith)]

/-- `x ||| (a ^^^ b)` is zero exactly when `x` is and `a = b`. -/
theorem or_xor_zero (x a b : BitVec 64) : (x ||| (a ^^^ b) = 0) ↔ (x = 0 ∧ a = b) := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

/-- The tail of `eqMask`: `(0 <u x) - 1` is the mask of `x = 0`. -/
theorem sltu_mask (x : BitVec 64) :
    (if BitVec.ofNat 64 0 < x then (1 : BitVec 64) else 0) - BitVec.ofNat 64 1 = bmask (decide (x = 0)) := by
  by_cases h : x = 0
  · subst h; decide
  · have h' : BitVec.ofNat 64 0 < x := by
      rw [BitVec.lt_def]; have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e); simp; omega
    simp only [h', ↓reduceIte, h, decide_false]
    decide

/-- The registers `eqMask` writes. -/
def eqRegs : List Reg := [.t3, .t4, .t5, .s1, .s2, .s3, .s4]

/-- `eqMask j k`, arrays of `w` words: `s4 &=` the mask of their being
equal. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j k : Nat}
    (hj : slot w j + 8 * w ≤ Z) (hk : slot w k + 8 * w ≤ Z) :
    WP isa (eqMask j k) s fun t =>
      (t.gpr .s4 = s.gpr .s4 &&&
          bmask (decide (wordsVal s.mem B (slot w j) w = wordsVal s.mem B (slot w k) w)) ∧
        t.mem = s.mem) ∧ Keep eqRegs s t := by
  have hnw := hs.nowrap
  have alj := slot_al w j
  have alk := slot_al w k
  unfold eqMask
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 j) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) k) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hpre : WP isa (.block [.addi .t5 .t0 0, .li .s1 0]) s₂ fun s₃ =>
      (s₃.gpr .t5 = BitVec.ofNat 64 w ∧ s₃.gpr .s1 = 0 ∧ s₃.mem = s₂.mem) ∧ Keep [.t5, .s1] s₂ s₃ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, (k12.gpr (r := .t0) (by decide)).trans h0, add_ofNat_zero]
    rfl
  refine WP.mono hpre fun s₃ ⟨⟨i5, i1, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  have hm3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w j + 8 * i) ∧ t.gpr .t4 = off B (slot w k + 8 * i) ∧
      (t.gpr .s1 = 0 ↔ ∀ l < i, word s.mem B (slot w j + 8 * l) = word s.mem B (slot w k + 8 * l)) ∧
      t.mem = s.mem ∧ Keep [.t3, .t4, .t5, .s1, .s2, .s3] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .s2 .t3 0, .load .d .s3 .t4 0,
      .logic .xor .s2 .s2 .s3, .logic .or .s1 .s1 .s2, .addi .t3 .t3 8, .addi .t4 .t4 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith)
      (by omega_arith) Inv (fun i hi t ⟨j3, j4, j1, jm, jk⟩ hc => ?_)
    ⟨by rw [k3.gpr (r := .t3) (by decide), k2.gpr (r := .t3) (by decide), a3]; rfl,
      by rw [k3.gpr (r := .t4) (by decide), a4]; rfl,
      ⟨fun _ _ h => absurd h (by omega_arith), fun _ => i1⟩, hm3, k13.mono (by decide)⟩ i5)
    fun t ⟨_, _, t1, tm, tk⟩ => ?_)
  · have hs' := hs.congr jk.2.2
    have hst : WP isa (.block [.load .d .s2 .t3 0, .load .d .s3 .t4 0, .logic .xor .s2 .s2 .s3,
        .logic .or .s1 .s1 .s2, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .t5 .t5 (-1)]) t
        fun t' => t' = (((((((t.write .s2 (word t.mem B (slot w j + 8 * i))).write .s3
          (word t.mem B (slot w k + 8 * i))).write .s2
          (word t.mem B (slot w j + 8 * i) ^^^ word t.mem B (slot w k + 8 * i))).write .s1
          (t.gpr .s1 ||| (word t.mem B (slot w j + 8 * i) ^^^ word t.mem B (slot w k + 8 * i)))).write .t3
          (off B (slot w j + 8 * i + 8))).write .t4 (off B (slot w k + 8 * i + 8))).write .t5
          (t.gpr .t5 - BitVec.ofNat 64 1)) := by
      brun [j3, j4, hs'.ld (show slot w j + 8 * i + 8 ≤ Z by omega_arith),
        hs'.ld (show slot w k + 8 * i + 8 ≤ Z by omega_arith),
        hs'.al8 (show slot w j + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
        hs'.al8 (show slot w k + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    refine ⟨⟨by gsimp; rw [show slot w j + 8 * i + 8 = slot w j + 8 * (i + 1) by omega_arith],
      by gsimp; rw [show slot w k + 8 * i + 8 = slot w k + 8 * (i + 1) by omega_arith], ?_, by gsimp; exact jm,
      ?_⟩, by gsimp⟩
    · gsimp
      rw [or_xor_zero, j1, jm]
      constructor
      · rintro ⟨h1, h2⟩ l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
        · exact h1 l hl
        · exact h2
      · intro h
        exact ⟨fun l hl => h l (by omega_arith), h i (by omega_arith)⟩
    · exact Keep.trans' jk ((((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono
        (by decide))
  · refine WP.mono (WP.keep [.s1, .s2, .s4] (Q := fun u => u.gpr .s4 = t.gpr .s4 &&& bmask (decide (t.gpr .s1 = 0)) ∧
      u.mem = t.mem) (by brun [exec_li, sltu_mask]) (by rfl) (by rfl)) fun u ⟨⟨u4, um⟩, ku⟩ =>
      ⟨⟨?_, um.trans tm⟩, (tk.trans ku).mono (by decide)⟩
    rw [u4, tk.gpr (by decide)]
    congr 2
    exact decide_eq_decide.mpr (t1.trans (wordsVal_eq_iff s.mem B (slot w j) (slot w k) w).symm)

theorem xor_one_odd {n : Nat} (h : n % 2 = 1) : n ^^^ 1 = n - 1 := by
  have h1 : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  have h2 : (n ^^^ 1) % 2 ≠ 1 := by rw [Ne, Nat.xor_mod_two_eq_one]; simp [h]
  omega

/-- `p − 1` from `p` (odd) in array `j`: its low word's bit 0 cleared. -/
theorem clear1_ok {t : State} {B : Addr} {Z w N j : Nat} (hs : Scr t B Z) (hZ : slot w j + 8 * w ≤ Z) (hw : 1 ≤ w)
    (h3 : t.gpr .t3 = off B (slot w j)) (hN : wordsVal t.mem B (slot w j) w = N) (hodd : N % 2 = 1) :
    WP isa (.block [.load .d .s0 .t3 0, .logicImm .xor .s0 .s0 1, .store .d .s0 .t3 0]) t fun u =>
      (wordsVal u.mem B (slot w j) w = N - 1 ∧ Outside B (slot w j) 8 t.mem u.mem) ∧ Keep [.s0] t u := by
  have hn := hs.nowrap
  have s8 : slot w j + 8 ≤ Z := by omega_arith
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h3, BitVec.add_zero, hs.ld s8, hs.st s8, hs.al8 s8 (slot_al w j), exec_logicImm (show imm12 1 by decide)]
  have ow := writeW_outside t.mem B (d := slot w j) (word t.mem B (slot w j) ^^^ BitVec.ofNat 64 1) (by omega_arith)
  refine ⟨?_, ow⟩
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega_arith⟩
  rw [← hN]
  simp only [wordsVal]
  rw [VG.Proof.Mont.word_writeW_self, Outside.wordsVal ow (Or.inr (by omega_arith)) (by omega_arith)]
  have hlow : (word t.mem B (slot (w' + 1) j)).toNat % 2 = 1 := by
    rw [← hN] at hodd
    simp only [wordsVal] at hodd
    omega_arith
  have hlow' : (t.mem.readW (off B (slot (w' + 1) j)) 64).toNat % 2 = 1 := hlow
  have hx : (t.mem.readW (off B (slot (w' + 1) j)) 64 ^^^ BitVec.ofNat 64 1).toNat =
      (word t.mem B (slot (w' + 1) j)).toNat - 1 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, xor_one_odd hlow']
  rw [hx]
  omega_using [hlow]

/-- `pMinus1`: `p − 1` into array 6, from p (odd) in array 0. -/
theorem pMinus1_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 6 + 8 * w ≤ Z)
    (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa pMinus1 s fun t =>
      (wordsVal t.mem B (slot w 6) w = wordsVal s.mem B (slot w 0) w - 1 ∧
        Outside B (slot w 6) (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e6 := e 6
  unfold pMinus1
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 6) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = off B (slot w 0) ∧ u.mem = s₁.mem)
    (by brun [(k1.gpr (by decide)).trans h7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  refine WP.seq (WP.mono (Win.copySame_ok (dS := slot w 0) (dD := slot w 6) (hs.congr k12.2.2) a4
    ((k2.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans h0) hw hw' (slot_al w 0) (slot_al w 6)
    (by omega_arith) hZ (Or.inl (by omega_arith))) fun s₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans h5) 6) fun s₄ ⟨⟨b3, m4⟩, k4⟩ => ?_
  have v6 : wordsVal s₄.mem B (slot w 6) w = wordsVal s.mem B (slot w 0) w := by
    rw [m4]; exact Win.wv_words c3
  refine WP.mono (clear1_ok (hs.congr (k13.trans k4).2.2) hZ hw b3 v6 hodd) fun t ⟨⟨tv, ot⟩, kt⟩ =>
    ⟨⟨tv, ?_⟩, ((k13.trans k4).trans kt).mono (by decide)⟩
  rw [m4] at ot
  exact o3.trans (ot.mono (Nat.le_refl _) (by omega_arith))

theorem li_m1 {s : State} {d : Reg} : exec (.li d (-1)) s = some (s.write d (BitVec.allOnes 64)) := by
  rw [exec_li (by decide)]; rfl

theorem xori_m1 {s : State} {d n : Reg} :
    exec (.logicImm .xor d n (-1)) s = some (s.write d (s.gpr n ^^^ BitVec.allOnes 64)) := by
  rw [exec_logicImm (by decide)]; rfl

theorem bmask_not (a : Bool) : bmask a ^^^ BitVec.allOnes 64 = bmask (!a) := by cases a <;> decide

theorem bmask_and (a b : Bool) : bmask a &&& bmask b = bmask (a && b) := by cases a <;> cases b <;> decide

theorem bmask_not' (a : Bool) : bmask a ^^^ -1#64 = bmask (!a) := by cases a <;> decide

theorem ones_and (b : Bool) : BitVec.allOnes 64 &&& bmask b = bmask b := by cases b <;> decide

theorem ones_xor (a : Bool) : bmask a ^^^ BitVec.allOnes 64 = bmask (!a) := bmask_not a

/-- After the first comparison: `s9 :=` its inverted mask, `s4 :=` all ones. -/
theorem blkA_ok {s : State} {a : Bool} (h9 : s.gpr .s9 = BitVec.allOnes 64) (h4 : s.gpr .s4 = bmask a) :
    WP isa (.block [.logic .xor .s4 .s4 .s9, .logic .and .s9 .s9 .s4, .li .s4 (-1)]) s fun t =>
      (t.gpr .s9 = bmask (!a) ∧ t.gpr .s4 = BitVec.allOnes 64 ∧ t.mem = s.mem) ∧ Keep [.s4, .s9] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h9, h4, li_m1, bmask_not, ones_and]

/-- A later comparison: its inverted mask and-ed into `s9`, `s4 :=` all
ones. -/
theorem blkB_ok {s : State} {a c : Bool} (h9 : s.gpr .s9 = bmask c) (h4 : s.gpr .s4 = bmask a) :
    WP isa (.block [.logicImm .xor .s4 .s4 (-1), .logic .and .s9 .s9 .s4, .li .s4 (-1)]) s fun t =>
      (t.gpr .s9 = bmask (c && !a) ∧ t.gpr .s4 = BitVec.allOnes 64 ∧ t.mem = s.mem) ∧ Keep [.s4, .s9] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h9, h4, li_m1, xori_m1, bmask_not, bmask_not', bmask_and]

/-- The last comparison. -/
theorem blkC_ok {s : State} {a c : Bool} (h9 : s.gpr .s9 = bmask c) (h4 : s.gpr .s4 = bmask a) :
    WP isa (.block [.logicImm .xor .s4 .s4 (-1), .logic .and .s9 .s9 .s4]) s fun t =>
      (t.gpr .s9 = bmask (c && !a) ∧ t.mem = s.mem) ∧ Keep [.s4, .s9] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h9, h4, xori_m1, bmask_not, bmask_not', bmask_and]

/-- The registers `zMask` writes. -/
def zRegs : List Reg := [.t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s9]

/-- `zMask`: `s9 :=` the mask of `z ∉ {0, 1, p − 1}` for z in array 4 and p
(odd) in array 0, writing only arrays 5–7. -/
theorem zMask_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa zMask s fun t =>
      (t.gpr .s9 = bmask (decide (wordsVal s.mem B (slot w 4) w ≠ 0 ∧ wordsVal s.mem B (slot w 4) w ≠ 1 ∧
          wordsVal s.mem B (slot w 4) w ≠ wordsVal s.mem B (slot w 0) w - 1)) ∧
        Outside B (slot w 5) (3 * (8 * (w + 2))) s.mem t.mem) ∧ Keep zRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  generalize hz : wordsVal s.mem B (slot w 4) w = z
  generalize hP : wordsVal s.mem B (slot w 0) w = p at hodd
  unfold zMask
  -- 0 into array 5.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 5) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h0) hw hw' (slot_al w 5)
    (by omega_arith)) fun s₂ ⟨⟨_, z2, o2⟩, k2⟩ => ?_)
  rw [m1] at o2
  have k12 := k1.trans k2
  -- 1 into array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok (hs.congr k12.2.2) hw hw' hZ ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) ((k12.gpr (by decide)).trans h0)) fun s₃ ⟨⟨v7, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  -- `p − 1` into array 6.
  have p3 : wordsVal s₃.mem B (slot w 0) w = p := by
    rw [Outside.wordsVal o3 (by omega_arith) (by omega_arith), Outside.wordsVal o2 (by omega_arith) (by omega_arith), hP]
  refine WP.seq (WP.mono (pMinus1_ok (hs.congr k13.2.2) ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans h5) ((k13.gpr (by decide)).trans h0) hw hw' (by omega_arith) (by rw [p3]; exact hodd))
    fun s₄ ⟨⟨v6, o4⟩, k4⟩ => ?_)
  rw [p3] at v6
  have k14 := k13.trans k4
  have hz4 : wordsVal s₄.mem B (slot w 4) w = z := by
    rw [Outside.wordsVal o4 (by omega_arith) (by omega_arith), Outside.wordsVal o3 (by omega_arith) (by omega_arith),
      Outside.wordsVal o2 (by omega_arith) (by omega_arith), hz]
  have v5 : wordsVal s₄.mem B (slot w 5) w = 0 := by
    rw [Outside.wordsVal o4 (by omega_arith) (by omega_arith), Outside.wordsVal o3 (by omega_arith) (by omega_arith)]
    exact Pub.wsv_zero z2
  have v7' : wordsVal s₄.mem B (slot w 7) w = 1 := by
    rw [Outside.wordsVal o4 (by omega_arith) (by omega_arith)]; exact v7
  have o14 : Outside B (slot w 5) (3 * (8 * (w + 2))) s.mem s₄.mem :=
    ((o2.mono (Nat.le_refl _) (by omega_arith)).trans (o3.mono (by omega_arith) (by omega_arith))).trans
      (o4.mono (by omega_arith) (by omega_arith))
  -- The masks.
  refine WP.seq (WP.mono (WP.keep [.s9, .s4] (Q := fun u => u.gpr .s9 = BitVec.allOnes 64 ∧
    u.gpr .s4 = BitVec.allOnes 64 ∧ u.mem = s₄.mem) (by brun [li_m1]) (by rfl) (by rfl)) fun s₅ ⟨⟨a9, a4, m5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have g : ∀ {u : State} {rs : List Reg}, Keep rs s u → (∀ r ∈ [Reg.a7, .s5, .t0], r ∉ rs) →
      u.gpr .a7 = off B (slot w 0) ∧ u.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) ∧ u.gpr .t0 = BitVec.ofNat 64 w :=
    fun k hr => ⟨(k.gpr (hr _ (by decide))).trans h7, (k.gpr (hr _ (by decide))).trans h5,
      (k.gpr (hr _ (by decide))).trans h0⟩
  have G5 := g k15 (by decide)
  refine WP.seq (WP.mono (eqMask_ok (j := 4) (k := 5) (hs.congr k15.2.2) G5.1 G5.2.1 G5.2.2 hw hw' (by omega_arith)
    (by omega_arith)) fun s₆ ⟨⟨b4, m6⟩, k6⟩ => ?_)
  rw [a4, ones_and, m5, hz4, v5] at b4
  refine WP.seq (WP.mono (blkA_ok ((k6.gpr (by decide)).trans a9) b4) fun s₇ ⟨⟨c9, c4, m7⟩, k7⟩ => ?_)
  have k17 := (k15.trans k6).trans k7
  have G7 := g k17 (by decide)
  refine WP.seq (WP.mono (eqMask_ok (j := 4) (k := 7) (hs.congr k17.2.2) G7.1 G7.2.1 G7.2.2 hw hw' (by omega_arith)
    (by omega_arith)) fun s₈ ⟨⟨d4, m8⟩, k8⟩ => ?_)
  rw [c4, ones_and, m7, m6, m5, hz4, v7'] at d4
  refine WP.seq (WP.mono (blkB_ok ((k8.gpr (by decide)).trans c9) d4) fun s₉ ⟨⟨f9, f4, m9⟩, k9⟩ => ?_)
  have k19 := (k17.trans k8).trans k9
  have G9 := g k19 (by decide)
  refine WP.seq (WP.mono (eqMask_ok (j := 4) (k := 6) (hs.congr k19.2.2) G9.1 G9.2.1 G9.2.2 hw hw' (by omega_arith)
    (by omega_arith)) fun s₁₀ ⟨⟨h4', m10⟩, k10⟩ => ?_)
  rw [f4, ones_and, m9, m8, m7, m6, m5, hz4, v6] at h4'
  refine WP.mono (blkC_ok ((k10.gpr (by decide)).trans f9) h4') fun t ⟨⟨t9, mt⟩, kt⟩ =>
    ⟨⟨?_, ?_⟩, ((k19.trans k10).trans kt).mono (by decide)⟩
  · rw [t9]
    congr 1
    by_cases a : z = 0 <;> by_cases b : z = 1 <;> by_cases c : z = p - 1 <;> simp [a, b, c]
  · rw [mt, m10, m9, m8, m7, m6, m5]; exact o14

end VG.Proof.Ffdh.RISCV64
