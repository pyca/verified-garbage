module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Pow57Ops
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pow57

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Pow57

/-! ## Digits -/

theorem exec_srlReg' {s : State} {d n m : Reg} :
    exec (.shiftReg .srl .d d n m) s = some (s.write d (s.gpr n >>> ((s.gpr m).toNat % 64))) := rfl

theorem exec_sllReg' {s : State} {d n m : Reg} :
    exec (.shiftReg .sll .d d n m) s = some (s.write d (s.gpr n <<< ((s.gpr m).toNat % 64))) := rfl

theorem mod_digit (V b k : Nat) : V % 2 ^ (b * (k + 1)) = V % 2 ^ (b * k) + 2 ^ (b * k) * (V / 2 ^ (b * k) % 2 ^ b) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]

theorem lv_digits {m : Mem} {B : Addr} {d V : Nat} : ∀ {k : Nat}, (∀ i < k, (word m B (d + 8 * i)).toNat = V / 2 ^ (57 * i) % 2 ^ 57) →
    lv m B d k = V % 2 ^ (57 * k)
  | 0, _ => by rw [lv, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by rw [lv, lv_digits fun i hi => h i (by omega_using [hi]), h k (Nat.lt_succ_self k), mod_digit]

theorem wv_digits {m : Mem} {B : Addr} {d V : Nat} : ∀ {k : Nat}, (∀ i < k, (word m B (d + 8 * i)).toNat = V / 2 ^ (64 * i) % 2 ^ 64) →
    wordsVal m B d k = V % 2 ^ (64 * k)
  | 0, _ => by rw [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by rw [wordsVal_succ_top, wv_digits fun i hi => h i (by omega_using [hi]), h k (Nat.lt_succ_self k), mod_digit]

theorem wv_div (m : Mem) (B : Addr) (d j k : Nat) : wordsVal m B d (j + k) / 2 ^ (64 * j) = wordsVal m B (d + 8 * j) k := by
  rw [fios_wordsVal_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wordsVal_lt m B d j), Nat.zero_add]

theorem lv_div {m : Mem} {B : Addr} {d j k : Nat} (h : Lim m B d j L57) : lv m B d (j + k) / 2 ^ (57 * j) = lv m B (d + 8 * j) k := by
  rw [lv_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (lv_lt h), Nat.zero_add]

/-- The quotient of a number of two words and more. -/
theorem div_two {b x y r s t : Nat} (h : s + t = b) : (x + 2 ^ b * (y + 2 ^ b * r)) / 2 ^ s = x / 2 ^ s + 2 ^ t * (y + 2 ^ b * r) := by
  rw [← h, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s)]

theorem digit_57 {V w w' r p k s : Nat} (hp : p = 64 * k + s) (hs : s < 64) (hV : V / 2 ^ (64 * k) = w + 2 ^ 64 * (w' + 2 ^ 64 * r)) :
    V / 2 ^ p % 2 ^ 57 = (w / 2 ^ s + w' * 2 ^ (64 - s)) % 2 ^ 64 % 2 ^ 57 := by
  rw [hp, Nat.pow_add, ← Nat.div_div_eq_div_mul, hV, div_two (t := 64 - s) (by omega_using [hs])]
  rw [Nat.mod_mod_of_dvd _ (by decide : (2 : Nat) ^ 57 ∣ 2 ^ 64)]
  rw [Nat.mul_add, Nat.mul_comm w', ← Nat.add_assoc, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_comm (2 ^ (64 - s) * r) (2 ^ 64),
    show 2 ^ 64 = 2 ^ 57 * 2 ^ 7 by decide, Nat.mul_assoc (2 ^ 57), Nat.add_mul_mod_self_left]

theorem digit_64 {V x y z r p k s : Nat} (hp : p = 57 * k + s) (hs : s < 57)
    (hV : V / 2 ^ (57 * k) = x + 2 ^ 57 * (y + 2 ^ 57 * (z + 2 ^ 57 * r))) :
    V / 2 ^ p % 2 ^ 64 = (x / 2 ^ s + y * 2 ^ (57 - s) + z * 2 ^ 57 * 2 ^ (57 - s)) % 2 ^ 64 := by
  rw [hp, Nat.pow_add, ← Nat.div_div_eq_div_mul, hV, div_two (t := 57 - s) (by omega_using [hs])]
  obtain ⟨t, ht⟩ : ∃ t, 57 - s = t + 1 := ⟨56 - s, by omega_using [hs]⟩
  rw [ht]
  obtain e : x / 2 ^ s + 2 ^ (t + 1) * (y + 2 ^ 57 * (z + 2 ^ 57 * r)) =
      x / 2 ^ s + y * 2 ^ (t + 1) + z * 2 ^ 57 * 2 ^ (t + 1) + 2 ^ 64 * (2 ^ 51 * (2 ^ t * r)) := by
    rw [Nat.pow_succ]
    grind
  rw [e, Nat.add_mul_mod_self_left]

/-! ## Unpacking -/

theorem not_mod64 : ∀ i < 54, ((BitVec.ofNat 64 (57 * i) ^^^ (-BitVec.ofNat 64 1 : BitVec 64)).toNat % 64) = 63 - 57 * i % 64 := by
  decide +kernel

theorem sll_toNat (x : BitVec 64) (k : Nat) : (x <<< k).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem srl_toNat (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem unpack_val {x y : BitVec 64} {s : Nat} (hs : s < 64) :
    ((x >>> s + y <<< 1 <<< (63 - s)) &&& m57).toNat = (x.toNat / 2 ^ s + y.toNat * 2 ^ (64 - s)) % 2 ^ 64 % 2 ^ 57 := by
  rw [and_m57, BitVec.toNat_add, srl_toNat, sll_toNat, sll_toNat, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add,
    show 1 + (63 - s) = 64 - s by omega_using [hs], Nat.add_mod_mod]

def unpackRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .t2, .t4, .t5]

theorem unpack_ok {s : State} {B : Addr} {Z dS dD n w V : Nat} (hs : Scr s B Z) (h3 : s.gpr .t3 = off B dS) (h4 : s.gpr .t4 = off B dD)
    (h5 : s.gpr .t5 = BitVec.ofNat 64 n) (hn0 : 0 < n) (hn : n ≤ 54) (hw : 57 * n ≤ 64 * w + 56) (hz : word s.mem B (dS + 8 * w) = 0)
    (hV : wordsVal s.mem B dS w = V) (hS : dS + 8 * w + 8 ≤ Z) (hD : dD + 8 * n ≤ Z) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0)
    (sep : dS + 8 * w + 8 ≤ dD ∨ dD + 8 * n ≤ dS) :
    WP isa unpack s fun t => (Outside B dD (8 * n) s.mem t.mem ∧ Lim t.mem B dD n L57 ∧ lv t.mem B dD n = V % 2 ^ (57 * n)) ∧
      Keep unpackRegs s t := by
  have hnw := hs.nowrap
  unfold unpack countLoop
  obtain r : WP isa (.block [.li .s4 (-1), .shift .srl .d .s4 .s4 7, .li .t2 0]) s fun t => (t.gpr .s4 = m57 ∧ t.gpr .t2 = 0#64 ∧
      t.mem = s.mem) ∧ Keep [.s4, .t2] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li]
    rfl
  refine WP.seq (WP.mono r fun s₁ ⟨⟨x4, x2, m1⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .t5) (N := n) (by omega_using [hn]) hn0 (fun i t => t.gpr .s4 = m57 ∧
      t.gpr .t2 = BitVec.ofNat 64 (57 * i) ∧ t.gpr .t4 = off B (dD + 8 * i) ∧ Outside B dD (8 * i) s.mem t.mem ∧
      (∀ j < i, (word t.mem B (dD + 8 * j)).toNat = V / 2 ^ (57 * j) % 2 ^ 57) ∧ Keep unpackRegs s t)
    (fun i hi t ⟨t4, t2, tp, to, tv, tk⟩ _ => ?_) ⟨x4, x2, (k1.gpr (by decide)).trans h4, by rw [m1]; exact Outside.refl _ _ _ _,
      fun j hj => absurd hj (Nat.not_lt_zero j), k1.mono (by decide)⟩ ((k1.gpr (by decide)).trans h5))
    fun t ⟨_, _, _, to, tv, tk⟩ => ⟨⟨to, fun j hj => by rw [tv j hj]; exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide)), lv_digits tv⟩, tk⟩
  obtain hk : 57 * i / 64 + 1 ≤ w := by omega_using [hw, hi]
  obtain rd : ∀ j ≤ w, word t.mem B (dS + 8 * j) = word s.mem B (dS + 8 * j) := fun j hj =>
    to.word (by omega_using [sep, hj, hi]) (by omega_using [hS, hnw, hj])
  generalize ek : 57 * i / 64 = k at hk
  generalize es : 57 * i % 64 = sh
  obtain hp : 57 * i = 64 * k + sh := by rw [← ek, ← es]; omega_using []
  obtain hsh : sh < 64 := by rw [← es]; omega_using []
  obtain R0 := rd k (by omega_using [hk])
  obtain R1 := rd (k + 1) hk
  obtain a1 : BitVec.ofNat 64 (57 * i) >>> 6 <<< 3 = BitVec.ofNat 64 (8 * k) := by
    rw [srl_ofNat (by omega_using [hi, hn]), ← ek]
    apply BitVec.eq_of_toNat_eq
    rw [sll_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using []
  obtain a2 : BitVec.ofNat 64 (8 * k) + off B dS = off B (dS + 8 * k) := by
    rw [BitVec.add_comm, off_add]
  obtain a3 : (BitVec.ofNat 64 (57 * i)).toNat % 64 = sh := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 57 * i) (b := 2 ^ 64) (by omega_using [hi, hn]), es]
  obtain a4 := not_mod64 i (by omega_using [hi, hn])
  rw [es] at a4
  obtain r : WP isa (.block ([.shift .srl .d .s0 .t2 6, .shift .sll .d .s0 .s0 3, .add .s0 .s0 .t3, .load .d .s1 .s0 0,
      .load .d .s2 .s0 8, .shiftReg .srl .d .s1 .s1 .t2, .logicImm .xor .s3 .t2 (-1), .shift .sll .d .s2 .s2 1,
      .shiftReg .sll .d .s2 .s2 .s3, .add .s1 .s1 .s2, .logic .and .s1 .s1 .s4, .store .d .s1 .t4 0,
      .addi .t4 .t4 8, .addi .t2 .t2 57] ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun u =>
      (u.mem = t.mem.writeW (off B (dD + 8 * i)) ((word s.mem B (dS + 8 * k) >>> sh +
          word s.mem B (dS + 8 * (k + 1)) <<< 1 <<< (63 - sh)) &&& m57) ∧
        u.gpr .t2 = BitVec.ofNat 64 (57 * i + 57) ∧ u.gpr .t4 = off B (dD + 8 * i + 8) ∧
        u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.s0, .s1, .s2, .s3, .t2, .t4, .t5] t u := by
    obtain hs := hs.congr tk.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [t2, (tk.gpr (r := .t3) (by decide)).trans h3, tp, t4, a1, a2, a3, a4, ↓exec_srlReg', ↓exec_sllReg',
      hs.ld (show dS + 8 * k + 8 ≤ Z by omega_using [hS, hk]), hs.ld (show dS + 8 * k + 8 + 8 ≤ Z by omega_using [hS, hk]),
      hs.st (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]),
      hs.al8 (show dS + 8 * k + 8 ≤ Z by omega_using [hS, hk]) (by omega_using [hS8]),
      hs.al8 (show dS + 8 * k + 8 + 8 ≤ Z by omega_using [hS, hk]) (by omega_using [hS8]),
      hs.al8 (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]) (by omega_using [hD8]), ← BitVec.ofNat_add,
      show t.mem.readW (off B (dS + 8 * k)) 64 = word s.mem B (dS + 8 * k) from R0,
      show t.mem.readW (off B (dS + 8 * k + 8)) 64 = word s.mem B (dS + 8 * (k + 1)) from R1]
  refine WP.mono r fun u ⟨⟨um, u2, u4, u5⟩, ku⟩ => ?_
  obtain ou : Outside B (dD + 8 * i) 8 t.mem u.mem := by rw [um]; exact writeW_outside _ B _ (by omega_using [hD, hi, hnw])
  refine ⟨⟨(ku.gpr (by decide)).trans t4, by rw [u2, Nat.mul_succ], by rw [u4, Nat.mul_succ, Nat.add_assoc],
    (to.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using [])), fun j hj => ?_,
    Keep.trans' tk (ku.mono (by decide))⟩, u5⟩
  by_cases hji : j < i
  · rw [ou.word (by omega_using [hji]) (by omega_using [hD, hi, hji, hnw])]; exact tv j hji
  · obtain rfl : j = i := by omega_using [hj, hji]
    rw [um, word_writeW_self, unpack_val hsh]
    refine (digit_57 (r := wordsVal s.mem B (dS + 8 * (k + 2)) (w - k - 1)) hp hsh ?_).symm
    obtain e : V = wordsVal s.mem B dS (k + (2 + (w - k - 1))) := by
      rw [show k + (2 + (w - k - 1)) = w + 1 by omega_using [hk], wordsVal_succ_top, hz, hV]
      rfl
    rw [e, wv_div, show 2 + (w - k - 1) = (w - k - 1) + 1 + 1 by omega_using [], wordsVal, wordsVal,
      show dS + 8 * k + 8 = dS + 8 * (k + 1) by omega_using [], show dS + 8 * (k + 1) + 8 = dS + 8 * (k + 2) by omega_using []]

/-- Array 5's offset. -/
abbrev o5 (q d0 : Nat) : Nat := d0 + 320 * q + 80

theorem sll_ofNat (n k : Nat) : BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [sll_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mul_mod]

/-- `unpackFrom dst`, for `dst` that puts `dD` into `t4`. -/
theorem unpackFrom_ok {s : State} {B : Addr} {Z q d0 dD : Nat} {dst : List Instr} (h : Sp s B Z q d0)
    (hdst : ∀ u, Sp u B Z q d0 → u.gpr .t2 = BitVec.ofNat 64 (72 * q) →
      WP isa (.block dst) u fun t => (t.gpr .t4 = off B dD ∧ t.mem = u.mem) ∧ Keep [.t4] u t)
    (hD : dD + 72 * q ≤ Z) (hD8 : dD % 8 = 0) (sep : o5 q d0 + 64 * q + 8 ≤ dD ∨ dD + 72 * q ≤ o5 q d0) :
    WP isa (unpackFrom dst) s fun t => (∃ m₁, Outside B (o5 q d0 + 64 * q) 8 s.mem m₁ ∧ Outside B dD (72 * q) m₁ t.mem ∧
      Lim t.mem B dD (9 * q) L57 ∧ lv t.mem B dD (9 * q) = wordsVal s.mem B (o5 q d0) (8 * q)) ∧
      Keep ([.t3] ++ unpackRegs) s t := by
  obtain q2 := h.q2
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain d8 := h.d8
  have hn := h.scr.nowrap
  unfold unpackFrom
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain b1 : o5 q d0 + 64 * q + 8 ≤ Z := by unfold o5; omega_using [fit, q2]
  obtain e1 : BitVec.ofNat 64 (64 * q + 16) <<< 2 = BitVec.ofNat 64 (256 * q + 64) := by
    rw [sll_ofNat]; exact congrArg _ (by omega_using [])
  obtain e2 : BitVec.ofNat 64 (72 * q) >>> 3 = BitVec.ofNat 64 (9 * q) := by
    rw [srl_ofNat (by omega_using [q6])]; exact congrArg _ (by omega_using [])
  obtain e3 : BitVec.ofNat 64 (256 * q + 64) + BitVec.ofNat 64 (64 * q + 16) + off B d0 = off B (o5 q d0) := by
    rw [BitVec.add_comm, ← BitVec.ofNat_add, off_add]; exact congrArg (off B) (by unfold o5; omega_using [])
  obtain r : WP isa (.block [.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .add .t5 .t3 .s5, .addi .t5 .t5 (-16),
    .li .s0 0, .store .d .s0 .t5 0, .shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18),
    .shift .srl .d .t5 .t2 3]) s fun t => (t.gpr .t3 = off B (o5 q d0) ∧ t.gpr .t2 = BitVec.ofNat 64 (72 * q) ∧
      t.gpr .t5 = BitVec.ofNat 64 (9 * q) ∧ t.mem = s.mem.writeW (off B (o5 q d0 + 64 * q)) 0#64) ∧ Keep [.t3, .t5, .s0, .t2] s t := by
    obtain hs := h.scr
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.a7, h.s5, e1, e2, e3, n8_calc q6, exec_li, off_sub B (show 16 ≤ o5 q d0 + (64 * q + 16) by omega_using []),
      show o5 q d0 + (64 * q + 16) - 16 = o5 q d0 + 64 * q by omega_using [], hs.st (show o5 q d0 + 64 * q + 8 ≤ Z by omega_using [b1]),
      hs.al8 (show o5 q d0 + 64 * q + 8 ≤ Z by omega_using [b1]) (by unfold o5; omega_using [d8])]
  refine WP.mono r fun u ⟨⟨u3, u2, u5, um⟩, ku⟩ => ?_
  refine WP.mono (hdst u (h.of ku (by decide) (by decide)) u2) fun v ⟨⟨v4, vm⟩, kv⟩ => ?_
  obtain kuv := ku.trans kv
  obtain ou : Outside B (o5 q d0 + 64 * q) 8 s.mem v.mem := by rw [vm, um]; exact writeW_outside _ B _ (by omega_using [b1, hn])
  refine WP.mono (unpack_ok (w := 8 * q) (n := 9 * q) (dS := o5 q d0) (dD := dD) (h.scr.congr kuv.2.2) ((kv.gpr (by decide)).trans u3) v4
    ((kv.gpr (by decide)).trans u5) (by omega_using [q2]) (by omega_using [q6]) (by omega_using [q6])
    (by rw [show o5 q d0 + 8 * (8 * q) = o5 q d0 + 64 * q by omega_using [], vm, um, word_writeW_self]; rfl) rfl
    (by omega_using [b1]) (by omega_using [hD]) (by unfold o5; omega_using [d8]) hD8 (by omega_using [sep]))
    fun t ⟨⟨ot, lt, et⟩, kt⟩ => ⟨⟨v.mem, ou, ot.mono (Nat.le_refl _) (by omega_using []), lt, ?_⟩, (kuv.trans kt).mono (by decide)⟩
  rw [et, ou.wordsVal (by omega_using []) (by omega_using [b1, hn])]
  refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (wordsVal_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_using [])))

theorem atM_ok {u : State} {B : Addr} {Z q d0 : Nat} (h : Sp u B Z q d0) :
    WP isa (.block atM) u fun t => (t.gpr .t4 = off B (oM q d0) ∧ t.mem = u.mem) ∧ Keep [.t4] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold atM
  brun [h.a7, h.s5]
  exact congrArg (off B) (by unfold oM; omega_using [])

theorem atA_ok {u : State} {B : Addr} {Z q d0 : Nat} (h : Sp u B Z q d0) (h2 : u.gpr .t2 = BitVec.ofNat 64 (72 * q)) :
    WP isa (.block atA) u fun t => (t.gpr .t4 = off B (oA q (oM q d0)) ∧ t.mem = u.mem) ∧ Keep [.t4] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold atA atM
  brun [h.a7, h.s5, h2]
  exact congrArg (off B) (by unfold oA oM; omega_using [])

theorem atE_ok {u : State} {B : Addr} {Z q d0 : Nat} (h : Sp u B Z q d0) (h2 : u.gpr .t2 = BitVec.ofNat 64 (72 * q)) :
    WP isa (.block atE) u fun t => (t.gpr .t4 = off B (oE q (oM q d0)) ∧ t.mem = u.mem) ∧ Keep [.t4] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold atE atA atM
  brun [h.a7, h.s5, h2]
  exact congrArg (off B) (by unfold oE oM; omega_using [])

theorem pads_ok {s : State} {B : Addr} {Z q d0 : Nat} (h : Sp s B Z q d0) :
    WP isa (.block pads) s fun t => (Outside B (oM q d0) (144 * q + 48) s.mem t.mem ∧ lv t.mem B (oM q d0 + 72 * q) 3 = 0 ∧
      lv t.mem B (oA q (oM q d0) + 72 * q) 3 = 0) ∧ Keep [.t4, .t2, .s0] s t := by
  obtain q2 := h.q2
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain d8 := h.d8
  have hn := h.scr.nowrap
  generalize eP : oM q d0 + 72 * q = P
  generalize eQ : oA q (oM q d0) + 72 * q = Q
  obtain bP : P + 72 * q + 24 = Q := by rw [← eP, ← eQ]; unfold oA; omega_using []
  obtain bQ : Q + 24 ≤ Z := by rw [← eQ]; unfold oA oM; omega_using [fit]
  obtain P8 : P % 8 = 0 := by rw [← eP]; unfold oM; omega_using [d8]
  obtain Q8 : Q % 8 = 0 := by omega_using [bP, P8]
  obtain p0 : off B (d0 + (64 * q + 16) + (64 * q + 16) + 72 * q) = off B P :=
    congrArg (off B) (by rw [← eP]; unfold oM; omega_using [])
  obtain r : WP isa (.block pads) s fun t => (t.mem = ((((((s.mem.writeW (off B P) 0#64).writeW (off B (P + 8)) 0#64).writeW
      (off B (P + 16)) 0#64).writeW (off B Q) 0#64).writeW (off B (Q + 8)) 0#64).writeW (off B (Q + 16)) 0#64)) ∧ Keep [.t4, .t2, .s0] s t := by
    obtain hs := h.scr
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold pads
    brun [h.a7, h.s5, n8_calc q6, exec_li, p0,
      show P + (72 * q + 24) = Q by omega_using [bP], show P + (72 * q + 32) = Q + 8 by omega_using [bP],
      show P + (72 * q + 40) = Q + 16 by omega_using [bP], show P + 72 * q + 24 = Q by omega_using [bP],
      show P + 72 * q + 32 = Q + 8 by omega_using [bP],
      show P + 72 * q + 40 = Q + 16 by omega_using [bP],
      hs.st (show P + 8 ≤ Z by omega_using [bP, bQ]), hs.st (show P + 8 + 8 ≤ Z by omega_using [bP, bQ]),
      hs.st (show P + 16 + 8 ≤ Z by omega_using [bP, bQ]), hs.st (show Q + 8 ≤ Z by omega_using [bQ]),
      hs.st (show Q + 8 + 8 ≤ Z by omega_using [bQ]), hs.st (show Q + 16 + 8 ≤ Z by omega_using [bQ]),
      hs.al8 (show P + 8 ≤ Z by omega_using [bP, bQ]) P8, hs.al8 (show P + 8 + 8 ≤ Z by omega_using [bP, bQ]) (by omega_using [P8]),
      hs.al8 (show P + 16 + 8 ≤ Z by omega_using [bP, bQ]) (by omega_using [P8]), hs.al8 (show Q + 8 ≤ Z by omega_using [bQ]) Q8,
      hs.al8 (show Q + 8 + 8 ≤ Z by omega_using [bQ]) (by omega_using [Q8]), hs.al8 (show Q + 16 + 8 ≤ Z by omega_using [bQ]) (by omega_using [Q8])]
  refine WP.mono r fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_, ?_⟩, kt⟩
  · rw [tm]
    obtain wo : ∀ (m : Mem) (d : Nat), oM q d0 ≤ d → d + 8 ≤ Q + 24 → Outside B (oM q d0) (144 * q + 48) m (m.writeW (off B d) 0#64) :=
      fun m d h1 h2 => (writeW_outside m B _ (by omega_using [h2, bQ, hn])).mono h1 (by
        rw [← eQ] at h2; unfold oA at h2; omega_using [h2])
    exact ((((((wo _ _ (by omega_using [eP]) (by omega_using [bP])).trans (wo _ _ (by omega_using [eP]) (by omega_using [bP]))).trans
      (wo _ _ (by omega_using [eP]) (by omega_using [bP]))).trans (wo _ _ (by omega_using [eP, bP]) (by omega_using []))).trans
      (wo _ _ (by omega_using [eP, bP]) (by omega_using []))).trans (wo _ _ (by omega_using [eP, bP]) (by omega_using [])))
  · obtain f : ∀ (m : Mem) (d e : Nat), e + 8 ≤ d → d + 8 ≤ Z → word (m.writeW (off B d) 0#64) B e = word m B e :=
      fun m d e h1 h2 => wd_ne m B _ (.inr h1) (by omega_using [h2, hn]) (by omega_using [h1, h2, hn])
    rw [lv_three, tm, f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ, bP]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ, bP]), word_writeW_self,
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ, bP]), word_writeW_self,
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), word_writeW_self]
    rfl
  · obtain f : ∀ (m : Mem) (d e : Nat), e + 8 ≤ d → d + 8 ≤ Z → word (m.writeW (off B d) 0#64) B e = word m B e :=
      fun m d e h1 h2 => wd_ne m B _ (.inr h1) (by omega_using [h2, hn]) (by omega_using [h1, h2, hn])
    rw [lv_three, tm, f _ _ _ (by omega_using []) (by omega_using [bQ]), f _ _ _ (by omega_using []) (by omega_using [bQ]), word_writeW_self,
      f _ _ _ (by omega_using []) (by omega_using [bQ]), word_writeW_self, word_writeW_self]
    rfl

/-! ## Packing -/

theorem limb_of_bit : ∀ j < 48, 64 * j * 1150 / 65536 = 64 * j / 57 := by decide +kernel

theorem pack_val {x y z : BitVec 64} {s : Nat} :
    (x >>> s + y <<< (57 - s) + z <<< 57 <<< (57 - s)).toNat =
      (x.toNat / 2 ^ s + y.toNat * 2 ^ (57 - s) + z.toNat * 2 ^ 57 * 2 ^ (57 - s)) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, srl_toNat, sll_toNat, sll_toNat, sll_toNat, Nat.mod_mul_mod]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]

/-- Array 6's offset. -/
abbrev o6 (q d0 : Nat) : Nat := d0 + 384 * q + 96

def packRegs : List Reg := [.t2, .t3, .t4, .t5, .t6, .a2, .a3, .a4, .a5, .s0, .s1, .s2, .s3, .s4]

theorem pack_ok {s : State} {B : Addr} {Z q d0 a : Nat} (h : Sp s B Z q d0) (h0 : s.gpr .t0 = BitVec.ofNat 64 (8 * q))
    (hA : AIn s.mem B q (oM q d0) a) :
    WP isa pack s fun t => (Outside B (o6 q d0) (64 * q) s.mem t.mem ∧ wordsVal t.mem B (o6 q d0) (8 * q) = a % 2 ^ (64 * (8 * q))) ∧
      Keep packRegs s t := by
  obtain q2 := h.q2
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain d8 := h.d8
  have hn := h.scr.nowrap
  unfold pack countLoop
  obtain e1 : BitVec.ofNat 64 (64 * q + 16) <<< 2 = BitVec.ofNat 64 (256 * q + 64) := by
    rw [sll_ofNat]; exact congrArg _ (by omega_using [])
  obtain e3 : off (BitVec.ofNat 64 (256 * q + 64)) (64 * q + 16 + (64 * q + 16)) + off B d0 = off B (o6 q d0) := by
    rw [BitVec.add_comm, show off (BitVec.ofNat 64 (256 * q + 64)) (64 * q + 16 + (64 * q + 16)) =
      BitVec.ofNat 64 (256 * q + 64 + (64 * q + 16 + (64 * q + 16))) from BitVec.ofNat_add .. |>.symm, off_add]
    exact congrArg (off B) (by unfold o6; omega_using [])
  obtain r : WP isa (.block ([.shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18)] ++ atA ++
      [.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .li .t6 0, .li .s4 57,
      .li .a2 1150, .addi .t5 .t0 0])) s fun t => (t.gpr .t4 = off B (oA q (oM q d0)) ∧ t.gpr .t3 = off B (o6 q d0) ∧
      t.gpr .t6 = 0#64 ∧ t.gpr .s4 = BitVec.ofNat 64 57 ∧ t.gpr .a2 = BitVec.ofNat 64 1150 ∧ t.gpr .t5 = BitVec.ofNat 64 (8 * q) ∧
      t.mem = s.mem) ∧ Keep [.t2, .t4, .t3, .t6, .s4, .a2, .t5] s t := by
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    obtain r : WP isa (.block [.shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18)]) s fun t =>
        (t.gpr .t2 = BitVec.ofNat 64 (72 * q) ∧ t.mem = s.mem) ∧ Keep [.t2] s t :=
      WP.keep _ (by brun [h.s5, n8_calc q6]) (by rfl) (by rfl)
    refine WP.mono r fun u ⟨⟨u2, um⟩, ku⟩ => ?_
    obtain hu := h.of ku (by decide) (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (atA_ok hu u2) fun v ⟨⟨v4, vm⟩, kv⟩ => ?_
    obtain hv := hu.of kv (by decide) (by decide)
    obtain r : WP isa (.block [.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .li .t6 0, .li .s4 57,
      .li .a2 1150, .addi .t5 .t0 0]) v fun t => (t.gpr .t3 = off B (o6 q d0) ∧
      t.gpr .t6 = 0#64 ∧ t.gpr .s4 = BitVec.ofNat 64 57 ∧ t.gpr .a2 = BitVec.ofNat 64 1150 ∧ t.gpr .t5 = BitVec.ofNat 64 (8 * q) ∧
      t.mem = v.mem) ∧ Keep [.t3, .t6, .s4, .a2, .t5] v t := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [hv.a7, hv.s5, e1, e3, exec_li, ((ku.trans kv).gpr (r := .t0) (by decide)).trans h0, BitVec.add_zero]
    exact WP.mono r fun t ⟨⟨a, b, c, d, e, f⟩, kt⟩ => ⟨⟨(kt.gpr (by decide)).trans v4, a, b, c, d, e, by rw [f, vm, um]⟩,
      ((ku.trans kv).trans kt).mono (by decide)⟩
  refine WP.seq (WP.mono r fun s₁ ⟨⟨x4, x3, x6, xs, xa, x5, m1⟩, k1⟩ => ?_)
  obtain bA : oA q (oM q d0) + 72 * q + 24 ≤ o6 q d0 := by unfold oA oM o6; omega_using []
  obtain bZ : o6 q d0 + 64 * q ≤ Z := by unfold o6; omega_using [fit, q2]
  obtain bA8 : oA q (oM q d0) % 8 = 0 := by unfold oA oM; omega_using [d8]
  obtain b68 : o6 q d0 % 8 = 0 := by unfold o6; omega_using [d8]
  refine WP.mono (wp_countdown (cnt := .t5) (N := 8 * q) (by omega_using [q6]) (by omega_using [q2]) (fun j t =>
      t.gpr .t4 = off B (oA q (oM q d0)) ∧ t.gpr .t3 = off B (o6 q d0 + 8 * j) ∧ t.gpr .t6 = BitVec.ofNat 64 (64 * j) ∧
      t.gpr .s4 = BitVec.ofNat 64 57 ∧ t.gpr .a2 = BitVec.ofNat 64 1150 ∧ Outside B (o6 q d0) (8 * j) s.mem t.mem ∧
      (∀ i < j, (word t.mem B (o6 q d0 + 8 * i)).toNat = a / 2 ^ (64 * i) % 2 ^ 64) ∧ Keep packRegs s t)
    (fun j hj t ⟨t4, t3, t6, ts, ta, to, tv, tk⟩ _ => ?_) ⟨x4, x3, x6, xs, xa, by rw [m1]; exact Outside.refl _ _ _ _,
      fun j hj => absurd hj (Nat.not_lt_zero j), k1.mono (by decide)⟩ x5)
    fun t ⟨_, _, _, _, _, to, tv, tk⟩ => ⟨⟨to.mono (Nat.le_refl _) (by omega_using []), wv_digits tv⟩, tk⟩
  obtain hk : 64 * j / 57 + 2 ≤ 9 * q + 2 := by omega_using [hj]
  generalize ek : 64 * j / 57 = k at hk
  obtain lm := limb_of_bit j (by omega_using [hj, q6])
  rw [ek] at lm
  obtain ⟨sh, hp, hsh⟩ : ∃ sh, 64 * j = 57 * k + sh ∧ sh < 57 := ⟨64 * j % 57, by rw [← ek]; omega_using [], by omega_using []⟩
  obtain rd : ∀ i ≤ 9 * q + 2, word t.mem B (oA q (oM q d0) + 8 * i) = word s.mem B (oA q (oM q d0) + 8 * i) := fun i hi =>
    to.word (by omega_using [bA, hi]) (by omega_using [bA, bZ, hi, hn])
  obtain R0 := rd k (by omega_using [hk])
  obtain R1 := rd (k + 1) (by omega_using [hk])
  obtain R2 := rd (k + 2) hk
  obtain a1 : (BitVec.ofNat 64 (64 * j) * BitVec.ofNat 64 1150) >>> 16 = BitVec.ofNat 64 k := by
    rw [← BitVec.ofNat_mul, srl_ofNat (by omega_using [hj, q6])]; exact congrArg _ lm
  obtain a2 : BitVec.ofNat 64 (64 * j) - BitVec.ofNat 64 k * BitVec.ofNat 64 57 = BitVec.ofNat 64 sh := by
    rw [← BitVec.ofNat_mul, sub_ofNat (by omega_using [hp])]; exact congrArg _ (by omega_using [hp])
  obtain a3 : BitVec.ofNat 64 57 - BitVec.ofNat 64 sh = BitVec.ofNat 64 (57 - sh) := sub_ofNat (Nat.le_of_lt hsh)
  obtain a4 : BitVec.ofNat 64 k <<< 3 + off B (oA q (oM q d0)) = off B (oA q (oM q d0) + 8 * k) := by
    rw [sll_ofNat, BitVec.add_comm, off_add]; exact congrArg (off B) (by omega_using [])
  obtain a5 : (BitVec.ofNat 64 sh).toNat % 64 = sh := by rw [BitVec.toNat_ofNat]; omega_using [hsh]
  obtain a6 : (BitVec.ofNat 64 (57 - sh)).toNat % 64 = 57 - sh := by rw [BitVec.toNat_ofNat]; omega_using [hsh]
  obtain r : WP isa (.block ([.mul .a3 .t6 .a2, .shift .srl .d .a3 .a3 16, .mul .a4 .a3 .s4, .sub .a4 .t6 .a4, .sub .a5 .s4 .a4,
      .shift .sll .d .a3 .a3 3, .add .a3 .a3 .t4, .load .d .s1 .a3 0, .load .d .s2 .a3 8, .load .d .s3 .a3 16,
      .shiftReg .srl .d .s1 .s1 .a4, .shiftReg .sll .d .s2 .s2 .a5, .shift .sll .d .s3 .s3 57,
      .shiftReg .sll .d .s3 .s3 .a5, .add .s1 .s1 .s2, .add .s1 .s1 .s3, .store .d .s1 .t3 0,
      .addi .t3 .t3 8, .addi .t6 .t6 64] ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun u =>
      (u.mem = t.mem.writeW (off B (o6 q d0 + 8 * j)) (word s.mem B (oA q (oM q d0) + 8 * k) >>> sh +
          word s.mem B (oA q (oM q d0) + 8 * (k + 1)) <<< (57 - sh) + word s.mem B (oA q (oM q d0) + 8 * (k + 2)) <<< 57 <<< (57 - sh)) ∧
        u.gpr .t6 = BitVec.ofNat 64 (64 * j + 64) ∧ u.gpr .t3 = off B (o6 q d0 + 8 * j + 8) ∧
        u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.a3, .a4, .a5, .s1, .s2, .s3, .t3, .t6, .t5] t u := by
    obtain hs := h.scr.congr tk.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [t3, t4, t6, ts, ta, a1, a2, a3, a4, a5, a6, ↓exec_srlReg', ↓exec_sllReg',
      hs.ld (show oA q (oM q d0) + 8 * k + 8 ≤ Z by omega_using [bA, bZ, hk]),
      hs.ld (show oA q (oM q d0) + 8 * k + 8 + 8 ≤ Z by omega_using [bA, bZ, hk]),
      hs.ld (show oA q (oM q d0) + 8 * k + 16 + 8 ≤ Z by omega_using [bA, bZ, hk]),
      hs.st (show o6 q d0 + 8 * j + 8 ≤ Z by omega_using [bZ, hj]),
      hs.al8 (show oA q (oM q d0) + 8 * k + 8 ≤ Z by omega_using [bA, bZ, hk]) (by omega_using [bA8]),
      hs.al8 (show oA q (oM q d0) + 8 * k + 8 + 8 ≤ Z by omega_using [bA, bZ, hk]) (by omega_using [bA8]),
      hs.al8 (show oA q (oM q d0) + 8 * k + 16 + 8 ≤ Z by omega_using [bA, bZ, hk]) (by omega_using [bA8]),
      hs.al8 (show o6 q d0 + 8 * j + 8 ≤ Z by omega_using [bZ, hj]) (by omega_using [b68]), ← BitVec.ofNat_add,
      show t.mem.readW (off B (oA q (oM q d0) + 8 * k)) 64 = word s.mem B (oA q (oM q d0) + 8 * k) from R0,
      show t.mem.readW (off B (oA q (oM q d0) + 8 * k + 8)) 64 = word s.mem B (oA q (oM q d0) + 8 * (k + 1)) from R1,
      show t.mem.readW (off B (oA q (oM q d0) + 8 * k + 16)) 64 = word s.mem B (oA q (oM q d0) + 8 * (k + 2)) from R2]
  refine WP.mono r fun u ⟨⟨um, u6, u3, u5⟩, ku⟩ => ?_
  obtain ou : Outside B (o6 q d0 + 8 * j) 8 t.mem u.mem := by rw [um]; exact writeW_outside _ B _ (by omega_using [bZ, hj, hn])
  refine ⟨⟨(ku.gpr (by decide)).trans t4, by rw [u3, Nat.mul_succ, Nat.add_assoc], by rw [u6, Nat.mul_succ],
    (ku.gpr (by decide)).trans ts, (ku.gpr (by decide)).trans ta,
    (to.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using [])), fun i hi => ?_,
    Keep.trans' tk (ku.mono (by decide))⟩, u5⟩
  by_cases hij : i < j
  · rw [ou.word (by omega_using [hij]) (by omega_using [bZ, hj, hij, hn])]; exact tv i hij
  · obtain rfl : i = j := by omega_using [hi, hij]
    rw [um, word_writeW_self, pack_val]
    refine (digit_64 (r := lv s.mem B (oA q (oM q d0) + 8 * (k + 3)) (9 * q - k)) hp hsh ?_).symm
    rw [← hA.pads, show 9 * q + 3 = k + (3 + (9 * q - k)) by omega_using [hk],
      lv_div (fun i' hi' => hA.lim i' (by omega_using [hi', hk])), lv_split3, lv_three,
      show oA q (oM q d0) + 8 * k + 8 = oA q (oM q d0) + 8 * (k + 1) by omega_using [],
      show oA q (oM q d0) + 8 * k + 16 = oA q (oM q d0) + 8 * (k + 2) by omega_using [],
      show oA q (oM q d0) + 8 * k + 24 = oA q (oM q d0) + 8 * (k + 3) by omega_using []]
    omega_using []

end VG.Proof.Bignum.RISCV64.Pow57
