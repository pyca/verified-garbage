module

public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontSqr
public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Round
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The Miller–Rabin round on RISC-V: the context

`MCtx`: the working space of the round, its 28 arrays of `w + 2` words
(the compact layout, `Proof.MillerRabin.Round.compact`), with the round's
registers set (`a7` array 0's base, `s5` the arrays' size, `t0` `w`, `t1`
`-c⁻¹ mod 2⁶⁴`, `setup_ok`) and the candidate in array 0. `Consts`: what the
round reads and never writes. The round writes only arrays 2, 3, 5, 6 and
the table (`Mut`).

The pieces every part of the round uses, as on PPC64LE
(`Proof/MillerRabin/PPC64LE/{Ctx,Eq,Sel}.lean`) and in the windowed
exponentiation (`Proof/Bignum/RISCV64/ModExpWin.lean`, for 24 arrays): a
Montgomery multiplication (`mont_ok`) and square (`sqr_ok`), a copy
(`copy_ok`), a masked selection (`sel_ok`) and a comparison (`eqMask_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.MillerRabin.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep Arrays)
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)
open VG.Impl.Bignum.RISCV64.ModExp (sqrOp copy ones)

/-- Array `j`'s number: its `w` words. -/
abbrev A (m : Mem) (B : Addr) (w j : Nat) : Nat := wordsVal m B (slot w j) w

/-- All ones if `b`, else 0. -/
abbrev mask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem slot_lt {w j k : Nat} (h : j < k) : slot w j + 8 * (w + 2) ≤ slot w k := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega_arith)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega_arith

/-! ## The context -/

/-- The working space at `B` (`Z` bytes) with 28 arrays, the round's
registers set, and the candidate `N` in array 0. -/
structure MCtx (s : State) (B : Addr) (Z w N : Nat) : Prop where
  scr : Scr s B Z
  w4 : 4 ≤ w
  w128 : w ≤ 128
  hZ : slot w 28 ≤ Z
  a7 : s.gpr .a7 = off B (slot w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 w
  inv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  n : A s.mem B w 0 = N

/-- The registers `MCtx` reads. -/
def ctxRegs : List Reg := [.a7, .s5, .t0, .t1]

theorem MCtx.sl {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {j : Nat} (hj : j < 28) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_lt hj) h.hZ

theorem MCtx.nw {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) : B.toNat + slot w 28 ≤ 2 ^ 64 := by
  have := h.scr.nowrap; have := h.hZ; omega_arith

theorem MCtx.w2 {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) : 2 ≤ w := by
  have := h.w4; omega_arith

theorem MCtx.w31 {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) : w < 2 ^ 31 := by
  have := h.w128; omega_arith

/-- An array none of `js`, below 28, keeps its value. -/
theorem arr_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {j : Nat}
    (hj : j < 28) (hjs : ∀ k ∈ js, k ≠ j) (hn : B.toNat + slot w 28 ≤ 2 ^ 64) : A m' B w j = A m B w j := by
  have := slot_lt (w := w) hj
  exact Pub.arrays_V h hjs (by omega_arith)

/-- One array written: `Outside` of up to its whole size. -/
theorem arr1 {B : Addr} {w o n : Nat} {m m' : Mem} (h : Outside B (slot w o) n m m') (hn : n ≤ 8 * (w + 2)) :
    Arrays B w [o] m m' :=
  Arrays.of_outside (by simp) h (Nat.le_refl _) (by omega_arith)

/-- After code writing only arrays `js` (none of them 0) and no register of
`ctxRegs`. -/
theorem MCtx.of {s t : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ctxRegs, r ∉ rs) {js : List Nat} (o : Arrays B w js s.mem t.mem) (hjs : ∀ j ∈ js, j ≠ 0) :
    MCtx t B Z w N := by
  have hn := h.nw
  have s0 := slot_lt (w := w) (show 0 < 28 by decide)
  have g := fun r hr => k.gpr (r := r) (hrs r hr)
  refine ⟨h.scr.congr k.2.2, h.w4, h.w128, h.hZ, (g .a7 (by decide)).trans h.a7,
    (g .s5 (by decide)).trans h.s5, (g .t0 (by decide)).trans h.t0, ?_, ?_⟩
  · have hw0 : Mont.word t.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
      o.word_eq (fun j hj => by
        have := slot_sep (w := w) (hjs j hj).symm
        have : 8 ≤ 8 * (w + 2) := by omega_arith
        omega_arith) (by omega_arith)
    rw [g .t1 (by decide), hw0]
    exact h.inv
  · rw [← h.n]
    exact arr_eq o (by decide) (fun j hj => hjs j hj) hn

theorem MCtx.regs {s t : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ctxRegs, r ∉ rs) (hm : t.mem = s.mem) : MCtx t B Z w N :=
  h.of k hrs (js := []) (fun x _ => by rw [hm]) (fun _ h => absurd h List.not_mem_nil)

/-! ## What the round may change -/

/-- The arrays the round writes: 2, 3, 5, 6 and the table, 11 to 26. -/
def mutArrs : List Nat := [2, 3, 5, 6, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- Memory that changes only in the arrays the round writes. -/
abbrev Mut (B : Addr) (w : Nat) (m m' : Mem) : Prop := Arrays B w mutArrs m m'

theorem Mut.of {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ j ∈ js, j ∈ mutArrs := by decide) : Mut B w m m' :=
  h.mono hjs

theorem Mut.trans {B : Addr} {w : Nat} {m₁ m₂ m₃ : Mem} (a : Mut B w m₁ m₂) (b : Mut B w m₂ m₃) :
    Mut B w m₁ m₃ :=
  Arrays.trans a b

/-! ## The constants -/

/-- What the round reads and never writes (the candidate is `MCtx.n`). -/
structure Consts (m : Mem) (B : Addr) (w c : Nat) : Prop where
  one : A m B w aOne = 2 ^ (64 * w) % c
  minus : A m B w aMinus = c - 2 ^ (64 * w) % c
  e : A m B w aE = Proof.RsaKeyGen.mrE c
  l : Mont.word m B (slot w aE + 8 * w) = BitVec.twoPow 64 (Proof.RsaKeyGen.mrA c % 64)

theorem Consts.of_mut {m m' : Mem} {B : Addr} {w c : Nat} (h : Consts m B w c) (hm : Mut B w m m')
    (hn : B.toNat + slot w 28 ≤ 2 ^ 64) : Consts m' B w c := by
  have hne : ∀ j, j ∉ mutArrs → ∀ k ∈ mutArrs, k ≠ j := fun j hj k hk e => hj (e ▸ hk)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [arr_eq hm (by decide) (hne _ (by decide)) hn]; exact h.one
  · rw [arr_eq hm (by decide) (hne _ (by decide)) hn]; exact h.minus
  · rw [arr_eq hm (by decide) (hne _ (by decide)) hn]; exact h.e
  · rw [← h.l]
    have h27 := slot_lt (w := w) (show aE < 28 by decide)
    refine hm.word_eq (fun j hj => ?_) (by simp only [aE] at h27 ⊢; omega_arith)
    simp only [mutArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [aE] at h27 ⊢
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp only [slot] at h27 ⊢ <;> omega_arith

/-! ## Montgomery multiplications and squares -/

/-- `montOp o a b`. -/
theorem mont_ok {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {o a b : Nat} (ho : o < 28)
    (ha : a < 28) (hb : b < 28) (ho0 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (hB : A s.mem B w b < N) :
    WP isa (montOp o a b) s fun t =>
      (MCtx t B Z w N ∧ A t.mem B w o < N ∧
        A t.mem B w o * 2 ^ (64 * w) % N = A s.mem B w a * A s.mem B w b % N ∧
        Arrays B w [2, 3, o] s.mem t.mem) ∧ Keep Pub.montRegs s t := by
  refine WP.mono (Pub.montOpN_ok h.scr (n := 28) (by decide) ho ha hb ho2 ho3 ha2 hb2 h.w2 h.w31 h.hZ h.a7 h.s5
    h.t0 h.inv (by rw [show wordsVal s.mem B (slot w 0) w = N from h.n]; exact hB))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  rw [show wordsVal s.mem B (slot w 0) w = N from h.n] at hlt he
  exact ⟨⟨h.of k (by decide) out (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith), hlt, he, out⟩, k⟩

/-- The registers a square writes. -/
def sqRegs : List Reg := [.a2, .a3, .a5, .a6] ++ sqrRegs

/-- `sqrOp o a p`, the temporary `p`. -/
theorem sqr_ok {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {o a p : Nat} (ho : o < 28)
    (ha : a < 28) (hp : p < 28) (ho0 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (ha3 : a ≠ 3)
    (hp0 : p ≠ 0) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpo : p ≠ o) (hA : A s.mem B w a < N) :
    WP isa (sqrOp o a p) s fun t =>
      (MCtx t B Z w N ∧ A t.mem B w o < N ∧
        A t.mem B w o * 2 ^ (64 * w) % N = A s.mem B w a * A s.mem B w a % N ∧
        Arrays B w [2, 3, p, o] s.mem t.mem) ∧ Keep sqRegs s t := by
  unfold sqrOp
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) h.a7 h.s5 o) fun t₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a3) (by decide) ((k1.gpr (by decide)).trans h.a7)
    ((k1.gpr (by decide)).trans h.s5) a) fun t₂ ⟨⟨a3, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k12.gpr (by decide)).trans h.a7)
    ((k12.gpr (by decide)).trans h.s5) 2) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k13.gpr (by decide)).trans h.a7)
    ((k13.gpr (by decide)).trans h.s5) p) fun t₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  have c4 := h.regs k14 (by decide) hm
  have g2 : t₄.gpr .a2 = off B (slot w o) := by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), a2]
  have g3 : t₄.gpr .a3 = off B (slot w a) := by rw [k4.gpr (by decide), k3.gpr (by decide), a3]
  have g5 : t₄.gpr .a5 = off B (slot w 2) := by rw [k4.gpr (by decide), a5]
  rw [← hm] at hA ⊢
  refine WP.mono (sqrTailN_ok c4.scr (n := 28) (by decide) ho ha hp ho2 ho3 ha2 ha3 hp0 hp2 hp3 hpo c4.w2 c4.w31
    c4.hZ g2 g3 g5 a6 c4.a7 c4.t0 c4.inv (by rw [show wordsVal t₄.mem B (slot w 0) w = N from c4.n]; exact hA))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  rw [show wordsVal t₄.mem B (slot w 0) w = N from c4.n] at hlt he
  exact ⟨⟨c4.of k (by decide) out (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith), hlt, he, out⟩,
    (k14.trans k).mono (by decide)⟩

/-! ## Copies and selections -/

/-- `selectAcc64`, its bases already in `a2` (the output), `a5` and `a6`,
and its mask in `s4`. -/
theorem sel_ok {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {b : Bool} {o a t : Nat}
    (ho : o < 28) (ha : a < 28) (ht : t < 28) (hoa : o ≠ a) (hot : o ≠ t)
    (h2 : s.gpr .a2 = off B (slot w o)) (h5 : s.gpr .a5 = off B (slot w a)) (h6 : s.gpr .a6 = off B (slot w t))
    (h4 : s.gpr .s4 = mask b) :
    WP isa selectAcc64 s fun s' =>
      (A s'.mem B w o = (if b then A s.mem B w a else A s.mem B w t) ∧
        Outside B (slot w o) (8 * w) s.mem s'.mem) ∧ Keep [.a0, .t3, .t4, .t5, .s2, .s3] s s' := by
  have sep := fun {j k : Nat} (hjk : j ≠ k) => slot_sep (w := w) hjk
  have hO := h.sl ho
  have hA := h.sl ha
  have hT := h.sl ht
  have al := slot_al w
  exact WP.mono (selectAcc64_ok h.scr (dA := slot w a) (dT := slot w t) (dO := slot w o) (w := w) (b := b)
      h5 h6 h2 h.t0 h4 (by have := h.w2; omega_arith) h.w31 (al a) (al t) (al o)
      (by omega_arith) (by omega_arith) (by omega_arith)
      (by have := sep hoa; omega_arith) (by have := sep hot; omega_arith)) fun s' ⟨hv, hout, k⟩ =>
    ⟨⟨hv, hout⟩, k⟩

/-- The registers `copy` writes. -/
def copyRegs : List Reg := [.a0, .t2, .t3, .t4, .t5, .s2, .s3, .s4, .a2, .a5, .a6]

/-- `copy o a`: array `o` := array `a`. -/
theorem copy_ok {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {o a : Nat} (ho : o < 28)
    (ha : a < 28) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t =>
      (A t.mem B w o = A s.mem B w a ∧ Outside B (slot w o) (8 * w) s.mem t.mem) ∧ Keep copyRegs s t := by
  unfold copy
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Win.ones_ok s) fun t₁ ⟨⟨h4, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k1.gpr (by decide)).trans h.a7)
    ((k1.gpr (by decide)).trans h.s5) a) fun t₂ ⟨⟨a5, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k12.gpr (by decide)).trans h.a7)
    ((k12.gpr (by decide)).trans h.s5) a) fun t₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k13.gpr (by decide)).trans h.a7)
    ((k13.gpr (by decide)).trans h.s5) o) fun t₄ ⟨⟨a2, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (sel_ok (h.regs k14 (by decide) hm) (b := true) ho ha ha hoa hoa a2
    (by rw [k4.gpr (by decide), k3.gpr (by decide), a5]) (by rw [k4.gpr (by decide), a6])
    (by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), h4]))
    fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨by simpa only [ite_true] using hv, hout⟩, (k14.trans k).mono (by decide)⟩

/-! ## Comparisons -/

/-- Two numbers of 64-bit words are equal exactly when their words are. -/
theorem wordsVal_eq_iff (m : Mem) (B : Addr) (da db : Nat) :
    ∀ n, wordsVal m B da n = wordsVal m B db n ↔
      ∀ k < n, Mont.word m B (da + 8 * k) = Mont.word m B (db + 8 * k)
  | 0 => ⟨fun _ _ h => absurd h (by omega_arith), fun _ => rfl⟩
  | n + 1 => by
    rw [wordsVal_succ_top, wordsVal_succ_top]
    have ha := wordsVal_lt m B da n
    have hb := wordsVal_lt m B db n
    constructor
    · intro h
      have hd : (Mont.word m B (da + 8 * n)).toNat = (Mont.word m B (db + 8 * n)).toNat := by
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

/-- `(0 <u x) − 1`: the mask of `x = 0`. -/
theorem zero_mask (x : BitVec 64) : (if 0#64 < x then 1 else 0) - 1#64 = mask (decide (x = 0)) := by
  by_cases hx : x = 0
  · subst hx; decide
  · have hlt : 0#64 < x := by
      rw [BitVec.lt_def]
      exact Nat.pos_of_ne_zero fun h' => hx (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [hlt, ↓reduceIte, hx, decide_false]
    rfl

/-- The registers `eqMask d a b` writes, but `d`. -/
def eqRegs : List Reg := [.t3, .t4, .t5, .s0, .s1, .s2, .s3]

/-- `(w − 1) mod 4 + 1` words, in bytes. -/
theorem eq_step {w : Nat} (h1 : 1 ≤ w) (hw : w < 2 ^ 31) :
    ((BitVec.ofNat 64 w - BitVec.ofNat 64 1 &&& BitVec.ofNat 64 3) + BitVec.ofNat 64 1) <<< 3 =
      BitVec.ofNat 64 (8 * ((w - 1) % 4 + 1)) := by
  rw [show BitVec.ofNat 64 w - BitVec.ofNat 64 1 = BitVec.ofNat 64 (w - 1) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_and, show (BitVec.ofNat 64 3).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- The groups of four words. -/
theorem eq_groups {w : Nat} (hw : w < 2 ^ 31) :
    (BitVec.ofNat 64 w + BitVec.ofNat 64 3) >>> 2 = BitVec.ofNat 64 ((w + 3) / 4) := by
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem eqInit_ok {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) (a b : Nat) :
    WP isa (.block (eqInit a b)) s fun t =>
      (t.gpr .t3 = off B (slot w a) ∧ t.gpr .t4 = off B (slot w b) ∧ t.gpr .t5 = BitVec.ofNat 64 ((w + 3) / 4) ∧
        t.gpr .s3 = BitVec.ofNat 64 (8 * ((w - 1) % 4 + 1)) ∧ t.gpr .s0 = 0 ∧ t.mem = s.mem) ∧
        Keep [.t3, .t4, .t5, .s3, .s0] s t := by
  have hw := h.w4
  unfold eqInit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 a) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  have e1 := h.regs k1 (by decide) m1
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) e1.a7 e1.s5 b) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have e2 := e1.regs k2 (by decide) m2
  have hpre : WP isa (.block [.addi .t5 .t0 3, .shift .srl .d .t5 .t5 2, .addi .s3 .t0 (-1),
      .logicImm .and .s3 .s3 3, .addi .s3 .s3 1, .shift .sll .d .s3 .s3 3, .li .s0 0]) t₂ fun t₃ =>
      (t₃.gpr .t5 = BitVec.ofNat 64 ((w + 3) / 4) ∧ t₃.gpr .s3 = BitVec.ofNat 64 (8 * ((w - 1) % 4 + 1)) ∧
        t₃.gpr .s0 = 0 ∧ t₃.mem = t₂.mem) ∧ Keep [.t5, .s3, .s0] t₂ t₃ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li (show imm12 0 by decide), e2.t0, eq_groups h.w31,
      eq_step (show 1 ≤ w by omega_arith) h.w31]
    rfl
  refine WP.mono hpre fun t ⟨⟨t5, t3, t0, tm⟩, kt⟩ => ⟨⟨?_, ?_, t5, t3, t0, by rw [tm, m2, m1]⟩,
    ((k1.trans k2).trans kt).mono (by decide)⟩
  · rw [kt.gpr (by decide), k2.gpr (by decide), a3]
  · rw [kt.gpr (by decide), a4]

/-- Word `k` of a group. -/
theorem eqWord_ok {s : State} {B : Addr} {Z p q k : Nat} (hs : Scr s B Z) (h3 : s.gpr .t3 = off B p)
    (h4 : s.gpr .t4 = off B q) (hp8 : p % 8 = 0) (hq8 : q % 8 = 0) (hk : k < 4) (hp : p + 32 ≤ Z) (hq : q + 32 ≤ Z) :
    WP isa (.block (eqWord k)) s fun t =>
      (t.gpr .s0 = s.gpr .s0 ||| (Mont.word s.mem B (p + 8 * k) ^^^ Mont.word s.mem B (q + 8 * k)) ∧
        t.mem = s.mem) ∧ Keep [.s0, .s1, .s2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold eqWord
  brun [h3, h4, show 8 * k < 2048 by omega_arith, hs.ld (show p + 8 * k + 8 ≤ Z by omega_arith),
    hs.ld (show q + 8 * k + 8 ≤ Z by omega_arith), hs.al8 (show p + 8 * k + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show q + 8 * k + 8 ≤ Z by omega_arith) (by omega_arith)]

theorem eqWords_succ (n : Nat) : eqWords (n + 1) = eqWords n ++ eqWord n := by
  simp only [eqWords, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The first `n` words of a group: `s0` stays zero exactly if they are equal. -/
theorem eqWords_ok {s : State} {B : Addr} {Z p q : Nat} (hs : Scr s B Z) (h3 : s.gpr .t3 = off B p)
    (h4 : s.gpr .t4 = off B q) (hp8 : p % 8 = 0) (hq8 : q % 8 = 0) (hp : p + 32 ≤ Z) (hq : q + 32 ≤ Z) :
    ∀ n ≤ 4, WP isa (.block (eqWords n)) s fun t =>
      ((t.gpr .s0 = 0 ↔ s.gpr .s0 = 0 ∧ ∀ k < n, Mont.word s.mem B (p + 8 * k) = Mont.word s.mem B (q + 8 * k)) ∧
        t.mem = s.mem) ∧ Keep [.s0, .s1, .s2] s t
  | 0, _ => WP.block_nil ⟨⟨⟨fun h => ⟨h, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩, fun h => h.1⟩, rfl⟩,
      Keep.refl _ _⟩
  | n + 1, hn => by
    rw [eqWords_succ, WP.block_append_iff]
    refine WP.mono (eqWords_ok hs h3 h4 hp8 hq8 hp hq n (by omega_arith)) fun t ⟨⟨t0, tm⟩, tk⟩ => ?_
    refine WP.mono (eqWord_ok (hs.congr tk.2.2) ((tk.gpr (by decide)).trans h3) ((tk.gpr (by decide)).trans h4)
      hp8 hq8 (by omega_arith) hp hq) fun u ⟨⟨u0, um⟩, uk⟩ => ⟨⟨?_, um.trans tm⟩, Keep.trans' tk uk⟩
    rw [u0, or_xor_zero, t0, tm]
    constructor
    · rintro ⟨⟨h0, hk⟩, he⟩
      refine ⟨h0, fun k hk' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
      · exact hk k hk'
      · exact he
    · rintro ⟨h0, hk⟩
      exact ⟨⟨h0, fun k hk' => hk k (by omega_arith)⟩, hk n (by omega_arith)⟩

/-- The first word of group `i`, of `w` words from the last group's end. -/
def eqAt (w i : Nat) : Nat := if i = 0 then 0 else (w - 1) % 4 + 1 + 4 * (i - 1)

/-- The words compared by the first `i` groups. -/
def eqTo (w i : Nat) : Nat := if i = 0 then 0 else eqAt w (i - 1) + 4

theorem eqAt_succ (w i : Nat) : eqAt w (i + 1) = eqAt w i + if i = 0 then (w - 1) % 4 + 1 else 4 := by
  unfold eqAt
  by_cases h : i = 0
  · subst h; simp
  · simp only [h, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false]; omega_arith

theorem eqTo_succ (w i : Nat) : eqTo w (i + 1) = eqAt w i + 4 := by
  simp only [eqTo, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]

theorem eqTo_at (w i : Nat) : eqAt w i ≤ eqTo w i ∧ eqTo w i ≤ eqAt w i + 4 := by
  cases i with
  | zero => simp [eqAt, eqTo]
  | succ i => rw [eqTo_succ, eqAt_succ]; split <;> omega_arith

theorem eqAt_le {w i : Nat} (hw : 4 ≤ w) (hi : i < (w + 3) / 4) : eqAt w i + 4 ≤ w := by
  unfold eqAt; split <;> omega_arith

theorem eqTo_last {w : Nat} (hw : 4 ≤ w) : eqTo w ((w + 3) / 4) = w := by
  simp only [eqTo, eqAt]
  by_cases h : w = 4
  · subst h; rfl
  · simp only [show ¬ (w + 3) / 4 = 0 by omega_arith, show ¬ (w + 3) / 4 - 1 = 0 by omega_arith, ↓reduceIte]
    omega_arith

/-- `eqMask d a b`: `d` := all ones if arrays `a` and `b` are equal, else 0. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) {d : Reg} (hd : d = .a3 ∨ d = .a4)
    {a b : Nat} (ha : a < 28) (hb : b < 28) :
    WP isa (eqMask d a b) s fun t =>
      (t.gpr d = mask (decide (A s.mem B w a = A s.mem B w b)) ∧ t.mem = s.mem) ∧ Keep (d :: eqRegs) s t := by
  have hA := h.sl ha
  have hB := h.sl hb
  have hw := h.w4
  have hw' := h.w128
  have al := slot_al w
  unfold eqMask
  refine WP.seq (WP.mono (eqInit_ok h a b) fun t₁ ⟨⟨a3, a4, a5, as, a0, m1⟩, k1⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w a + 8 * eqAt w i) ∧ t.gpr .t4 = off B (slot w b + 8 * eqAt w i) ∧
      t.gpr .s3 = BitVec.ofNat 64 (8 * if i = 0 then (w - 1) % 4 + 1 else 4) ∧
      (t.gpr .s0 = 0 ↔ ∀ k < eqTo w i, Mont.word s.mem B (slot w a + 8 * k) = Mont.word s.mem B (slot w b + 8 * k)) ∧
      t.mem = s.mem ∧ Keep eqRegs s t
  refine WP.seq (WP.mono (wp_countdown (body := .block (eqWords 4 ++ eqNext ++ ([.addi .t5 .t5 (-1)] : List Instr)))
      (cnt := .t5) (N := (w + 3) / 4) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, j4, js, j0, jm, jk⟩ _ => ?_)
    ⟨a3, a4, as, ⟨fun _ _ hk => absurd hk (Nat.not_lt_zero _), fun _ => a0⟩, m1, k1.mono (by decide)⟩ a5)
    fun t hI => ?_)
  · have hs := h.scr.congr jk.2.2
    have hle := eqAt_le hw hi
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (eqWords_ok hs j3 j4 (by have := al a; omega_arith) (by have := al b; omega_arith)
      (by omega_arith) (by omega_arith) 4 (Nat.le_refl _)) fun u ⟨⟨u0, um⟩, uk⟩ => ?_
    have hst : WP isa (.block (eqNext ++ ([.addi .t5 .t5 (-1)] : List Instr))) u fun v =>
        (v.gpr .t3 = u.gpr .t3 + u.gpr .s3 ∧ v.gpr .t4 = u.gpr .t4 + u.gpr .s3 ∧ v.gpr .s3 = BitVec.ofNat 64 32 ∧
          v.gpr .t5 = u.gpr .t5 - BitVec.ofNat 64 1 ∧ v.mem = u.mem) ∧ Keep [.t3, .t4, .t5, .s3] u v := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      unfold eqNext
      brun [exec_li]
    refine WP.mono hst fun v ⟨⟨v3, v4, vs, v5, vm⟩, vk⟩ => ⟨⟨?_, ?_, ?_, ?_, by rw [vm, um, jm],
      ((jk.trans uk).trans vk).mono (by decide)⟩, by rw [v5, uk.gpr (by decide)]⟩
    · rw [v3, uk.gpr (by decide), uk.gpr (by decide), j3, js, off_add, eqAt_succ, Nat.mul_add, Nat.add_assoc]
    · rw [v4, uk.gpr (by decide), uk.gpr (by decide), j4, js, off_add, eqAt_succ, Nat.mul_add, Nat.add_assoc]
    · rw [vs]; rfl
    · have ht := eqTo_at w i
      rw [vk.gpr (by decide), u0, j0, jm, eqTo_succ]
      constructor
      · rintro ⟨hk, hg⟩ k hk'
        by_cases hc : k < eqTo w i
        · exact hk k hc
        · have := hg (k - eqAt w i) (by omega_arith)
          rwa [show slot w a + 8 * eqAt w i + 8 * (k - eqAt w i) = slot w a + 8 * k by omega_arith,
            show slot w b + 8 * eqAt w i + 8 * (k - eqAt w i) = slot w b + 8 * k by omega_arith] at this
      · intro hk
        refine ⟨fun k hk' => hk k (by omega_arith), fun k hk' => ?_⟩
        have := hk (eqAt w i + k) (by omega_arith)
        rwa [Nat.mul_add, ← Nat.add_assoc, ← Nat.add_assoc] at this
  · obtain ⟨_, _, _, j0, jm, jk⟩ := hI
    rw [eqTo_last hw] at j0
    have hv : (A s.mem B w a = A s.mem B w b) ↔ t.gpr .s0 = 0 := by
      rw [wordsVal_eq_iff, j0]
    have hfin : WP isa (.block [.li .s1 0, .sltu .s1 .s1 .s0, .addi d .s1 (-1)]) t fun t' =>
        (t'.gpr d = mask (decide (A s.mem B w a = A s.mem B w b)) ∧ t'.mem = t.mem) ∧ Keep [.s1, d] t t' := by
      rcases hd with rfl | rfl <;>
      · refine WP.keep _ ?_ (by rfl) (by rfl)
        brun [exec_li (show imm12 0 by decide)]
        rw [zero_mask]
        simp only [hv]
    refine WP.mono hfin fun t' ⟨⟨hd', hm'⟩, k'⟩ => ⟨⟨hd', hm'.trans jm⟩, (Keep.trans jk k').mono ?_⟩
    rcases hd with rfl | rfl <;> decide

/-! ## The registers -/

theorem shl3_ofNat' (w : Nat) :
    BitVec.ofNat 64 w <<< 3 + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (w + 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `setup`: the round's registers, from the working space at `a0`. -/
theorem setup_ok {s : State} {B : Addr} {Z w N : Nat} (hs : Scr s B Z) (h0 : s.gpr .a0 = B)
    (hw : Mont.word s.mem B (8 * sW) = BitVec.ofNat 64 w) (hw4 : 4 ≤ w) (hw128 : w ≤ 128)
    (hZ : slot w 28 ≤ Z)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (Mont.word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hn : A s.mem B w 0 = N) :
    WP isa (.block setup) s fun t => (MCtx t B Z w N ∧ t.mem = s.mem) ∧ Keep [.a7, .t0, .s5, .t1] s t := by
  have h28 : 256 ≤ slot w 28 := by simp only [slot, Impl.Bignum.hdrBytes]; omega_arith
  have hb : WP isa (.block setup) s fun t =>
      (t.gpr .a7 = off B (slot w 0) ∧ t.gpr .t0 = BitVec.ofNat 64 w ∧
        t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .t1 = Mont.word s.mem B (8 * sMinv) ∧
        t.mem = s.mem) ∧ Keep [.a7, .t0, .s5, .t1] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold setup
    have e0 : off B (slot w 0) = B + BitVec.ofNat 64 256 := by simp [slot, Impl.Bignum.hdrBytes]
    have hw48 : s.mem.readW (B + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 w := hw
    have l48 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 48) 8 := hs.ld (d := 48) (by omega_arith)
    have l56 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 56) 8 := hs.ld (d := 56) (by omega_arith)
    have g48 : (B + BitVec.ofNat 64 48).toNat % 8 = 0 := hs.al8 (d := 48) (by omega_arith) (by decide)
    have g56 : (B + BitVec.ofNat 64 56).toNat % 8 = 0 := hs.al8 (d := 56) (by omega_arith) (by decide)
    brun [h0, l48, l56, g48, g56, hw48, sW, sMinv, Impl.Bignum.hdrBytes, e0, shl3_ofNat' w]
  refine WP.mono hb fun t ⟨⟨t7, t0, t5, t1, tm⟩, k⟩ =>
    ⟨⟨⟨hs.congr k.2.2, hw4, hw128, hZ, t7, t5, t0, by rw [t1, tm]; exact hinv, by rw [tm]; exact hn⟩, tm⟩, k⟩

end VG.Proof.MillerRabin.RISCV64
