module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: the arrays

In a working space (`Env`): `a7` moved to array `j` and back (`adds_ok`,
`subs_ok`); `loadArr_ok`, a number's octets into array `j`, its word `w`
zeroed first; `zeroArr_ok`; `below_ok`, the mask of an array being below the
modulus in array 0 (`subMod64`'s borrow); `copy_ok`, an array's `w + 2`
words into another.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

theorem slot_succ (w j : Nat) : slot w (j + 1) = slot w j + 8 * (w + 2) := by
  unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega

/-- `j` of `add a7, a7, s5`: `a7` from array `i` to array `i + j`. -/
theorem adds_ok {B : Addr} {w i : Nat} : ∀ (j : Nat) {t : State},
    t.gpr .a7 = off B (slot w i) → t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) →
    WP isa (.block (List.replicate j (.add .a7 .a7 .s5))) t fun t' =>
      (t'.gpr .a7 = off B (slot w (i + j)) ∧ t'.mem = t.mem) ∧ Keep [.a7] t t'
  | 0, t, h7, _ => WP.block_nil ⟨⟨h7, rfl⟩, Keep.refl _ _⟩
  | j + 1, t, h7, h5 => by
    rw [List.replicate_succ', WP.block_append_iff]
    refine WP.mono (adds_ok j h7 h5) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1, (k1.gpr (r := .s5) (by decide)).trans h5]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write_self, off_add, ← Nat.add_assoc, slot_succ]

/-- `j` of `sub a7, a7, s5`: `a7` from array `i + j` back to array `i`. -/
theorem subs_ok {B : Addr} {w i : Nat} (hB : B.toNat + slot w (i + 28) ≤ 2 ^ 64) : ∀ (j : Nat) {t : State},
    j ≤ 28 → t.gpr .a7 = off B (slot w (i + j)) → t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) →
    WP isa (.block (back j)) t fun t' =>
      (t'.gpr .a7 = off B (slot w i) ∧ t'.mem = t.mem) ∧ Keep [.a7] t t'
  | 0, t, _, h7, _ => WP.block_nil ⟨⟨h7, rfl⟩, Keep.refl _ _⟩
  | j + 1, t, hj, h7, h5 => by
    unfold back
    rw [List.replicate_succ]
    have e : off B (slot w (i + (j + 1))) - BitVec.ofNat 64 (8 * (w + 2)) = off B (slot w (i + j)) := by
      rw [off_sub B (by rw [← Nat.add_assoc, slot_succ]; omega), ← Nat.add_assoc, slot_succ, Nat.add_sub_cancel]
    refine Steps.WP.cons exec_sub ?_
    refine WP.mono (subs_ok hB j (t := t.write .a7 (t.gpr .a7 - t.gpr .s5)) (by omega)
      (by rw [gpr_write_self, h7, h5, e]) (by rw [gpr_write_of_ne _ _ (by decide)]; exact h5))
      fun t' ⟨⟨h1, m1⟩, k1⟩ => ⟨⟨h1, by rw [m1]; rfl⟩, ((Keep.write _ _ _).trans k1).mono (by simp)⟩

/-- A buffer's bytes are those of a memory that changed only in the working
space. -/
theorem bytesAt_out {B I : Addr} {Z o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off I i ≠ x) :
    Spec.Rsa.bytesAt m' I k = Spec.Rsa.bytesAt m I k := by
  rw [VG.Proof.Bignum.bytesAt_eq, VG.Proof.Bignum.bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  by_contra hc
  exact hsep i hi (I + BitVec.ofNat 64 i) (by simp only [ofs] at hc ⊢; omega) rfl

/-- The registers `loadArr` writes. -/
def loadRegs : List Reg := [.a0, .a7, .s0, .t3, .t4, .t5]

/-- `loadArr j`: the `k ≤ 8 w` octets at `N` (`s7`, `k` in `s8`), most
significant first, into array `j`, whose word `w` is 0; `a7` back to array 0. -/
theorem loadArr_ok {s : State} {B N : Addr} {Z w k j : Nat} (h : Env s B Z w) (hj : j < 28)
    (h7 : s.gpr .s7 = off N 0) (h8 : s.gpr .s8 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hN : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) (hsep : ∀ i < k, ∀ x, ofs B x < Z → off N i ≠ x) :
    WP isa (loadArr j) s fun t =>
      (wordsVal t.mem B (slot w j) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) ∧
        word t.mem B (slot w j + 8 * w) = 0 ∧ Outside B (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .a7 = off B (slot w 0)) ∧ Keep loadRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZj := h.arr hj
  have hZ28 := h.hZ
  have hw2 := h.w2
  have hw48 := h.w48
  have alj : slot w j % 8 = 0 := slot_al w j
  unfold loadArr
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (adds_ok (i := 0) j h.a7 h.s5) fun s₁ ⟨⟨a7', m1⟩, k1⟩ => ?_
  rw [Nat.zero_add] at a7'
  have e16 : off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w j + 8 * w) := by
    rw [off_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith),
      show slot w j + 8 * (w + 2) - 16 = slot w j + 8 * w by omega_arith]
  refine WP.mono (WP.keep [.t3, .s0] (Q := fun t =>
    t.mem = s₁.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64)) ?_ (by rfl) (by rfl))
    fun s₂ ⟨m2, k2⟩ => ?_
  · brun [a7', (k1.gpr (r := .s5) (by decide)).trans h.s5, off_add, e16, exec_li_zero,
      (hs.congr k1.2.2).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k1.2.2).al8 (show slot w j + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
  have k12 := k1.trans k2
  have hz : word s₂.mem B (slot w j + 8 * w) = 0 := by rw [m2]; exact word_writeW_self _ _ _ _
  have out2 : Outside B (slot w j + 8 * w) 8 s.mem s₂.mem := by
    rw [m2, m1]; exact writeW_outside s.mem B (d := slot w j + 8 * w) 0 (by omega_arith)
  refine WP.seq (WP.mono (loadN_ok (dA := slot w j) (hs.congr k12.2.2) ((k2.gpr (by decide)).trans a7')
    ((k12.gpr (by decide)).trans h7) ((k12.gpr (by decide)).trans h8) ((k12.gpr (by decide)).trans h.t0) hk hkw
    (by omega_arith) (by simp only [Lay.slot_eq]; omega) alj (by omega_arith) (by rw [k12.2.1, k12.2.2]; exact hN)
    hsep) fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  have k123 := k12.trans k3
  have hb : B.toNat + slot w (0 + 28) ≤ 2 ^ 64 := by rw [Nat.zero_add]; omega_arith
  have a73 : s₃.gpr .a7 = off B (slot w (0 + j)) := by
    rw [Nat.zero_add, k3.gpr (by decide), k2.gpr (by decide)]; exact a7'
  refine WP.mono (subs_ok hb j (by omega) a73 ((k123.gpr (by decide)).trans h.s5))
    fun t ⟨⟨t7, mt⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t7⟩, (k123.trans k4).mono (by decide)⟩
  · rw [mt, hv, bytesAt_out out2 (by omega_arith) hsep]
  · rw [mt, out₃.word (Or.inr (by omega)) (by omega_arith)]; exact hz
  · rw [mt]
    exact (out2.mono (by omega) (by omega)).trans (out₃.mono (Nat.le_refl _) (by omega))

/-! ## Zero, comparison and copies -/

/-- `base rd j` in a working space. -/
theorem Env.base {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {rd : Reg} (hrd5 : rd ≠ .s5) (j : Nat) :
    WP isa (.block (PublicChecked.base rd j)) s fun t =>
      (t.gpr rd = off B (slot w j) ∧ t.mem = s.mem) ∧ Keep [rd] s t :=
  Pub.base_ok hrd5 h.a7 h.s5 j

/-- `zeroArr j`: array `j`'s `w` words := 0. -/
theorem zeroArr_ok {s : State} {B : Addr} {Z w j : Nat} (h : Env s B Z w) (hj : j < 28) :
    WP isa (zeroArr j) s fun t =>
      (wordsVal t.mem B (slot w j) w = 0 ∧ Outside B (slot w j) (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t5] s t := by
  have hZj := h.arr hj
  have hw2 := h.w2
  have hw48 := h.w48
  unfold zeroArr
  refine WP.seq (WP.mono (h.base (rd := .t3) (by decide) j) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.mono (zeroWords_ok (h.hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h.t0) (by omega) (by omega)
    (slot_al w j) (by omega)) fun t ⟨⟨_, hz, out⟩, k⟩ => ⟨⟨?_, by rw [← m1]; exact out⟩, (k1.trans k).mono (by decide)⟩
  exact ModArith.ma_wordsVal_zero hz

/-- The registers `below` writes. -/
def belowRegs : List Reg := [.a0, .a1, .a5, .a6, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `below a`: `a1 :=` the mask of array `a` (its word `w` zero) being
below the modulus in array 0; array 3 is the temporary. -/
theorem below_ok {s : State} {B : Addr} {Z w a : Nat} (h : Env s B Z w) (ha : a < 28)
    (ha3 : a ≠ 3) (htop : word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (below a) s fun t =>
      (t.gpr .a1 = mask (decide (wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w)) ∧
        Outside B (slot w 3) (8 * w) s.mem t.mem) ∧ Keep belowRegs s t := by
  have hs := h.hs
  have hZa := h.arr ha
  have hZ3 := h.arr (show 3 < 28 by decide)
  have hw2 := h.w2
  have hw48 := h.w48
  have s3a := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ a by omega)
  have s30 := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ 0 by decide)
  unfold below
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .a5) (by decide) a) fun s₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .a6) (by decide) 3) fun s₂ ⟨⟨a6, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (subMod64_ok (dA := slot w a) (dT := slot w 3) (dM := slot w 0) (h.hs.congr k12.2.2)
    ((k2.gpr (by decide)).trans a5) a6 ((k12.gpr (by decide)).trans h.a7) ((k12.gpr (by decide)).trans h.t0)
    (by omega) (by omega) (slot_al w a) (slot_al w 3) (slot_al w 0) (by omega) (by omega)
    (by have := h.arr (show 0 < 28 by decide); omega) (by omega) (by omega))
    fun s₃ ⟨⟨c, hc, he, h4⟩, out, k3⟩ => ?_)
  rw [m2, m1] at he out
  rw [m2, m1, htop] at h4
  have hlt := wordsVal_lt s₃.mem B (slot w 3) w
  refine WP.keep [.a1] (Q := fun t => (t.gpr .a1 = mask (decide (wordsVal s.mem B (slot w a) w <
    wordsVal s.mem B (slot w 0) w)) ∧ Outside B (slot w 3) (8 * w) s.mem t.mem)) ?_ (by rfl) (by rfl)
    |>.mono fun t ⟨q, k4⟩ => ⟨q, ((k12.trans k3).trans k4).mono (by decide)⟩
  brun [h4]
  refine ⟨?_, out⟩
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases hc' with rfl | rfl
  · have : ¬ wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w := by omega
    simp [this, mask]
  · have : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w := by omega
    simp [this, mask]

/-- The registers `copy` writes. -/
def copyRegs : List Reg := [.s0, .t3, .t4, .t5]

/-- `copy o a`: array `o`'s `w + 2` words := array `a`'s. -/
theorem copy_ok {s : State} {B : Addr} {Z w o a : Nat} (h : Env s B Z w) (ho : o < 28) (ha : a < 28)
    (hoa : o ≠ a) :
    WP isa (copy o a) s fun t =>
      ((∀ i < w + 2, word t.mem B (slot w o + 8 * i) = word s.mem B (slot w a + 8 * i)) ∧
        Outside B (slot w o) (8 * (w + 2)) s.mem t.mem) ∧ Keep copyRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZo := h.arr ho
  have hZa := h.arr ha
  have hw2 := h.w2
  have hw48 := h.w48
  have soa := VG.Proof.Bignum.slot_sep (w := w) hoa
  have alo := slot_al w o
  have ala := slot_al w a
  unfold copy
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) o) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .t4) (by decide) a) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.t5] (Q := fun s₃ => s₃.gpr .t5 = BitVec.ofNat 64 (w + 2) ∧ s₃.mem = s₂.mem)
    (by brun [(k12.gpr (r := .t0) (by decide)).trans h.t0]
        rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]) (by rfl) (by rfl))
    fun s₃ ⟨⟨b5, m3⟩, k3⟩ => ?_
  have k123 := k12.trans k3
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w o + 8 * i) ∧ t.gpr .t4 = off B (slot w a + 8 * i) ∧
      Outside B (slot w o) (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (slot w o + 8 * k) = word s.mem B (slot w a + 8 * k)) ∧ Keep copyRegs s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w + 2) (by omega_arith)
    (by omega) Inv (fun i hi t ⟨j3, j4, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k3.gpr (by decide), k2.gpr (by decide), a3]; rfl, by rw [k3.gpr (by decide), a4]; rfl,
      by rw [m3, m2, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega), k123.mono (by decide)⟩ b5)
    fun t ⟨_, _, tout, tc, tk⟩ => ⟨⟨tc, tout⟩, tk⟩
  have hsa : word t.mem B (slot w a + 8 * i) = word s.mem B (slot w a + 8 * i) :=
    jout.word (by omega) (by omega_arith)
  have hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
      .addi .t5 .t5 (-1)]) t fun t' => t' = (((({ t.write .s0 (word t.mem B (slot w a + 8 * i)) with
        mem := t.mem.writeW (off B (slot w o + 8 * i)) (word t.mem B (slot w a + 8 * i)) } : State).write
        .t3 (off B (slot w o + 8 * i + 8))).write .t4 (off B (slot w a + 8 * i + 8))).write .t5
          (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [j3, j4, BitVec.add_zero, (hs.congr jk.2.2).ld (show slot w a + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show slot w a + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      (hs.congr jk.2.2).st (show slot w o + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show slot w o + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := slot w o + 8 * i) (word t.mem B (slot w a + 8 * i)) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show slot w o + 8 * i + 8 = slot w o + 8 * (i + 1) by omega],
    by gsimp; rw [show slot w a + 8 * i + 8 = slot w a + 8 * (i + 1) by omega], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsa]
  · exact Keep.trans' jk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-- Arrays of `w` words with the same words have the same value. -/
theorem wordsVal_congr {m m' : Mem} {B : Addr} {d d' : Nat} : ∀ {w : Nat},
    (∀ i < w, word m' B (d' + 8 * i) = word m B (d + 8 * i)) → wordsVal m' B d' w = wordsVal m B d w
  | 0, _ => rfl
  | w + 1, h => by
    simp only [wordsVal]
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, wordsVal_congr (d := d + 8) (d' := d' + 8) fun i hi => by
      rw [show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega, show d + 8 + 8 * i = d + 8 * (i + 1) by omega]
      exact h (i + 1) (by omega)]

/-- Two arrays of `w` words are equal exactly when their words are. -/
theorem wordsVal_eq_iff {m : Mem} {B : Addr} {d d' : Nat} : ∀ {w : Nat},
    wordsVal m B d w = wordsVal m B d' w ↔ ∀ i < w, word m B (d + 8 * i) = word m B (d' + 8 * i)
  | 0 => by simp [wordsVal]
  | w + 1 => by
    simp only [wordsVal]
    have h1 := (word m B d).isLt
    have h2 := (word m B d').isLt
    constructor
    · intro e
      have e0 : (word m B d).toNat = (word m B d').toNat := by omega
      have e1 : wordsVal m B (d + 8) w = wordsVal m B (d' + 8) w := by omega
      intro i hi
      rcases i with _ | i
      · simpa using BitVec.eq_of_toNat_eq e0
      · have := ((wordsVal_eq_iff (d := d + 8) (d' := d' + 8)).mp e1) i (by omega)
        rwa [show d + 8 + 8 * i = d + 8 * (i + 1) by omega, show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega] at this
    · intro hw
      have e0 := hw 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at e0
      rw [e0, (wordsVal_eq_iff (d := d + 8) (d' := d' + 8)).mpr fun i hi => by
        rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega, show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega]
        exact hw (i + 1) (by omega)]

/-- The registers `eqMask` writes. -/
def eqRegs (rd : Reg) : List Reg := [.s0, .s1, .t2, .t3, .t4, .t5, rd]

theorem or_xor_zero (x a b : BitVec 64) : (x ||| a ^^^ b) = 0 ↔ x = 0 ∧ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

/-- `eqMask rd j k`: `rd :=` the mask of arrays `j` and `k` being equal in
their `w` words. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w j k : Nat} (h : Env s B Z w) (hj : j < 28) (hk : k < 28)
    {rd : Reg} (hrd : rd ∉ ([.s0, .s1, .t2, .t3, .t4, .t5, .s5, .a7, .t0] : List Reg)) :
    WP isa (eqMask rd j k) s fun t =>
      (t.gpr rd = mask (decide (wordsVal s.mem B (slot w j) w = wordsVal s.mem B (slot w k) w)) ∧
        t.mem = s.mem) ∧ Keep (eqRegs rd) s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZj := h.arr hj
  have hZk := h.arr hk
  have hw2 := h.w2
  have hw48 := h.w48
  have alj := slot_al w j
  have alk := slot_al w k
  unfold eqMask
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) j) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .t4) (by decide) k) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.t5, .t2] (Q := fun s₃ => s₃.gpr .t5 = BitVec.ofNat 64 w ∧ s₃.gpr .t2 = 0 ∧
    s₃.mem = s₂.mem) (by brun [(k12.gpr (r := .t0) (by decide)).trans h.t0, exec_li_zero, BitVec.add_zero]) (by rfl) (by rfl))
    fun s₃ ⟨⟨b5, b2, m3⟩, k3⟩ => ?_
  have k123 := k12.trans k3
  have ms : s₃.mem = s.mem := by rw [m3, m2, m1]
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w j + 8 * i) ∧ t.gpr .t4 = off B (slot w k + 8 * i) ∧ t.mem = s.mem ∧
      (t.gpr .t2 = 0 ↔ ∀ q < i, word s.mem B (slot w j + 8 * q) = word s.mem B (slot w k + 8 * q)) ∧
      Keep (eqRegs rd) s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .s0 .t3 0, .load .d .s1 .t4 0,
      .logic .xor .s0 .s0 .s1, .logic .or .t2 .t2 .s0, .addi .t3 .t3 8, .addi .t4 .t4 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith) (by omega) Inv
    (fun i hi t ⟨j3, j4, jm, jc, jk⟩ hc => ?_)
    ⟨by rw [k3.gpr (by decide), k2.gpr (by decide), a3]; rfl, by rw [k3.gpr (by decide), a4]; rfl, ms,
      by rw [b2]; simp, k123.mono (by simp [eqRegs])⟩ b5) fun t ⟨_, _, tm, tc, tk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .s0 .t3 0, .load .d .s1 .t4 0, .logic .xor .s0 .s0 .s1,
        .logic .or .t2 .t2 .s0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .t5 .t5 (-1)]) t fun t' =>
        t' = ((((((t.write .s0 (word s.mem B (slot w j + 8 * i))).write .s1 (word s.mem B (slot w k + 8 * i))).write
          .s0 (word s.mem B (slot w j + 8 * i) ^^^ word s.mem B (slot w k + 8 * i))).write .t2
          (t.gpr .t2 ||| (word s.mem B (slot w j + 8 * i) ^^^ word s.mem B (slot w k + 8 * i)))).write .t3
          (off B (slot w j + 8 * i + 8))).write .t4 (off B (slot w k + 8 * i + 8))).write .t5
            (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [j3, j4, jm, BitVec.add_zero, (hs.congr jk.2.2).ld (show slot w j + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.2.2).al8 (show slot w j + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
        (hs.congr jk.2.2).ld (show slot w k + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.2.2).al8 (show slot w k + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    refine ⟨⟨by gsimp; rw [show slot w j + 8 * i + 8 = slot w j + 8 * (i + 1) by omega],
      by gsimp; rw [show slot w k + 8 * i + 8 = slot w k + 8 * (i + 1) by omega], by gsimp; exact jm, ?_, ?_⟩,
      by gsimp⟩
    · gsimp
      rw [or_xor_zero, jc]
      constructor
      · rintro ⟨hq, he⟩ q hq'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
        · exact hq q hq'
        · exact he
      · intro hq
        exact ⟨fun q hq' => hq q (by omega), hq i (by omega)⟩
    · refine Keep.trans' jk ((((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono
        (by simp [eqRegs]))
  · refine WP.keep [.s0, .s1, rd] (Q := fun u => u.gpr rd = mask (decide (wordsVal s.mem B (slot w j) w =
      wordsVal s.mem B (slot w k) w)) ∧ u.mem = t.mem) ?_ (by cases rd <;> simp_all <;> decide) (by rfl)
      |>.mono fun u ⟨⟨q, mu⟩, ku⟩ => ⟨⟨q, by rw [mu, tm]⟩, (tk.trans ku).mono (by simp [eqRegs])⟩
    have hrs0 : rd ≠ .s0 := fun e => hrd (by simp [e])
    have hrs1 : rd ≠ .s1 := fun e => hrd (by simp [e])
    brun [exec_li_zero, hrs0.symm, hrs1.symm, gpr_write_self, gpr_write_of_ne _ _ hrs0, gpr_write_of_ne _ _ hrs1]
    have hiff : (wordsVal s.mem B (slot w j) w = wordsVal s.mem B (slot w k) w) ↔ t.gpr .t2 = 0 := by
      rw [tc, wordsVal_eq_iff]
    by_cases h0 : t.gpr .t2 = 0
    · simp [h0, hiff.mpr h0, mask]
    · have : (0 : BitVec 64) < t.gpr .t2 := by
        rw [BitVec.lt_def]
        exact Nat.pos_of_ne_zero fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e))
      have hn : ¬ wordsVal s.mem B (slot w j) w = wordsVal s.mem B (slot w k) w := fun e => h0 (hiff.mp e)
      simp only [hn, decide_false, mask]
      simp only [this, ite_true]; rfl

end VG.Proof.Dsa.RISCV64
