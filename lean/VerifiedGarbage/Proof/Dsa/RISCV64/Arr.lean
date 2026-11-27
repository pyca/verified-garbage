module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2Words
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2Lazy
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: the arrays

In a working space (`Env`): `a7` moved to array `j` and back (`adds_ok`,
`subs_ok`); `loadArr_ok`, a number's octets into array `j`, its word `w`
zeroed first; `zeroArr_ok`; `below_ok`, the mask of an array being below the
modulus in array 0 (`subMod64`'s borrow); `copy_ok`, an array's `w + 2`
words into another; `rr_ok` and `rrAny_ok`, `R² mod m`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

theorem slot_succ (w j : Nat) : slot w (j + 1) = slot w j + 8 * (w + 2) := by
  unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega_using []

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
    obtain e : off B (slot w (i + (j + 1))) - BitVec.ofNat 64 (8 * (w + 2)) = off B (slot w (i + j)) := by
      rw [off_sub B (by rw [← Nat.add_assoc, slot_succ]; omega_using []), ← Nat.add_assoc, slot_succ, Nat.add_sub_cancel]
    refine Steps.WP.cons exec_sub ?_
    refine WP.mono (subs_ok hB j (t := t.write .a7 (t.gpr .a7 - t.gpr .s5)) (by omega_using [hj])
      (by rw [gpr_write_self, h7, h5, e]) (by rw [gpr_write_of_ne _ _ (by decide)]; exact h5))
      fun t' ⟨⟨h1, m1⟩, k1⟩ => ⟨⟨h1, by rw [m1]; rfl⟩, ((Keep.write _ _ _).trans k1).mono (by simp)⟩

/-- A buffer's bytes are those of a memory that changed only in the working
space. -/
theorem bytesAt_out {B I : Addr} {Z o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off I i ≠ x) :
    Spec.Rsa.bytesAt m' I k = Spec.Rsa.bytesAt m I k := by
  rw [VG.Proof.Bignum.bytesAt_eq, VG.Proof.Bignum.bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ ?_
  obtain hi := List.mem_range.mp hi
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
  obtain hZj := h.arr hj
  have hZ28 := h.hZ
  have hw2 := h.w2
  have hw48 := h.w48
  obtain alj : slot w j % 8 = 0 := slot_al w j
  unfold loadArr
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (adds_ok (i := 0) j h.a7 h.s5) fun s₁ ⟨⟨a7', m1⟩, k1⟩ => ?_
  rw [Nat.zero_add] at a7'
  obtain e16 : off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w j + 8 * w) := by
    rw [off_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith),
      show slot w j + 8 * (w + 2) - 16 = slot w j + 8 * w by omega_arith]
  refine WP.mono (WP.keep [.t3, .s0] (Q := fun t =>
    t.mem = s₁.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64)) ?_ (by rfl) (by rfl))
    fun s₂ ⟨m2, k2⟩ => ?_
  · brun [a7', (k1.gpr (r := .s5) (by decide)).trans h.s5, off_add, e16, exec_li_zero,
      (hs.congr k1.2.2).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k1.2.2).al8 (show slot w j + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
  obtain k12 := k1.trans k2
  obtain hz : word s₂.mem B (slot w j + 8 * w) = 0 := by rw [m2]; exact word_writeW_self _ _ _ _
  obtain out2 : Outside B (slot w j + 8 * w) 8 s.mem s₂.mem := by
    rw [m2, m1]; exact writeW_outside s.mem B (d := slot w j + 8 * w) 0 (by omega_arith)
  refine WP.seq (WP.mono (loadN_ok (dA := slot w j) (hs.congr k12.2.2) ((k2.gpr (by decide)).trans a7')
    ((k12.gpr (by decide)).trans h7) ((k12.gpr (by decide)).trans h8) ((k12.gpr (by decide)).trans h.t0) hk hkw
    (by omega_arith) (by simp only [Lay.slot_eq]; omega_using []) alj (by omega_arith) (by rw [k12.2.1, k12.2.2]; exact hN)
    hsep) fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  obtain k123 := k12.trans k3
  obtain hb : B.toNat + slot w (0 + 28) ≤ 2 ^ 64 := by rw [Nat.zero_add]; omega_arith
  obtain a73 : s₃.gpr .a7 = off B (slot w (0 + j)) := by
    rw [Nat.zero_add, k3.gpr (by decide), k2.gpr (by decide)]; exact a7'
  refine WP.mono (subs_ok hb j (by omega_using [hj]) a73 ((k123.gpr (by decide)).trans h.s5))
    fun t ⟨⟨t7, mt⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t7⟩, (k123.trans k4).mono (by decide)⟩
  · rw [mt, hv, bytesAt_out out2 (by omega_arith) hsep]
  · rw [mt, out₃.word (Or.inr (by omega_using [])) (by omega_arith)]; exact hz
  · rw [mt]
    exact (out2.mono (by omega_using []) (by omega_using [])).trans (out₃.mono (Nat.le_refl _) (by omega_using []))

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
  obtain hZj := h.arr hj
  have hw2 := h.w2
  have hw48 := h.w48
  unfold zeroArr
  refine WP.seq (WP.mono (h.base (rd := .t3) (by decide) j) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.mono (zeroWords_ok (h.hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h.t0) (by omega_using [hw2]) (by omega_using [hw48])
    (slot_al w j) (by omega_using [hZj])) fun t ⟨⟨_, hz, out⟩, k⟩ => ⟨⟨?_, by rw [← m1]; exact out⟩, (k1.trans k).mono (by decide)⟩
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
  obtain hZa := h.arr ha
  obtain hZ3 := h.arr (show 3 < 28 by decide)
  have hw2 := h.w2
  have hw48 := h.w48
  obtain s3a := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ a by omega_using [ha3])
  obtain s30 := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ 0 by decide)
  unfold below
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .a5) (by decide) a) fun s₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .a6) (by decide) 3) fun s₂ ⟨⟨a6, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.seq (WP.mono (subMod64_ok (dA := slot w a) (dT := slot w 3) (dM := slot w 0) (h.hs.congr k12.2.2)
    ((k2.gpr (by decide)).trans a5) a6 ((k12.gpr (by decide)).trans h.a7) ((k12.gpr (by decide)).trans h.t0)
    (by omega_using [hw2]) (by omega_using [hw48]) (slot_al w a) (slot_al w 3) (slot_al w 0) (by omega_using [hZa]) (by omega_using [hZ3])
    (by have := h.arr (show 0 < 28 by decide); omega_using [this]) (by omega_using [s3a]) (by omega_using [s30]))
    fun s₃ ⟨⟨c, hc, he, h4⟩, out, k3⟩ => ?_)
  rw [m2, m1] at he out
  rw [m2, m1, htop] at h4
  obtain hlt := wordsVal_lt s₃.mem B (slot w 3) w
  refine WP.keep [.a1] (Q := fun t => (t.gpr .a1 = mask (decide (wordsVal s.mem B (slot w a) w <
    wordsVal s.mem B (slot w 0) w)) ∧ Outside B (slot w 3) (8 * w) s.mem t.mem)) ?_ (by rfl) (by rfl)
    |>.mono fun t ⟨q, k4⟩ => ⟨q, ((k12.trans k3).trans k4).mono (by decide)⟩
  brun [h4]
  refine ⟨?_, out⟩
  obtain hc' : c = 0 ∨ c = 1 := by omega_using [hc]
  rcases hc' with rfl | rfl
  · have : ¬ wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w := by omega_using [he]
    simp [this, mask]
  · have : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w := by omega_using [hlt, he]
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
  obtain hZo := h.arr ho
  obtain hZa := h.arr ha
  have hw2 := h.w2
  have hw48 := h.w48
  obtain soa := VG.Proof.Bignum.slot_sep (w := w) hoa
  obtain alo := slot_al w o
  obtain ala := slot_al w a
  unfold copy
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) o) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .t4) (by decide) a) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (WP.keep [.t5] (Q := fun s₃ => s₃.gpr .t5 = BitVec.ofNat 64 (w + 2) ∧ s₃.mem = s₂.mem)
    (by brun [(k12.gpr (r := .t0) (by decide)).trans h.t0]
        rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]) (by rfl) (by rfl))
    fun s₃ ⟨⟨b5, m3⟩, k3⟩ => ?_
  obtain k123 := k12.trans k3
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w o + 8 * i) ∧ t.gpr .t4 = off B (slot w a + 8 * i) ∧
      Outside B (slot w o) (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (slot w o + 8 * k) = word s.mem B (slot w a + 8 * k)) ∧ Keep copyRegs s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w + 2) (by omega_arith)
    (by omega_using []) Inv (fun i hi t ⟨j3, j4, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k3.gpr (by decide), k2.gpr (by decide), a3]; rfl, by rw [k3.gpr (by decide), a4]; rfl,
      by rw [m3, m2, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), k123.mono (by decide)⟩ b5)
    fun t ⟨_, _, tout, tc, tk⟩ => ⟨⟨tc, tout⟩, tk⟩
  obtain hsa : word t.mem B (slot w a + 8 * i) = word s.mem B (slot w a + 8 * i) :=
    jout.word (by omega_using [soa, hi]) (by omega_arith)
  obtain hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
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
  obtain hw := writeW_outside t.mem B (d := slot w o + 8 * i) (word t.mem B (slot w a + 8 * i)) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show slot w o + 8 * i + 8 = slot w o + 8 * (i + 1) by omega_using []],
    by gsimp; rw [show slot w a + 8 * i + 8 = slot w a + 8 * (i + 1) by omega_using []], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans (hw.mono (by omega_using []) (by omega_using []))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_using [hk]) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsa]
  · exact Keep.trans' jk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-- Arrays of `w` words with the same words have the same value. -/
theorem wordsVal_congr {m m' : Mem} {B : Addr} {d d' : Nat} : ∀ {w : Nat},
    (∀ i < w, word m' B (d' + 8 * i) = word m B (d + 8 * i)) → wordsVal m' B d' w = wordsVal m B d w
  | 0, _ => rfl
  | w + 1, h => by
    simp only [wordsVal]
    obtain h0 := h 0 (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, wordsVal_congr (d := d + 8) (d' := d' + 8) fun i hi => by
      rw [show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega_using [], show d + 8 + 8 * i = d + 8 * (i + 1) by omega_using []]
      exact h (i + 1) (by omega_using [hi])]

/-- Two arrays of `w` words are equal exactly when their words are. -/
theorem wordsVal_eq_iff {m : Mem} {B : Addr} {d d' : Nat} : ∀ {w : Nat},
    wordsVal m B d w = wordsVal m B d' w ↔ ∀ i < w, word m B (d + 8 * i) = word m B (d' + 8 * i)
  | 0 => by simp [wordsVal]
  | w + 1 => by
    simp only [wordsVal]
    obtain h1 := (word m B d).isLt
    obtain h2 := (word m B d').isLt
    constructor
    · intro e
      obtain e0 : (word m B d).toNat = (word m B d').toNat := by omega_using [e]
      obtain e1 : wordsVal m B (d + 8) w = wordsVal m B (d' + 8) w := by omega_using [e]
      intro i hi
      rcases i with _ | i
      · simpa using BitVec.eq_of_toNat_eq e0
      · have := ((wordsVal_eq_iff (d := d + 8) (d' := d' + 8)).mp e1) i (by omega_using [hi])
        rwa [show d + 8 + 8 * i = d + 8 * (i + 1) by omega_using [], show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega_using []] at this
    · intro hw
      obtain e0 := hw 0 (by omega_using [])
      simp only [Nat.mul_zero, Nat.add_zero] at e0
      rw [e0, (wordsVal_eq_iff (d := d + 8) (d' := d' + 8)).mpr fun i hi => by
        rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega_using [], show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega_using []]
        exact hw (i + 1) (by omega_using [hi])]

/-- The registers `eqMask` writes. -/
def eqRegs (rd : Reg) : List Reg := [.s0, .s1, .t2, .t3, .t4, .t5, rd]

theorem or_xor_zero (x a b : BitVec 64) : (x ||| a ^^^ b) = 0 ↔ x = 0 ∧ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

/-- What `eqMask`'s last block writes, for any `rd`: the cases are split here, in no context. -/
private theorem eqMask_tail_writes (rd : Reg) :
    writesOnly [.s0, .s1, rd] (.block [.li .s0 0, .sltu .s1 .s0 .t2, .addi rd .s1 (-1)]) = true := by
  cases rd <;> decide

/-- `eqMask rd j k`: `rd :=` the mask of arrays `j` and `k` being equal in
their `w` words. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w j k : Nat} (h : Env s B Z w) (hj : j < 28) (hk : k < 28)
    {rd : Reg} (hrd : rd ∉ ([.s0, .s1, .t2, .t3, .t4, .t5, .s5, .a7, .t0] : List Reg)) :
    WP isa (eqMask rd j k) s fun t =>
      (t.gpr rd = mask (decide (wordsVal s.mem B (slot w j) w = wordsVal s.mem B (slot w k) w)) ∧
        t.mem = s.mem) ∧ Keep (eqRegs rd) s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  obtain hZj := h.arr hj
  obtain hZk := h.arr hk
  have hw2 := h.w2
  have hw48 := h.w48
  obtain alj := slot_al w j
  obtain alk := slot_al w k
  unfold eqMask
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) j) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .t4) (by decide) k) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (WP.keep [.t5, .t2] (Q := fun s₃ => s₃.gpr .t5 = BitVec.ofNat 64 w ∧ s₃.gpr .t2 = 0 ∧
    s₃.mem = s₂.mem) (by brun [(k12.gpr (r := .t0) (by decide)).trans h.t0, exec_li_zero, BitVec.add_zero]) (by rfl) (by rfl))
    fun s₃ ⟨⟨b5, b2, m3⟩, k3⟩ => ?_
  obtain k123 := k12.trans k3
  obtain ms : s₃.mem = s.mem := by rw [m3, m2, m1]
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w j + 8 * i) ∧ t.gpr .t4 = off B (slot w k + 8 * i) ∧ t.mem = s.mem ∧
      (t.gpr .t2 = 0 ↔ ∀ q < i, word s.mem B (slot w j + 8 * q) = word s.mem B (slot w k + 8 * q)) ∧
      Keep (eqRegs rd) s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .s0 .t3 0, .load .d .s1 .t4 0,
      .logic .xor .s0 .s0 .s1, .logic .or .t2 .t2 .s0, .addi .t3 .t3 8, .addi .t4 .t4 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith) (by omega_using [hw2]) Inv
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
    refine ⟨⟨by gsimp; rw [show slot w j + 8 * i + 8 = slot w j + 8 * (i + 1) by omega_using []],
      by gsimp; rw [show slot w k + 8 * i + 8 = slot w k + 8 * (i + 1) by omega_using []], by gsimp; exact jm, ?_, ?_⟩,
      by gsimp⟩
    · gsimp
      rw [or_xor_zero, jc]
      constructor
      · rintro ⟨hq, he⟩ q hq'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
        · exact hq q hq'
        · exact he
      · intro hq
        exact ⟨fun q hq' => hq q (by omega_using [hq']), hq i (by omega_using [])⟩
    · refine Keep.trans' jk ((((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono
        (by simp [eqRegs]))
  · refine WP.keep [.s0, .s1, rd] (Q := fun u => u.gpr rd = mask (decide (wordsVal s.mem B (slot w j) w =
      wordsVal s.mem B (slot w k) w)) ∧ u.mem = t.mem) ?_ (eqMask_tail_writes rd) (by rfl)
      |>.mono fun u ⟨⟨q, mu⟩, ku⟩ => ⟨⟨q, by rw [mu, tm]⟩, (tk.trans ku).mono (by simp [eqRegs])⟩
    -- `have`: the unused-variable linter does not see `hrd` referenced under `obtain`
    have hrs0 : rd ≠ .s0 := fun e => hrd (by simp [e])
    obtain hrs1 : rd ≠ .s1 := fun e => hrd (by simp [e])
    brun [exec_li_zero, hrs0.symm, hrs1.symm, gpr_write_self, gpr_write_of_ne _ _ hrs0, gpr_write_of_ne _ _ hrs1]
    obtain hiff : (wordsVal s.mem B (slot w j) w = wordsVal s.mem B (slot w k) w) ↔ t.gpr .t2 = 0 := by
      rw [tc, wordsVal_eq_iff]
    by_cases h0 : t.gpr .t2 = 0
    · simp [h0, hiff.mpr h0, mask]
    · have : (0 : BitVec 64) < t.gpr .t2 := by
        rw [BitVec.lt_def]
        exact Nat.pos_of_ne_zero fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e))
      obtain hn : ¬ wordsVal s.mem B (slot w j) w = wordsVal s.mem B (slot w k) w := fun e => h0 (hiff.mp e)
      simp only [hn, decide_false, mask]
      simp only [this, ite_true]; rfl

/-! ## `R² mod m` by doublings -/

/-- One word 1 and the others 0 are 1. -/
theorem wordsVal_one {m : Mem} {B : Addr} {d : Nat} {w : Nat} (hw : 1 ≤ w) (h0 : word m B d = 1)
    (hz : ∀ i < w - 1, word m B (d + 8 + 8 * i) = 0) : wordsVal m B d w = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_using [hw]⟩
  simp only [wordsVal, h0, ModArith.ma_wordsVal_zero (w := k) fun i hi => hz i (by omega_using [hi])]
  rfl

/-- The registers `rrDbl` writes. -/
def rrDblRegs : List Reg := [.a0, .a1, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- The bases of arrays 1–3 (`rrDbl` and `rrHi` work in them). -/
structure Bases (s : State) (B : Addr) (w : Nat) : Prop where
  a2 : s.gpr .a2 = off B (slot w 1)
  a5 : s.gpr .a5 = off B (slot w 2)
  a6 : s.gpr .a6 = off B (slot w 3)

theorem Bases.keep {s t : State} {B : Addr} {w : Nat} {rs : List Reg} (h : Bases s B w) (k : Keep rs s t)
    (hr : ∀ r ∈ [Reg.a2, .a5, .a6], r ∉ rs := by decide) : Bases t B w :=
  ⟨(k.gpr (hr _ (by decide))).trans h.a2, (k.gpr (hr _ (by decide))).trans h.a5,
    (k.gpr (hr _ (by decide))).trans h.a6⟩

/-- `rrDbl`: `R² mod m = 2^(128 w) mod m` into array 1, for `m ≥ 2` in array 0,
changing only arrays 1–3. -/
theorem rrDbl_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (hb : Bases s B w)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) :
    WP isa rrDbl s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep rrDblRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw2 := h.w2
  have hw48 := h.w48
  obtain e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e28 := e 28
  unfold rrDbl
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = off B (slot w 1) ∧ u.mem = s.mem)
    (by brun [hb.a2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₄ ⟨⟨a3, m14⟩, k14⟩ => ?_)
  obtain hE4 := h.keep k14 (by decide)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k14.2.2) a3 hE4.t0 (by omega_using [hw2]) (by omega_using [hw48]) (slot_al w 1)
    (by omega_using [hZ, e1, e28])) fun s₅ ⟨⟨_, hz, out5⟩, k5⟩ => ?_)
  rw [m14] at out5
  obtain k15 := k14.trans k5
  obtain hB5 := hb.keep k15 (by decide)
  obtain hE5 := h.keep k15 (by decide)
  refine WP.seq (WP.mono (WP.keep [.s0, .a1] (Q := fun u => u.mem = s₅.mem.writeW (off B (slot w 1)) (1 : BitVec 64) ∧
      u.gpr .a1 = BitVec.ofNat 64 (128 * w)) ?_ (by rfl) (by rfl)) fun s₆ ⟨⟨m6, a1⟩, k6⟩ => ?_)
  · have e7 : BitVec.ofNat 64 w <<< 7 = BitVec.ofNat 64 (128 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_arith
    brun [hB5.a2, hE5.t0, exec_li_lit (show 1 < 2048 by decide), BitVec.add_zero, e7,
      (hs.congr k15.2.2).st (show slot w 1 + 8 ≤ Z by omega_using [hZ, e1, e28]),
      (hs.congr k15.2.2).al8 (show slot w 1 + 8 ≤ Z by omega_using [hZ, e1, e28]) (slot_al w 1), exec_shift_d (show 7 < 64 by decide)]
    rfl
  obtain k16 := k15.trans k6
  obtain hE6 := h.keep k16 (by decide)
  obtain hB6 := hb.keep k16 (by decide)
  obtain hw6 := writeW_outside s₅.mem B (d := slot w 1) (1 : BitVec 64) (by omega_arith)
  obtain n6 : wordsVal s₆.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w := by
    rw [m6, hw6.wordsVal (by omega_using [e0, e1]) (by omega_arith), out5.wordsVal (by omega_using [e0, e1]) (by omega_arith)]
  obtain x6 : wordsVal s₆.mem B (slot w 1) w = 2 ^ 0 % wordsVal s.mem B (slot w 0) w := by
    rw [Nat.pow_zero, Nat.mod_eq_of_lt (by omega_using [hN])]
    refine wordsVal_one (by omega_using [hw2]) (by rw [m6]; exact word_writeW_self _ _ _ _) fun i hi => ?_
    rw [m6, hw6.word (by omega_using []) (by omega_arith)]
    have := hz (i + 1) (by omega_using [hi])
    rwa [show slot w 1 + 8 * (i + 1) = slot w 1 + 8 + 8 * i by omega_using []] at this
  refine WP.mono (r2Dbl_ok (a := 0) (M := 128 * w) (hs.congr k16.2.2) hB6.a5 hB6.a6 hE6.a7 hB6.a2 hE6.t0
    (by omega_using [hw2]) (by omega_using [hw48]) (by omega_using [hZ, e4, e28]) n6 (by omega_using [hN]) x6 a1 (by omega_using [hw2])
    (by omega_arith)) fun s₇ ⟨x7, out7, k7⟩ => ⟨⟨?_, ?_⟩, (k16.trans k7).mono (by decide)⟩
  · rw [x7, Nat.zero_add]
  · have o6 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₆.mem := by
      rw [m6]; exact (out5.mono (by omega_using []) (by omega_using [])).trans (hw6.mono (by omega_using []) (by omega_using []))
    exact o6.trans out7

/-- Array 1's `w + 2` words copied into array 24, after changes to arrays 1–3. -/
theorem rrCopy_ok {s₀ s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w)
    (out : Outside B (slot w 1) (24 * (w + 2)) s₀.mem s.mem) :
    WP isa (copy 24 1) s fun t =>
      (wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w ∧
        wordsVal t.mem B (slot w 24) w = wordsVal s.mem B (slot w 1) w ∧
        Outside B (slot w 1) (24 * (8 * (w + 2))) s₀.mem t.mem) ∧ Keep copyRegs s t := by
  have hnw := h.hs.nowrap
  have hZ := h.hZ
  have hw48 := h.w48
  obtain e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain e1 := e 1; have e24 := e 24; have e28 := e 28
  refine WP.mono (copy_ok h (o := 24) (a := 1) (by decide) (by decide) (by decide))
    fun t ⟨⟨hc, out8⟩, k8⟩ => ⟨⟨?_, ?_, ?_⟩, k8⟩
  · exact out8.wordsVal (by omega_using [e1, e24]) (by omega_arith)
  · exact wordsVal_congr fun i hi => hc i (by omega_using [hi])
  · exact (out.mono (by omega_using []) (by omega_using [])).trans (out8.mono (by omega_using [e1, e24]) (by omega_using [e1, e24]))

/-- The registers `rrAny` writes. -/
def rrAnyRegs : List Reg := [.a0, .a1, .a2, .a5, .a6, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `rrAny`: `R² mod m = 2^(128 w) mod m` into arrays 1 and 24, for `m ≥ 2` in
array 0, changing only arrays 1–24. -/
theorem rrAny_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) :
    WP isa rrAny s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w 24) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (8 * (w + 2))) s.mem t.mem) ∧ Keep rrAnyRegs s t := by
  unfold rrAny
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .a2) (by decide) 1) fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .a5) (by decide) 2) fun s₂ ⟨⟨a5, m2⟩, k2⟩ => ?_
  refine WP.mono ((h.keep (k1.trans k2)).base (rd := .a6) (by decide) 3) fun s₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  obtain k13 := (k1.trans k2).trans k3
  obtain m13 : s₃.mem = s.mem := by rw [m3, m2, m1]
  refine WP.seq (WP.mono (rrDbl_ok (h.keep k13) ⟨by rw [k3.gpr (by decide), k2.gpr (by decide)]; exact a2,
    by rw [k3.gpr (by decide)]; exact a5, a6⟩ (by rw [m13]; exact hN)) fun s₄ ⟨⟨x4, o4⟩, k4⟩ => ?_)
  rw [m13] at x4 o4
  obtain k14 := k13.trans k4
  exact WP.mono (rrCopy_ok (h.keep k14) o4) fun t ⟨⟨c1, c24, o⟩, k⟩ =>
    ⟨⟨by rw [c1, x4], by rw [c24, x4], o⟩, (k14.trans k).mono (by decide)⟩

/-! ## `R² mod m`, for a top word that is not zero -/

/-- An odd modulus whose top word is not zero is above `2^(64 (w - 1))`. -/
theorem top_lt {m : Mem} {B : Addr} {w : Nat} (hw : 2 ≤ w) (hodd : wordsVal m B (slot w 0) w % 2 = 1)
    (ht : (word m B (slot w 0 + 8 * (w - 1))).toNat ≠ 0) : 2 ^ (64 * (w - 1)) < wordsVal m B (slot w 0) w := by
  obtain e := wordsVal_top m B (slot w 0) (w := w) (by omega_using [hw])
  obtain h1 : 2 ^ (64 * (w - 1)) * 1 ≤ 2 ^ (64 * (w - 1)) * (word m B (slot w 0 + 8 * (w - 1))).toNat :=
    Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero ht)
  obtain h2 : 2 ^ (64 * (w - 1)) % 2 = 0 := by
    rw [show 64 * (w - 1) = 64 * (w - 1) - 1 + 1 by omega_using [hw], Nat.pow_succ]; omega_using []
  omega_using [e, h1, h2, hodd]

/-- The registers `rrSqr` writes. -/
def rrSqrRegs : List Reg := [.a0, .a1, .a3, .a4, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s7]

/-- `rrSqr`: `R² mod m` into array 1, for an odd `m` above `2^(64 (w - 1))` in
array 0 and `-m⁻¹ mod 2⁶⁴` in `t1`, changing only arrays 1–3. -/
theorem rrSqr_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (hb : Bases s B w)
    (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) (hN : 2 ^ (64 * (w - 1)) < wordsVal s.mem B (slot w 0) w)
    (hinv : ((word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0) :
    WP isa rrSqr s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep rrSqrRegs s t := by
  have hw2 := h.w2
  have hw48 := h.w48
  have hZ := h.hZ
  have hnw := h.hs.nowrap
  obtain e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8; have e28 := e 28
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hodd hN ⊢
  unfold rrSqr
  refine WP.seq (WP.mono (r2HiDbl_ok (N := N) h.hs hb.a5 hb.a6 h.a7 hb.a2 h.t0 hw2 (by omega_using [hw48])
    (by omega_using [hZ, e4, e28]) hNd hN) fun s₁ ⟨x1, o1, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = BitVec.ofNat 64 6 ∧ u.mem = s₁.mem)
    (by brun [exec_li_lit (show 6 < 2048 by decide)]) (by rfl) (by rfl)) fun s₂ ⟨⟨a7, m2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  rw [← m2] at x1 o1
  obtain hw0 : word s₂.mem B (slot w 0) = word s.mem B (slot w 0) := Outside.word o1 (by omega_using [e0, e1]) (by omega_using [hZ, hnw, e0, e28])
  obtain n2 : wordsVal s₂.mem B (slot w 0) w = N := by rw [Outside.wordsVal o1 (by omega_using [e0, e1]) (by omega_using [hZ, hnw, e0, e28]), hNd]
  let Inv : Nat → State → Prop := fun j t =>
    SqI t B Z w N (w * 2 ^ j) t ∧ Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep rrSqrRegs s t
  obtain I0 : Inv 0 s₂ := by
    obtain E := h.keep k12 (by decide)
    obtain hB := hb.keep k12 (by decide)
    refine ⟨⟨E.hs, hB.a2, hB.a5, hB.a6, E.a7, E.t0, by rw [hw0, k12.gpr (by decide)]; exact hinv, n2, ?_, ?_,
      Outside.refl _ _ _ _, Keep.refl _ _⟩, o1, k12.mono (by decide)⟩
    · rw [x1]; exact Nat.mod_lt _ (by omega_using [hN])
    · rw [x1, Nat.mod_mod, Nat.pow_zero, Nat.mul_one, Nat.pow_add]
  refine WP.mono (wp_countdown (cnt := .s7) (N := 6) (by decide) (by decide) Inv (fun j _ t ⟨I, to, tk⟩ _ => ?_)
    I0 a7) fun t ⟨I, to, tk⟩ => ⟨⟨?_, to⟩, tk⟩
  · refine WP.seq (WP.mono (sqI_step hw2 (by omega_using [hw48]) (by omega_using [hZ, e8, e28]) hodd I) fun u I' => ?_)
    refine WP.mono (dec_ok u .s7) fun u' e' => ?_
    subst e'
    refine ⟨⟨⟨I'.scr.congr rfl, by gsimp; exact I'.a2, by gsimp; exact I'.a5, by gsimp; exact I'.a6, by gsimp; exact I'.a7,
      by gsimp; exact I'.t0, by gsimp; exact I'.inv, by gsimp; exact I'.n, by gsimp; exact I'.lt, ?_,
      Outside.refl _ _ _ _, Keep.refl _ _⟩, to.trans (by gsimp; exact I'.out),
      Keep.trans' tk ((I'.keep.trans (Keep.write _ _ _)).mono (by decide))⟩, ?_⟩
    · gsimp
      rw [I'.x, show 2 * (w * 2 ^ j) = w * 2 ^ (j + 1) by rw [Nat.pow_succ]; grind]
    · gsimp; rw [I'.keep.gpr (by decide)]
  · rw [← Nat.mod_eq_of_lt I.lt, I.x, ← Nat.pow_add]
    congr 2; omega_using []

/-- The registers `rrHi` writes. -/
def rrHiRegs : List Reg := rrSqrRegs

theorem ltu_four {w : Nat} (hw : w ≤ 48) : decide (BitVec.ofNat 64 w < BitVec.ofNat 64 4) = decide (w < 4) := by
  rw [decide_eq_decide, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega_using [hw])]

/-- `rrHi`: `R² mod m` into array 1, for an odd `m` above `2^(64 (w - 1))` in
array 0 and `-m⁻¹ mod 2⁶⁴` in `t1`, changing only arrays 1–3. -/
theorem rrHi_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (hb : Bases s B w)
    (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) (hN : 2 ^ (64 * (w - 1)) < wordsVal s.mem B (slot w 0) w)
    (hinv : ((word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0) :
    WP isa rrHi s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep rrHiRegs s t := by
  have hw2 := h.w2
  have hw48 := h.w48
  have hZ := h.hZ
  obtain e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e4 := e 4; have e28 := e 28
  unfold rrHi
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 4 ∧ u.mem = s.mem)
    (by brun [exec_li_lit (show 4 < 2048 by decide)]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  obtain E := h.keep k1
  obtain hB := hb.keep k1
  rw [← m1] at hodd hN ⊢
  refine WP.ite (decide (w < 4)) (by show some (decide (s₁.gpr .t0 < s₁.gpr .t3)) = _; rw [E.t0, a3, ltu_four hw48]) (fun _ => ?_) (fun hc => ?_)
  · refine WP.mono (rrSqr_ok E hB hodd hN (by rw [m1, k1.gpr (by decide)]; exact hinv)) fun t ⟨q, k⟩ =>
      ⟨q, (k1.trans k).mono (by decide)⟩
  · obtain hw4 : 4 ≤ w := by have := of_decide_eq_false hc; omega_using [this]
    obtain hT := topW_pos (m := s₁.mem) (B := B) (w := w) (by omega_using [hw2]) (Nat.le_of_lt hN)
    refine WP.seq (WP.mono (lz_ok E.hs E.a7 E.t0 (by omega_using [hw2]) (slot_al w 0) (by omega_using [hZ, e0, e28]) hT)
      fun s₂ ⟨⟨a1, _, _, m2⟩, k2⟩ => ?_)
    obtain E2 := E.keep k2
    obtain hB2 := hB.keep k2
    rw [← m2] at hodd hN a1 ⊢
    exact WP.mono (r2Words_ok E2.hs hB2.a2 hB2.a6 E2.a7 E2.t0 a1 hw4 (by omega_using [hw48])
      (by omega_using [hZ, e4, e28]) (Nat.le_of_lt hN) hodd) fun t ⟨q, k⟩ =>
        ⟨q, ((k1.trans k2).trans k).mono (by decide)⟩

/-! ## `rr` -/

/-- `rr` up to its branch: the arrays' bases, and the modulus's top word in `s0`. -/
theorem rrTop_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ t, Env t B Z w → Bases t B w → t.gpr .s0 = word s.mem B (slot w 0 + 8 * (w - 1)) → t.mem = s.mem →
      Keep [.a2, .a5, .a6, .t3, .s0] s t → WP isa c t Q) :
    WP isa (.seq (.block (PublicChecked.base .a2 1)) (.seq (.block (PublicChecked.base .a5 2))
      (.seq (.block (PublicChecked.base .a6 3)) (.seq (.block rrTop) c)))) s Q := by
  have hw2 := h.w2
  have hw48 := h.w48
  have hZ := h.hZ
  have hnw := h.hs.nowrap
  obtain e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e28 := e 28
  refine WP.seq (WP.mono (h.base (rd := .a2) (by decide) 1) fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono ((h.keep k1).base (rd := .a5) (by decide) 2) fun s₂ ⟨⟨a5, m2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono ((h.keep (k1.trans k2)).base (rd := .a6) (by decide) 3) fun s₃ ⟨⟨a6, m3⟩, k3⟩ => ?_)
  obtain k13 := (k1.trans k2).trans k3
  obtain m13 : s₃.mem = s.mem := by rw [m3, m2, m1]
  obtain E := h.keep k13
  obtain ea := ea_top B (d := slot w 0) (w := w) (c := 8) (by omega_using [hw2]) (by omega_using [hZ, hnw, e0, e28, hw2])
  refine WP.seq (WP.mono (WP.keep [.t3, .s0] (Q := fun u => u.gpr .s0 = word s.mem B (slot w 0 + 8 * (w - 1)) ∧ u.mem = s₃.mem)
    ?_ (by rfl) (by rfl)) fun s₄ ⟨⟨a0, m4⟩, k4⟩ => ?_)
  · rw [show slot w 0 + 8 * w - 8 = slot w 0 + 8 * (w - 1) by omega_using [hw2]] at ea
    brun [rrTop, E.t0, E.a7, ea, BitVec.add_zero, exec_shift_d (show 3 < 64 by decide),
      E.hs.ld (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_using [hw2, hZ, e0, e28]),
      E.hs.al8 (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_using [hw2, hZ, e0, e28])
        (by have := slot_al w 0; omega_using [this])]
    rw [m13]
  · obtain k14 := k13.trans k4
    exact hc s₄ (h.keep k14) ⟨by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide)]; exact a2,
      by rw [k4.gpr (by decide), k3.gpr (by decide)]; exact a5, by rw [k4.gpr (by decide)]; exact a6⟩ a0
      (m4.trans m13) (k14.mono (by decide))

/-- `rr`'s branch: `R² mod m` into array 1, for an odd `m ≥ 2` in array 0,
`-m⁻¹ mod 2⁶⁴` in `t1` and the top word in `s0`, changing only arrays 1–3. -/
theorem rrIte_ok {s₁ : State} {B : Addr} {Z w : Nat} (E : Env s₁ B Z w) (hB : Bases s₁ B w)
    (hN : 2 ≤ wordsVal s₁.mem B (slot w 0) w) (hodd : wordsVal s₁.mem B (slot w 0) w % 2 = 1)
    (hinv : ((word s₁.mem B (slot w 0)).toNat * (s₁.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (a0 : s₁.gpr .s0 = word s₁.mem B (slot w 0 + 8 * (w - 1))) :
    WP isa (.ite (.zero .s0) rrDbl rrHi) s₁ fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s₁.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (w + 2)) s₁.mem t.mem) ∧ Keep rrHiRegs s₁ t := by
  refine WP.ite (s₁.gpr .s0 == 0) (by rw [Steps.eval_zero]) (fun _ => ?_) (fun hc => ?_)
  · exact WP.mono (rrDbl_ok E hB hN) fun t ⟨q, k⟩ => ⟨q, k.mono (by decide)⟩
  · refine rrHi_ok E hB hodd (top_lt E.w2 hodd fun ht => ?_) hinv
    rw [beq_eq_false_iff_ne, a0] at hc
    exact hc (BitVec.eq_of_toNat_eq ht)

/-- The registers `rr` writes. -/
def rrRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s7]

/-- `rr`: `R² mod m = 2^(128 w) mod m` into arrays 1 and 24, for an odd `m ≥ 2` in
array 0 and `-m⁻¹ mod 2⁶⁴` in `t1`, changing only arrays 1–24. -/
theorem rr_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1)
    (hinv : ((word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0) :
    WP isa rr s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w 24) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (8 * (w + 2))) s.mem t.mem) ∧ Keep rrRegs s t := by
  unfold rr
  refine rrTop_ok h fun s₁ E hB a0 m1 k1 => ?_
  rw [← m1] at hN hodd hinv a0 ⊢
  exact WP.seq (WP.mono (rrIte_ok E hB hN hodd (by rw [k1.gpr (by decide)]; exact hinv) a0) fun s₂ ⟨⟨x2, o2⟩, k2⟩ =>
    WP.mono (rrCopy_ok (E.keep k2) o2) fun t ⟨⟨c1, c24, o⟩, k⟩ =>
      ⟨⟨by rw [c1, x2], by rw [c24, x2], o⟩, ((k1.trans k2).trans k).mono (by decide)⟩)

/-! ## Numbers out of a working space -/

/-- The registers `storeBE` writes. -/
def storeRegs : List Reg := [.s0, .t3, .t4, .t5]

/-- `storeBE j`: array `j`'s low `k` octets (`k` in `s8`), most significant
first, to `O` (`s7`), a buffer apart from the working space. -/
theorem storeBE_ok {s : State} {B O : Addr} {Z w k j : Nat} (h : Env s B Z w) (hj : j < 28)
    (ho : ∀ i < k, InRegions s.wr (off O i) 1) (hno : O.toNat + k ≤ 2 ^ 64) (h7 : s.gpr .s7 = O) (h8 : s.gpr .s8 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x) :
    WP isa (storeBE j) s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem O k) = (s.mem.read (off B (slot w j)) k).toNat ∧
        Outside O 0 k s.mem t.mem) ∧ Keep storeRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  obtain hZj := h.arr hj
  have hw48 := h.w48
  obtain hsl : 256 ≤ slot w j := by rw [Lay.slot_eq]; omega_using []
  unfold storeBE
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) j) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun s₂ => s₂.gpr .t3 = off B (slot w j + (k - 1)) ∧
    s₂.gpr .t4 = off O 0 ∧ s₂.gpr .t5 = BitVec.ofNat 64 k ∧ s₂.mem = s₁.mem)
    (by brun [a3, (k1.gpr (r := .s8) (by decide)).trans h8, (k1.gpr (r := .s7) (by decide)).trans h7, off_add,
        add_ofNat_zero]
        rw [off_sub _ (by omega_arith)]; congr 2; omega_arith) (by rfl) (by rfl)) fun s₂ ⟨⟨b3, b4, b5, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w j + (k - 1) - i) ∧ t.gpr .t4 = off O i ∧ Outside O 0 i s.mem t.mem ∧
      (∀ i' < i, t.mem (off O i') = s.mem (off B (slot w j + (k - 1 - i')))) ∧ Keep storeRegs s t
  refine WP.mono (wp_countdown (body := .block ([.load .b .s0 .t3 0, .store .b .s0 .t4 0, .addi .t4 .t4 1,
      .addi .t3 .t3 (-1)] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := k) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨t3, t4, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b3]; rfl, b4, by rw [m2, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k12.mono (by decide)⟩ b5) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have hrd : InRegions (t.rd ++ t.wr) (off B (slot w j + (k - 1) - i)) 1 := by
      rw [tk.2.1, tk.2.2]; exact hs.ld (show slot w j + (k - 1) - i + 1 ≤ Z by omega_arith)
    obtain hst : WP isa (.block [.load .b .s0 .t3 0, .store .b .s0 .t4 0, .addi .t4 .t4 1, .addi .t3 .t3 (-1),
        .addi .t5 .t5 (-1)]) t fun t' => t' = ((({ (t.write .s0
          ((t.mem.read (off B (slot w j + (k - 1) - i)) 1).setWidth 64)) with
          mem := t.mem.write (off O i) 1 (((t.mem.read (off B (slot w j + (k - 1) - i)) 1).setWidth 64).setWidth 8) } :
            State).write .t4 (off O (i + 1))).write .t3
              (off B (slot w j + (k - 1) - i) - BitVec.ofNat 64 1)).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [t3, t4, hrd, add_ofNat_zero, (show InRegions t.wr (off O i) 1 by rw [tk.2.2]; exact ho i (by omega_arith))]
    refine WP.mono hst fun t' e => ?_
    subst e
    obtain hw1 := write1_outside t.mem O (d := i)
      (((t.mem.read (off B (slot w j + (k - 1) - i)) 1).setWidth 64).setWidth 8) (by omega_arith)
    obtain harr : t.mem (off B (slot w j + (k - 1) - i)) = s.mem (off B (slot w j + (k - 1) - i)) := by
      refine tout _ (Or.inr ?_)
      by_contra hc
      have := hsep (off B (slot w j + (k - 1) - i)) (by omega_arith)
      rw [show ofs B (off B (slot w j + (k - 1) - i)) = slot w j + (k - 1) - i from
        Mem.sub_ofNat_toNat B (by omega_arith)] at this
      omega_arith
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; rw [off_sub _ (by omega_arith),
        show slot w j + (k - 1) - i - 1 = slot w j + (k - 1) - (i + 1) by omega_arith]
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
    · intro i' hi'
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i' hi'
      · rw [write1_self, read_one', show slot w j + (k - 1 - i') = slot w j + (k - 1) - i' by omega_arith, ← harr]
    · exact Keep.trans' tk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))
  · refine (VG.Proof.Bignum.reversed_read t.mem s.mem O (off B (slot w j)) k fun i hi => ?_).symm
    rw [off_add, tb (k - 1 - i) (by omega_arith), show k - 1 - (k - 1 - i) = i by omega_arith]

/-- The low `k` octets of a number of `w` words below `2^(8 k)` are the number. -/
theorem read_low (m : Mem) (B : Addr) {d w k : Nat} (hkw : k ≤ 8 * w)
    (hlt : wordsVal m B d w < 2 ^ (8 * k)) :
    (m.read (off B d) k).toNat = wordsVal m B d w := by
  obtain e1 := read_eq_wordsVal m B w d
  rw [show 8 * w = (8 * w - k) + k by omega_arith, read_toNat_add] at e1
  obtain hl := (m.read (off B d) k).isLt
  generalize (m.read (off B d) k).toNat = lo at e1 hl
  generalize (m.read (off B d + BitVec.ofNat 64 k) (8 * w - k)).toNat = hi at e1
  rcases Nat.eq_zero_or_pos hi with rfl | hp
  · omega_arith
  · have := Nat.le_mul_of_pos_right (2 ^ (8 * k)) hp
    omega_arith

end VG.Proof.Dsa.RISCV64
