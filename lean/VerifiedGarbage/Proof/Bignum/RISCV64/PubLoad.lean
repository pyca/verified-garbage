module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA public-key operation on RISC-V: the arrays' bases, `pre` and the input

`base_ok`: an array's base from array 0's (`a7`) and the arrays' size
(`s5`). `copyPre_ok`: `n` and `R² mod n` from `pre` into arrays 0 and 1;
`loadX_ok`: the input into array 4, its word `w` zero; `checkX_ok`: the
mask of whether the input is below `n`, and-ed into `s9`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

theorem base_cons (rd : Reg) (j : Nat) :
    base rd (j + 1) = base rd j ++ ([.add rd rd .s5] : List Instr) := by
  simp only [base, List.replicate_succ', List.cons_append]

/-- `base rd j`, array 0 at `a7` and the arrays' size in `s5`. -/
theorem base_ok {t : State} {B : Addr} {w : Nat} {rd : Reg} (hrd5 : rd ≠ .s5)
    (h7 : t.gpr .a7 = off B (slot w 0)) (h5 : t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (base rd j)) t fun t' =>
      (t'.gpr rd = off B (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    apply WP.of_runBlock
    simp only [base, List.replicate_zero, runBlock_cons, exec_addi_nat (show 0 < 2048 by decide), runStep_some,
      runBlock_nil, add_ofNat_zero, h7]
    exact ⟨_, rfl, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
  | j + 1 => by
    rw [base_cons, WP.block_append_iff]
    refine WP.mono (base_ok hrd5 h7 h5 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr (r := .s5) (by simpa using Ne.symm hrd5)).trans h5]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega]

/-- A word of a buffer apart from the working space, unchanged by writes to
it. -/
theorem Outside.word_apart {B P : Addr} {Z Zp o n : Nat} {m m' : Mem} (h : Outside B o n m m')
    (hsep : ∀ x, ofs P x < Zp → Z ≤ ofs B x) (hn : o + n ≤ Z) {d : Nat} (hd : d + 8 ≤ Zp)
    (hP : P.toNat + Zp ≤ 2 ^ 64) : word m' P d = word m P d :=
  Mem.readW_congr fun i hi => h _ (Or.inr (Nat.le_trans hn
    (hsep _ (by rw [ofs_off P (d := d) (i := i) (by omega_arith)]; omega_arith))))

/-- `copyWords`, `w` words from `dS` of `P` (`t4`), readable, aligned and apart
from the working space, to `dD` of the working space (`t3`), with `w` in `t0`. -/
theorem copyIn_ok {s : State} {B P : Addr} {Z Zp dS dD w : Nat} (hs : Scr s B Z)
    (hP : P.toNat + Zp ≤ 2 ^ 64) (hrd : ∀ i < w, InRegions (s.rd ++ s.wr) (off P (dS + 8 * i)) 8)
    (hal : ∀ i < w, (off P (dS + 8 * i)).toNat % 8 = 0)
    (h4 : s.gpr .t4 = off P dS) (h3 : s.gpr .t3 = off B dD) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD8 : dD % 8 = 0) (hS : dS + 8 * w ≤ Zp) (hD : dD + 8 * w ≤ Z)
    (hsep : ∀ x, ofs P x < Zp → Z ≤ ofs B x) :
    WP isa Precompute.copyWords s fun t =>
      (t.gpr .t3 = off B (dD + 8 * w) ∧ t.gpr .t4 = off P (dS + 8 * w) ∧
        (∀ i < w, word t.mem B (dD + 8 * i) = word s.mem P (dS + 8 * i)) ∧
        Outside B dD (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  unfold Precompute.copyWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h0, add_ofNat_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i5, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dD + 8 * i) ∧ t.gpr .t4 = off P (dS + 8 * i) ∧ Outside B dD (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (dD + 8 * k) = word s.mem P (dS + 8 * k)) ∧ Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith)
      (by omega_arith) Inv
    (fun i hi t ⟨j3, j4, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr (by decide), h3]; rfl, by rw [k₁.gpr (by decide), h4]; rfl,
      by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), k₁.mono (by decide)⟩ i5)
    fun t ⟨t3, t4, tout, tc, tk⟩ => ⟨⟨t3, t4, tc, tout⟩, tk⟩
  have hsrc : word t.mem P (dS + 8 * i) = word s.mem P (dS + 8 * i) :=
    Outside.word_apart jout hsep (by omega_arith) (by omega_arith) hP
  have hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
      .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ (t.write .s0 (word t.mem P (dS + 8 * i))) with
        mem := t.mem.writeW (off B (dD + 8 * i)) (word t.mem P (dS + 8 * i)) } :
        State).write .t3 (off B (dD + 8 * i + 8))).write .t4
          (off P (dS + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
    brun [j3, j4, add_ofNat_zero, (by rw [jk.2.1, jk.2.2]; exact hrd i hi : InRegions (t.rd ++ t.wr) (off P (dS + 8 * i)) 8),
      hal i hi, (hs.congr jk.2.2).st (show dD + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show dD + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := dD + 8 * i) (word t.mem P (dS + 8 * i)) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega_arith],
    by gsimp; rw [show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsrc]
  · exact Keep.trans' jk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-- `copyPre`: `pre`'s `2 w` words (`a2`) into arrays 0 and 1. -/
theorem copyPre_ok {s : State} {B P : Addr} {Z w : Nat} (hs : Scr s B Z) (hP : P.toNat + 16 * w ≤ 2 ^ 64)
    (hPa : P.toNat % 8 = 0)
    (hrd : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off P (8 * i)) 8) (h2 : s.gpr .a2 = off P 0)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hsep : ∀ x, ofs P x < 16 * w → Z ≤ ofs B x) :
    WP isa copyPre s fun t =>
      ((∀ i < w, word t.mem B (slot w 0 + 8 * i) = word s.mem P (8 * i)) ∧
        (∀ i < w, word t.mem B (slot w 1 + 8 * i) = word s.mem P (8 * w + 8 * i)) ∧
        Outside B (slot w 0) (16 * (w + 1)) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have pal : ∀ d, d % 8 = 0 → d < 16 * w → (off P d).toNat % 8 = 0 := fun d hd hd' => by
    have : (off P d).toNat = P.toNat + d := by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := d) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    rw [this]; omega_arith
  unfold copyPre
  refine WP.seq ?_
  refine WP.mono (WP.keep [.t3, .t4] (Q := fun s₁ => s₁.gpr .t3 = off B (slot w 0) ∧
    s₁.gpr .t4 = off P 0 ∧ s₁.mem = s.mem) (by brun [h7, h2, add_ofNat_zero]) (by rfl) (by rfl))
    fun s₁ ⟨⟨a3, a4, m1⟩, k1⟩ => ?_
  refine WP.seq (WP.mono (copyIn_ok (dS := 0) (dD := slot w 0) (hs.congr k1.2.2) hP
    (fun i hi => by rw [k1.2.1, k1.2.2, Nat.zero_add]; exact hrd i (by omega_arith))
    (fun i hi => by rw [Nat.zero_add]; exact pal _ (by omega_arith) (by omega_arith)) a4 a3
    ((k1.gpr (by decide)).trans h0) hw hw' (by omega_arith) (by omega_arith) (by omega_arith) hsep)
    fun s₂ ⟨⟨b3, b4, bw, bout⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.seq ?_
  refine WP.mono (WP.keep [.t3] (Q := fun s₃ => s₃.gpr .t3 = off B (slot w 1) ∧ s₃.mem = s₂.mem)
    (by brun [(k12.gpr (r := .a7) (by decide)).trans h7, (k12.gpr (r := .s5) (by decide)).trans h5, off_add]
        congr 1; omega_arith) (by rfl) (by rfl))
    fun s₃ ⟨⟨c3, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (copyIn_ok (dS := 0 + 8 * w) (dD := slot w 1) (hs.congr k13.2.2) hP
    (fun i hi => by rw [k13.2.1, k13.2.2, show 0 + 8 * w + 8 * i = 8 * (w + i) by omega_arith]; exact hrd _ (by omega_arith))
    (fun i hi => pal _ (by omega_arith) (by omega_arith))
    ((k3.gpr (by decide)).trans b4) c3 ((k13.gpr (by decide)).trans h0) hw hw' (by omega_arith) (by omega_arith)
    (by omega_arith) hsep) fun t ⟨⟨_, _, tw, tout⟩, k4⟩ => ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, (k13.trans k4).mono (by decide)⟩
  · rw [Outside.word tout (by omega_arith) (by omega_arith), m3, bw i hi, m1, Nat.zero_add]
  · rw [tw i hi, m3, Outside.word_apart bout hsep (by omega_arith) (by omega_arith) hP, m1, Nat.zero_add]
  · rw [m1] at bout
    rw [m3] at tout
    exact (Outside.mono bout (by omega_arith) (by omega_arith)).trans (Outside.mono tout (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.RISCV64.Pub
