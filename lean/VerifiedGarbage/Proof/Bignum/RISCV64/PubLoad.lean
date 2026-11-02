module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
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
    simp only [base, List.replicate_zero]
    apply WP.of_runBlock
    refine ⟨t.write rd (off B (slot w 0)), ?_, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
    simp only [runBlock_cons, runBlock_nil, exec_addi (show imm12 0 by decide), runStep_some,
      BitVec.ofInt_ofNat, BitVec.add_zero, h7]
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

/-- `loadX`: the input's `k` bytes (`a6`) into array 4 as `w` words, its word
`w` := 0, `a7` back to array 0 and `s7` as it was. -/
theorem loadX_ok {s : State} {B X : Addr} {Z w k : Nat} (hs : Scr s B Z) (h6s : s.gpr .s6 = B)
    (h6 : s.gpr .a6 = X) (h11 : s.gpr .s11 = BitVec.ofNat 64 k)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off X i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off X i ≠ x) :
    WP isa loadX s fun t =>
      (wordsVal t.mem B (slot w 4) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X k) ∧
        Mont.word t.mem B (slot w 4 + 8 * w) = 0 ∧ Outside B (slot w 4) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .a7 = off B (slot w 0) ∧ t.gpr .s7 = s.gpr .s7) ∧
      Keep [.a0, .a1, .a7, .s0, .s7, .s8, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e4 := e 4; have e5 := e 5; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have al4 : slot w 4 % 8 = 0 := slot_al w 4
  unfold loadX
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a7) (by decide) h7 h5 4) fun s₁ ⟨⟨a7', m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.a1, .s7, .s8] (Q := fun s₂ => s₂.gpr .a1 = s.gpr .s7 ∧ s₂.gpr .s7 = off X 0 ∧
    s₂.gpr .s8 = BitVec.ofNat 64 k ∧ s₂.mem = s₁.mem)
    (by brun [(k1.gpr (r := .s7) (by decide)), (k1.gpr (r := .a6) (by decide)).trans h6,
      (k1.gpr (r := .s11) (by decide)).trans h11, add_ofNat_zero])
    (by rfl) (by rfl)) fun s₂ ⟨⟨a1', a7x, a8, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 4) (hs.congr k12.2.2) ((k2.gpr (by decide)).trans a7')
    a7x a8 ((k12.gpr (by decide)).trans h0) hk hkw hw' (by omega_arith) al4 (by omega_arith)
    (by rw [k12.2.1, k12.2.2]; exact hrd) (by intro i hi x hx; exact hsep i hi x hx))
    fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  rw [m2, m1] at hv out₃
  have k13 := k12.trans k3
  have a7'' : s₃.gpr .a7 = off B (slot w 4) := (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans a7')
  have e16 : off B (slot w 4 + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w 4 + 8 * w) := by
    rw [off_sub B (show 16 ≤ slot w 4 + 8 * (w + 2) by omega_arith),
      show slot w 4 + 8 * (w + 2) - 16 = slot w 4 + 8 * w by omega_arith]
  have e256 : B + BitVec.ofNat 64 hdrBytes = off B (slot w 0) := by simp [off, slot]
  refine WP.mono (WP.keep [.t3, .s0, .a7, .s7] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w 4 + 8 * w)) (0 : BitVec 64) ∧ t.gpr .a7 = off B (slot w 0) ∧
      t.gpr .s7 = s.gpr .s7)
    ?_ (by rfl) (by rfl)) fun t ⟨⟨tm, t7, ts7⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t7, ts7⟩, (k13.trans k4).mono (by decide)⟩
  · brun [a7'', (k13.gpr (r := .s5) (by decide)).trans h5, (k13.gpr (r := .s6) (by decide)).trans h6s,
      (k3.gpr (r := .a1) (by decide)).trans a1', off_add, e16, e256, exec_li,
      exec_addi_nat (n := .s6) (d := .a7) (show hdrBytes < 2048 by decide), add_ofNat_zero,
      (hs.congr k13.2.2).st (show slot w 4 + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k13.2.2).al8 (show slot w 4 + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
    rfl
  · rw [tm, Outside.wordsVal (fun x hx => writeW_outside s₃.mem B (d := slot w 4 + 8 * w) 0 (by omega_arith) x hx)
      (by omega_arith) (by omega_arith)]
    exact hv
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (Outside.mono out₃ (Nat.le_refl _) (by omega_arith)).trans
      (Outside.mono (writeW_outside s₃.mem B (d := slot w 4 + 8 * w) 0 (by omega_arith)) (by omega_arith) (by omega_arith))

/-- `checkX`, the input in array 4 with its word `w` zero and `n` in array 0:
`s9 &=` all ones if the input is below `n`, else 0. -/
theorem checkX_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (htop : Mont.word s.mem B (slot w 4 + 8 * w) = 0) :
    WP isa checkX s fun t =>
      (t.gpr .s9 = s.gpr .s9 &&& (if wordsVal s.mem B (slot w 4) w < wordsVal s.mem B (slot w 0) w
          then BitVec.allOnes 64 else 0) ∧
        Outside B (slot w 3) (8 * w) s.mem t.mem) ∧
      Keep [.a0, .a5, .a6, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s9] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e3 := e 3; have e4 := e 4; have e8 := e 8
  unfold checkX
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a5) (by decide) h7 h5 4) fun s₁ ⟨⟨a5', m1⟩, k1⟩ => ?_
  refine WP.mono (base_ok (rd := .a6) (by decide) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) 3) fun s₂ ⟨⟨a6', m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 4) (dT := slot w 3) (dM := slot w 0)
    (hs.congr k12.2.2) ((k2.gpr (by decide)).trans a5') a6' ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h0) hw1 hw' (slot_al w 4) (slot_al w 3) (slot_al w 0) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨⟨c, hc, hD, h4⟩, out, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = s₃.gpr .s9 &&& s₃.gpr .s4 ∧ t.mem = s₃.mem)
    (by brun) (by rfl) (by rfl)) fun t ⟨⟨t9, tm⟩, k4⟩ =>
      ⟨⟨?_, by rw [m2, m1] at out; rw [tm]; exact Outside.mono out (Nat.le_refl _) (by omega_arith)⟩,
        (k13.trans k4).mono (by decide)⟩
  rw [t9, k3.gpr (r := .s9) (by decide), k12.gpr (r := .s9) (by decide), h4, m2, m1, htop]
  rw [m2, m1] at hD
  have hDl := wordsVal_lt s₃.mem B (slot w 3) w
  have hAl := wordsVal_lt s.mem B (slot w 4) w
  have hMl := wordsVal_lt s.mem B (slot w 0) w
  congr 1
  rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
  · have h : ¬ wordsVal s.mem B (slot w 4) w < wordsVal s.mem B (slot w 0) w := by omega_arith
    simp [h]
  · have h : wordsVal s.mem B (slot w 4) w < wordsVal s.mem B (slot w 0) w := by omega_arith
    simp [h]

end VG.Proof.Bignum.RISCV64.Pub
