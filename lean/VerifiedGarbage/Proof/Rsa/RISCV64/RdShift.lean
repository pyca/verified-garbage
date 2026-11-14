module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
public import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet
public import VerifiedGarbage.Proof.Bignum.ShiftStages
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLoops
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv
import VerifiedGarbage.Proof.Bignum.WordStepLazy
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the shifts by stages, which both the halvings (`RdTwos`) and the second
-- division (`RdStage2`) use

/-!
# Shifts by stages for `vg_rsa_recover_primes_det` on RISC-V

A number of the working space's `w` words shifted by a count in a register,
without a branch on the count:

* `shrStage_ok`, `shlStage_ok`: down or up by `2^j` words if bit `b + j` of
  the count is set (each word moved by a mask, `moveUp_ok`, `moveDown_ok`, the
  words shifted out cleared by it, `clearUp_ok`, `clearDown_ok`), nothing where
  `2^j ≥ w`, whose bit is zero;
* `shrStages_ok`, `shlStages_ok`: the stages `0, …, k - 1`, by
  `⌊c / 2^b⌋ mod 2^k` words (`VG.Proof.Bignum.ShiftStages.mod_two_pow_succ`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr mov)
open VG.Impl.Rsa.RISCV64.RecoverDet (stageMask stageMove stageClear stageBody shrStage shlStage shrStages
  shlStages shrBy shlBy tzStage tzScan ctz)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Proof.Rsa.RISCV64.Loops (out_step)

/-- A word of a masked selection, `x ⊕ ((h ⊕ x) ∧ mask)`. -/
theorem sel64 (x h : BitVec 64) (b : Bool) :
    x ^^^ ((h ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) = if b then h else x := by
  rw [BitVec.xor_comm]; exact select64_arith x h b

/-- A word of a masked clearing. -/
theorem clr64 (x : BitVec 64) (b : Bool) :
    x &&& ((if b then BitVec.allOnes 64 else 0) ^^^ -1#64) = if b then 0 else x := by
  cases b
  · show x &&& (0#64 ^^^ BitVec.allOnes 64) = x
    rw [BitVec.zero_xor, BitVec.and_allOnes]
  · show x &&& (BitVec.allOnes 64 ^^^ BitVec.allOnes 64) = 0#64
    rw [BitVec.xor_self, BitVec.and_zero]

/-- A count's bit as a mask. -/
theorem mask_bit {r : Nat} (hr : r < 2 ^ 64) (k : Nat) :
    0#64 - (BitVec.ofNat 64 r >>> k &&& 1#64) =
      if r / 2 ^ k % 2 = 1 then BitVec.allOnes 64 else 0 := by
  have e : (BitVec.ofNat 64 r >>> k &&& 1#64) = BitVec.ofNat 64 (r / 2 ^ k % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr,
      Nat.shiftRight_eq_div_pow, show (1#64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat, Nat.pow_one, Nat.mod_eq_of_lt (show r / 2 ^ k % 2 < 2 ^ 64 by omega_using [])]
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (r / 2 ^ k) with h | h <;> rw [h] <;> decide

/-! ## The masked moves and clearings -/

/-- `countLoop .t5 (stageMove 8)`: `n` words from `dX`, word `i` := word `i + P`
if `b` (the mask in `t4`), from the first up. -/
theorem moveUp_ok {s : State} {B : Addr} {Z dX P n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dX) (h1 : s.gpr .t1 = off B (dX + 8 * P)) (h5 : s.gpr .t5 = BitVec.ofNat 64 n)
    (h4 : s.gpr .t4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hX8 : dX % 8 = 0)
    (hZ : dX + 8 * (n + P) ≤ Z) :
    WP isa (countLoop .t5 (stageMove 8)) s fun t => t.gpr .t0 = off B (dX + 8 * n) ∧
      wordsVal t.mem B dX n = (if b then wordsVal s.mem B (dX + 8 * P) n else wordsVal s.mem B dX n) ∧
      Outside B dX (8 * n) s.mem t.mem ∧ Keep [.t0, .t1, .t5, .a7, .a3] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dX + 8 * i) ∧ t.gpr .t1 = off B (dX + 8 * (i + P)) ∧ Outside B dX (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dX i = (if b then wordsVal s.mem B (dX + 8 * P) i else wordsVal s.mem B dX i) ∧
      Keep [.t0, .t1, .t5, .a7, .a3] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ _ => ?_)
    ⟨by rw [h0]; rfl, by rw [h1, Nat.zero_add], Outside.refl _ _ _ _, by cases b <;> rfl, Keep.refl _ _⟩ h5)
    fun t ⟨t0, _, tout, teq, tk⟩ => ⟨t0, teq, tout, tk⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .t4 = if b then BitVec.allOnes 64 else 0 := (jk.gpr (r := .t4) (by decide)).trans h4
  refine WP.mono (WP.keep [.t0, .t1, .t5, .a7, .a3] (Q := fun t' =>
      t'.gpr .t0 = off B (dX + 8 * i + 8) ∧ t'.gpr .t1 = off B (dX + 8 * (i + P) + 8) ∧
        t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dX + 8 * i))
          (word t.mem B (dX + 8 * i) ^^^ ((word t.mem B (dX + 8 * (i + P)) ^^^ word t.mem B (dX + 8 * i)) &&&
            (if b then BitVec.allOnes 64 else 0)))) (by
    unfold stageMove
    brun [j0, j1, ja, BitVec.add_zero, exec_addi_nat (show 8 < 2048 by decide),
      hs'.ld (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi]) (by omega_using [hX8]),
      hs'.ld (show dX + 8 * (i + P) + 8 ≤ Z by omega_using [hZ, hi]), hs'.al8 (show dX + 8 * (i + P) + 8 ≤ Z by omega_using [hZ, hi]) (by omega_using [hX8]),
      hs'.st (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi])]) (by rfl) (by rfl)) fun t' ⟨⟨l0, l1, l5, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans lk |>.mono (by decide)⟩, l5⟩
  · rw [l0, show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega_using []]
  · rw [l1, show dX + 8 * (i + P) + 8 = dX + 8 * (i + 1 + P) by omega_using []]
  · rw [lm]; exact out_step _ jout (by omega_using [hZ, hnw, hi])
  · have wa : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega_using []) (by omega_using [hZ, hnw, hi])
    have wb : word t.mem B (dX + 8 * (i + P)) = word s.mem B (dX + 8 * P + 8 * i) := by
      rw [show dX + 8 * P + 8 * i = dX + 8 * (i + P) by omega_using []]; exact jout.word (by omega_using []) (by omega_using [hZ, hnw, hi])
    rw [lm, sel64, fin64_wordsVal_write_top _ _ _ _ _ (by omega_using [hZ, hnw, hi]), wa, wb, jeq]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [← wordsVal_succ_top]
    · simp only [ite_true]; rw [← wordsVal_succ_top]

/-- `countLoop .t5 (stageClear 8)`: `n` words from `dX` cleared if `b` (the
inverted mask in `a3`). -/
theorem clearUp_ok {s : State} {B : Addr} {Z dX n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dX) (h5 : s.gpr .t5 = BitVec.ofNat 64 n)
    (h3 : s.gpr .a3 = (if b then BitVec.allOnes 64 else 0) ^^^ -1#64) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hX8 : dX % 8 = 0) (hZ : dX + 8 * n ≤ Z) :
    WP isa (countLoop .t5 (stageClear 8)) s fun t =>
      wordsVal t.mem B dX n = (if b then 0 else wordsVal s.mem B dX n) ∧
      Outside B dX (8 * n) s.mem t.mem ∧ Keep [.t0, .t5, .a7] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dX + 8 * i) ∧ Outside B dX (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dX i = (if b then 0 else wordsVal s.mem B dX i) ∧ Keep [.t0, .t5, .a7] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨j0, jout, jeq, jk⟩ _ => ?_)
    ⟨by rw [h0]; rfl, Outside.refl _ _ _ _, by cases b <;> rfl, Keep.refl _ _⟩ h5)
    fun t ⟨_, tout, teq, tk⟩ => ⟨teq, tout, tk⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a3 = (if b then BitVec.allOnes 64 else 0) ^^^ -1#64 := (jk.gpr (r := .a3) (by decide)).trans h3
  refine WP.mono (WP.keep [.t0, .t5, .a7] (Q := fun t' =>
      t'.gpr .t0 = off B (dX + 8 * i + 8) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dX + 8 * i))
          (word t.mem B (dX + 8 * i) &&& ((if b then BitVec.allOnes 64 else 0) ^^^ -1#64))) (by
    unfold stageClear
    brun [j0, ja, BitVec.add_zero, exec_addi_nat (show 8 < 2048 by decide),
      hs'.ld (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi]) (by omega_using [hX8]),
      hs'.st (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi])]) (by rfl) (by rfl))
    fun t' ⟨⟨l0, l5, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans lk |>.mono (by decide)⟩, l5⟩
  · rw [l0, show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega_using []]
  · rw [lm]; exact out_step _ jout (by omega_using [hZ, hnw, hi])
  · have wa : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega_using []) (by omega_using [hZ, hnw, hi])
    rw [lm, clr64, fin64_wordsVal_write_top _ _ _ _ _ (by omega_using [hZ, hnw, hi]), wa, jeq]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [← wordsVal_succ_top]
    · simp

theorem exec_srl_imm {s : State} {d n : Reg} {k : Nat} (hk : k < 64) :
    exec (.shift .srl .d d n k) s = some (s.write d (s.gpr n >>> k)) := by
  simp only [exec, hk, ite_true]

theorem exec_sll_imm {s : State} {d n : Reg} {k : Nat} (hk : k < 64) :
    exec (.shift .sll .d d n k) s = some (s.write d (s.gpr n <<< k)) := by
  simp only [exec, hk, ite_true]

/-- The registers a stage writes. -/
abbrev stRegs : List Reg := [.t0, .t1, .t3, .t4, .t5, .a7, .a3, .a4]

theorem bv_le_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ≤ BitVec.ofNat 64 b) ↔ a ≤ b := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- The high part of a number of words, by the low part's words. -/
theorem wordsVal_div {m : Mem} {B : Addr} {d P n : Nat} :
    wordsVal m B d (P + n) / 2 ^ (64 * P) = wordsVal m B (d + 8 * P) n := by
  rw [wordsVal_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wordsVal_lt _ _ _ _), Nat.zero_add]

/-- `shrStage X R b j`, the count `r` in `R`: `[X] := ⌊[X] / 2^(64 · 2^j)⌋` (its
`w` words) if bit `b + j` of `r` is set, a bit that is zero where `2^j ≥ w`. -/
theorem shrStage_ok {s : State} {B : Addr} {Z w N X : Nat} {R : Reg} {r b j : Nat} (h : Ws s B Z w N)
    (hX : X < N) (hN : N ≤ 2048) (hR : s.gpr R = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) (hRr : R ∉ stRegs)
    (hj : j ≤ 10) (hbj : b + j < 64) (hbit : w ≤ 2 ^ j → r / 2 ^ (b + j) % 2 = 0) :
    WP isa (shrStage X R b j) s fun t => Ws t B Z w N ∧ Frame B w [X] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w X) w = (if r / 2 ^ (b + j) % 2 = 1 then wordsVal s.mem B (arr w X) w / 2 ^ (64 * 2 ^ j)
        else wordsVal s.mem B (arr w X) w) ∧ Keep stRegs s t := by
  have fit := h.arr_fit hX
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have hw0 := h.wpos
  have hpj : 2 ^ j ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hj
  have hpj0 := Nat.two_pow_pos j
  unfold shrStage
  refine WP.seq (WP.mono (WP.keep [.t3, .t4, .a4] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (2 ^ j) ∧
      u.gpr .t4 = (if r / 2 ^ (b + j) % 2 = 1 then BitVec.allOnes 64 else 0) ∧ u.mem = s.mem) (by
    unfold stageMask
    brun [hR, exec_li_nat (show 2 ^ j < 2048 by omega_using [hpj]), fin64_exec_li_zero, exec_srl_imm hbj]
    rw [ite_eq_right (fun e => hRr (by rw [e]; decide))]
    exact mask_bit hr _) (by rfl) (by rfl))
    fun u ⟨⟨u3, u4, um⟩, uk⟩ => ?_)
  have hu := h.of_keep uk
  have u9 : u.gpr .s9 = BitVec.ofNat 64 w := hu.s9
  refine WP.ite (decide (w ≤ 2 ^ j)) (by
    show some (decide (u.gpr .s9 ≤ u.gpr .t3)) = _
    rw [u3, u9]; congr 1; exact decide_eq_decide.mpr (bv_le_ofNat (by omega_using [hwl]) (by omega_using [hpj]))) (fun hc => ?_) (fun hc => ?_)
  · -- `2^j ≥ w`: nothing, and the bit is zero.
    have hb0 := hbit (of_decide_eq_true hc)
    refine WP.block_nil_iff.mpr ⟨hu, by rw [um]; exact Frame.refl _ _ _ _ _, ?_, uk.mono (by decide)⟩
    rw [um]; simp [hb0]
  · have hlt : 2 ^ j < w := by have := of_decide_eq_false hc; omega_using [this]
    rw [WP.seq_iff]
    refine ptr_ok hu (by decide) (by decide) (show X < 2048 by omega_using [hX, hN]) ?_
    refine WP.mono (WP.keep [.t1, .t5] (Q := fun v => v.gpr .t1 = off B (arr w X + 8 * 2 ^ j) ∧
        v.gpr .t5 = BitVec.ofNat 64 (w - 2 ^ j) ∧ v.mem = u.mem) (by
      brun [u3, u9, shl3_ofNat, off_add, bv_sub_lit (show w < 2 ^ 64 by omega_using [hwl]) (show 2 ^ j ≤ w by omega_using [hlt])]) (by rfl) (by rfl)) fun v ⟨⟨v1, v5, vm⟩, vk⟩ => ?_
    have kv : Keep [.t3, .t4, .a4, .t0, .t1, .t5] s v :=
      ((uk.trans ((Keep.write _ _ _).trans vk)).mono (by decide))
    have hv := h.of_keep kv
    have v0 : v.gpr .t0 = off B (arr w X) := by rw [vk.gpr (by decide)]; simp [gpr_write]
    have v4 : v.gpr .t4 = if r / 2 ^ (b + j) % 2 = 1 then BitVec.allOnes 64 else 0 := by
      rw [vk.gpr (by decide), gpr_write, ite_eq_right (by decide)]; exact u4
    have v3 : v.gpr .t3 = BitVec.ofNat 64 (2 ^ j) := by
      rw [vk.gpr (by decide), gpr_write, ite_eq_right (by decide)]; exact u3
    have hvm : v.mem = s.mem := vm.trans um
    have al := arr_al w X
    -- The moves: word `i` := word `i + 2^j` if the bit is set.
    rw [stageBody, WP.seq_iff]
    refine WP.mono (moveUp_ok (b := decide (r / 2 ^ (b + j) % 2 = 1)) (P := 2 ^ j) (n := w - 2 ^ j) hv.scr v0
      v1 v5 (by simpa using v4) (by omega_using [hlt]) (by omega_using [hwl, hpj0]) al (by omega_using [fit, hSz, hlt])) fun t₁ ⟨l0, lv, lo, lk⟩ => ?_
    rw [hvm] at lv lo
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.a3, .t5] (Q := fun t₂ => t₂.gpr .a3 =
        (if decide (r / 2 ^ (b + j) % 2 = 1) then BitVec.allOnes 64 else 0) ^^^ -1#64 ∧
        t₂.gpr .t5 = BitVec.ofNat 64 (2 ^ j) ∧ t₂.mem = t₁.mem) (by
      have l4 : t₁.gpr .t4 = if decide (r / 2 ^ (b + j) % 2 = 1) then BitVec.allOnes 64 else 0 := by
        rw [lk.gpr (by decide)]; simpa using v4
      have l3 : t₁.gpr .t3 = BitVec.ofNat 64 (2 ^ j) := by rw [lk.gpr (by decide)]; exact v3
      brun [mov, l4, l3, BitVec.add_zero]) (by rfl) (by rfl)) fun t₂ ⟨⟨m3, m5, mm⟩, mk⟩ => ?_
    have l0' : t₂.gpr .t0 = off B (arr w X + 8 * (w - 2 ^ j)) := by rw [mk.gpr (by decide)]; exact l0
    refine WP.mono (clearUp_ok (hv.scr.congr (lk.trans mk).2.2) l0' m5 m3 (by omega_using [hpj0]) (by omega_using [hpj]) (by omega_using [al])
      (by omega_using [fit, hSz, hlt])) fun t ⟨cv, co, ck⟩ => ?_
    rw [mm] at co cv
    have kk : Keep stRegs s t := (((kv.trans lk).trans mk).trans ck).mono (by decide)
    refine ⟨h.of_keep kk, ?_, ?_, kk⟩
    · exact Frame.of_arr (o := X) (d := 0) (n := 8 * w) (by
        have := (lo.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [hpj0])).trans
          ((co.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [hlt])))
        simpa using this) (by omega_using [hSz]) (by simp)
    · -- `w = (w - 2^j) + 2^j` words: the moved ones, then the cleared ones.
      have e := wordsVal_append t.mem B (arr w X) (w - 2 ^ j) (2 ^ j)
      rw [show w - 2 ^ j + 2 ^ j = w by omega_using [hlt]] at e
      rw [e, cv, Outside.wordsVal co (by omega_using []) (by omega_using [fit, nw, hSz, hpj0]), lv]
      have e2 := wordsVal_append s.mem B (arr w X) (2 ^ j) (w - 2 ^ j)
      rw [show 2 ^ j + (w - 2 ^ j) = w by omega_using [hlt]] at e2
      by_cases hb : r / 2 ^ (b + j) % 2 = 1
      · simp only [hb, decide_true, ite_true, Nat.mul_zero, Nat.add_zero]
        rw [e2, Nat.mul_comm (2 ^ (64 * 2 ^ j)), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt (wordsVal_lt _ _ _ _), Nat.zero_add]
      · simp only [hb, decide_false, Bool.false_eq_true, ite_false]
        have e3 := wordsVal_append s.mem B (arr w X) (w - 2 ^ j) (2 ^ j)
        rw [show w - 2 ^ j + 2 ^ j = w by omega_using [hlt]] at e3
        rw [e3, Outside.wordsVal lo (by omega_using []) (by omega_using [fit, nw, hSz, hlt])]

/-- Bit `b + k` of `r`: bit `k` of `⌊r / 2^b⌋`. -/
theorem bit_shift (r b k : Nat) : r / 2 ^ (b + k) % 2 = r / 2 ^ b / 2 ^ k % 2 := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- `shrStages X R b k`, the count `r` in `R`, `⌊r / 2^b⌋ < w`:
`[X] := ⌊[X] / 2^(64 (⌊r / 2^b⌋ mod 2^k))⌋`. -/
theorem shrStages_ok {s : State} {B : Addr} {Z w N X : Nat} {R : Reg} {r b K : Nat} (h : Ws s B Z w N)
    (hX : X < N) (hN : N ≤ 2048) (hR : s.gpr R = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) (hRr : R ∉ stRegs)
    (hb : b + K ≤ 64) (hK : K ≤ 11) (hc : r / 2 ^ b < w) : ∀ k ≤ K,
    WP isa (shrStages X R b k) s fun t => Ws t B Z w N ∧ Frame B w [X] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w X) w = wordsVal s.mem B (arr w X) w / 2 ^ (64 * (r / 2 ^ b % 2 ^ k)) ∧
      Keep stRegs s t
  | 0, _ => by
    refine WP.block_nil_iff.mpr ⟨h, Frame.refl _ _ _ _ _, ?_, Keep.refl _ _⟩
    rw [Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  | k + 1, hk => by
    rw [shrStages]
    refine WP.seq (WP.mono (shrStages_ok h hX hN hR hr hRr hb hK hc k (by omega_using [hk])) fun u ⟨hu, fu, vu, ku⟩ => ?_)
    have uR : u.gpr R = BitVec.ofNat 64 r := (ku.gpr hRr).trans hR
    refine WP.mono (shrStage_ok (j := k) hu hX hN uR hr hRr (by omega_using [hK, hk]) (by omega_using [hb, hk]) fun hw => ?_)
      fun t ⟨ht, ft, vt, kt⟩ => ⟨ht, fu.trans ft, ?_, (ku.trans kt).mono (by decide)⟩
    · rw [bit_shift, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hc hw)]
    · rw [vt, vu, VG.Proof.Bignum.ShiftStages.mod_two_pow_succ, ← bit_shift]
      split
      · rename_i hbit
        rw [hbit, Nat.one_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add]
      · rename_i hbit
        rw [show r / 2 ^ (b + k) % 2 = 0 by omega_using [hbit], Nat.zero_mul, Nat.add_zero]

/-- `countLoop .t5 (stageMove (-8))`: from the top, the `n` words at `dX + 8 P`,
word `P + i` := word `i` if `b` (the mask in `t4`). -/
theorem moveDown_ok {s : State} {B : Addr} {Z dX P n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B (dX + 8 * (P + n)) - BitVec.ofNat 64 8)
    (h1 : s.gpr .t1 = off B (dX + 8 * n) - BitVec.ofNat 64 8) (h5 : s.gpr .t5 = BitVec.ofNat 64 n)
    (h4 : s.gpr .t4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hP : 1 ≤ P)
    (hX8 : dX % 8 = 0) (hX : 8 ≤ dX) (hZ : dX + 8 * (n + P) ≤ Z) :
    WP isa (countLoop .t5 (stageMove (-8))) s fun t => t.gpr .t0 = off B (dX + 8 * P) - BitVec.ofNat 64 8 ∧
      wordsVal t.mem B (dX + 8 * P) n = (if b then wordsVal s.mem B dX n else wordsVal s.mem B (dX + 8 * P) n) ∧
      Outside B (dX + 8 * P) (8 * n) s.mem t.mem ∧ Keep [.t0, .t1, .t5, .a7, .a3] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dX + 8 * (P + n - i)) - BitVec.ofNat 64 8 ∧
      t.gpr .t1 = off B (dX + 8 * (n - i)) - BitVec.ofNat 64 8 ∧
      Outside B (dX + 8 * (P + n - i)) (8 * i) s.mem t.mem ∧
      wordsVal t.mem B (dX + 8 * (P + n - i)) i =
        (if b then wordsVal s.mem B (dX + 8 * (n - i)) i else wordsVal s.mem B (dX + 8 * (P + n - i)) i) ∧
      Keep [.t0, .t1, .t5, .a7, .a3] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := n) (by omega) (by omega) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ _ => ?_)
    ⟨by rw [h0, Nat.sub_zero], by rw [h1, Nat.sub_zero], Outside.refl _ _ _ _, by cases b <;> rfl, Keep.refl _ _⟩ h5)
    fun t ⟨t0, _, tout, teq, tk⟩ => ⟨by rw [t0, show P + n - n = P by omega],
      by rw [show P + n - n = P by omega, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at teq; exact teq,
      by rw [show P + n - n = P by omega] at tout; exact tout, tk⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .t4 = if b then BitVec.allOnes 64 else 0 := (jk.gpr (r := .t4) (by decide)).trans h4
  generalize hk : P + n - 1 - i = k
  generalize hl : n - 1 - i = l
  have e0 : t.gpr .t0 = off B (dX + 8 * k) := by
    rw [j0, off_sub B (show 8 ≤ dX + 8 * (P + n - i) by omega)]; congr 1; omega
  have e1 : t.gpr .t1 = off B (dX + 8 * l) := by
    rw [j1, off_sub B (show 8 ≤ dX + 8 * (n - i) by omega)]; congr 1; omega
  refine WP.mono (WP.keep [.t0, .t1, .t5, .a7, .a3] (Q := fun t' =>
      t'.gpr .t0 = off B (dX + 8 * k) - BitVec.ofNat 64 8 ∧ t'.gpr .t1 = off B (dX + 8 * l) - BitVec.ofNat 64 8 ∧
        t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dX + 8 * k))
          (word t.mem B (dX + 8 * k) ^^^ ((word t.mem B (dX + 8 * l) ^^^ word t.mem B (dX + 8 * k)) &&&
            (if b then BitVec.allOnes 64 else 0)))) (by
    unfold stageMove
    brun [e0, e1, ja, BitVec.add_zero,
      hs'.ld (show dX + 8 * k + 8 ≤ Z by omega), hs'.al8 (show dX + 8 * k + 8 ≤ Z by omega) (by omega),
      hs'.ld (show dX + 8 * l + 8 ≤ Z by omega), hs'.al8 (show dX + 8 * l + 8 ≤ Z by omega) (by omega),
      hs'.st (show dX + 8 * k + 8 ≤ Z by omega)]) (by rfl) (by rfl))
    fun t' ⟨⟨l0, l1, l5, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans lk |>.mono (by decide)⟩, l5⟩
  · rw [l0, show dX + 8 * k = dX + 8 * (P + n - (i + 1)) by omega]
  · rw [l1, show dX + 8 * l = dX + 8 * (n - (i + 1)) by omega]
  · rw [lm, show dX + 8 * (P + n - (i + 1)) = dX + 8 * k by omega]
    exact ((jout.mono (o' := dX + 8 * k) (n' := 8 * (i + 1)) (by omega) (by omega))).trans
      ((writeW_outside _ B (d := dX + 8 * k) _ (by omega)).mono (by omega) (by omega))
  · have wa : word t.mem B (dX + 8 * k) = word s.mem B (dX + 8 * k) := jout.word (by omega) (by omega)
    have wb : word t.mem B (dX + 8 * l) = word s.mem B (dX + 8 * l) := jout.word (by omega) (by omega)
    have o1 := writeW_outside t.mem B (d := dX + 8 * k) (if b then word s.mem B (dX + 8 * l) else
      word s.mem B (dX + 8 * k)) (by omega)
    rw [lm, sel64, wa, wb, show dX + 8 * (P + n - (i + 1)) = dX + 8 * k by omega,
      show dX + 8 * (n - (i + 1)) = dX + 8 * l by omega]
    simp only [wordsVal]
    rw [word_writeW_self, o1.wordsVal (by omega) (by omega), show dX + 8 * k + 8 = dX + 8 * (P + n - i) by omega,
      jeq, show dX + 8 * l + 8 = dX + 8 * (n - i) by omega]
    cases b <;> rfl

/-- `countLoop .t5 (stageClear (-8))`: from the top, the `P` words at `dX`
cleared if `b` (the inverted mask in `a3`). -/
theorem clearDown_ok {s : State} {B : Addr} {Z dX P : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B (dX + 8 * P) - BitVec.ofNat 64 8) (h5 : s.gpr .t5 = BitVec.ofNat 64 P)
    (h3 : s.gpr .a3 = (if b then BitVec.allOnes 64 else 0) ^^^ -1#64) (hP : 1 ≤ P) (hP' : P < 2 ^ 32)
    (hX8 : dX % 8 = 0) (hX : 8 ≤ dX) (hZ : dX + 8 * P ≤ Z) :
    WP isa (countLoop .t5 (stageClear (-8))) s fun t =>
      wordsVal t.mem B dX P = (if b then 0 else wordsVal s.mem B dX P) ∧
      Outside B dX (8 * P) s.mem t.mem ∧ Keep [.t0, .t5, .a7] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dX + 8 * (P - i)) - BitVec.ofNat 64 8 ∧ Outside B (dX + 8 * (P - i)) (8 * i) s.mem t.mem ∧
      wordsVal t.mem B (dX + 8 * (P - i)) i = (if b then 0 else wordsVal s.mem B (dX + 8 * (P - i)) i) ∧
      Keep [.t0, .t5, .a7] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := P) (by omega_using [hP']) (by omega_using [hP]) Inv
    (fun i hi t ⟨j0, jout, jeq, jk⟩ _ => ?_)
    ⟨by rw [h0, Nat.sub_zero], Outside.refl _ _ _ _, by cases b <;> rfl, Keep.refl _ _⟩ h5)
    fun t ⟨_, tout, teq, tk⟩ => ⟨by simpa using teq, by simpa using tout, tk⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a3 = (if b then BitVec.allOnes 64 else 0) ^^^ -1#64 := (jk.gpr (r := .a3) (by decide)).trans h3
  generalize hk : P - 1 - i = k
  have e0 : t.gpr .t0 = off B (dX + 8 * k) := by
    rw [j0, off_sub B (show 8 ≤ dX + 8 * (P - i) by omega_using [hX])]; congr 1; omega_using [hi, hk]
  refine WP.mono (WP.keep [.t0, .t5, .a7] (Q := fun t' =>
      t'.gpr .t0 = off B (dX + 8 * k) - BitVec.ofNat 64 8 ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dX + 8 * k))
          (word t.mem B (dX + 8 * k) &&& ((if b then BitVec.allOnes 64 else 0) ^^^ -1#64))) (by
    unfold stageClear
    brun [e0, ja, BitVec.add_zero,
      hs'.ld (show dX + 8 * k + 8 ≤ Z by omega_using [hP, hZ, hk]), hs'.al8 (show dX + 8 * k + 8 ≤ Z by omega_using [hP, hZ, hk]) (by omega_using [hX8]),
      hs'.st (show dX + 8 * k + 8 ≤ Z by omega_using [hP, hZ, hk])]) (by rfl) (by rfl))
    fun t' ⟨⟨l0, l5, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans lk |>.mono (by decide)⟩, l5⟩
  · rw [l0, show dX + 8 * k = dX + 8 * (P - (i + 1)) by omega_using [hk]]
  · rw [lm, show dX + 8 * (P - (i + 1)) = dX + 8 * k by omega_using [hk]]
    exact ((jout.mono (o' := dX + 8 * k) (n' := 8 * (i + 1)) (by omega_using [hk]) (by omega_using [hk]))).trans
      ((writeW_outside _ B (d := dX + 8 * k) _ (by omega_using [hP, hZ, hnw, hk])).mono (by omega_using []) (by omega_using []))
  · have wa : word t.mem B (dX + 8 * k) = word s.mem B (dX + 8 * k) := jout.word (by omega_using [hi, hk]) (by omega_using [hP, hZ, hnw, hk])
    have o1 := writeW_outside t.mem B (d := dX + 8 * k) (if b then 0 else word s.mem B (dX + 8 * k)) (by omega_using [hP, hZ, hnw, hk])
    rw [lm, clr64, wa, show dX + 8 * (P - (i + 1)) = dX + 8 * k by omega_using [hk]]
    simp only [wordsVal]
    rw [word_writeW_self, o1.wordsVal (by omega_using []) (by omega_using [hZ, hnw, hi, hk]), show dX + 8 * k + 8 = dX + 8 * (P - i) by omega_using [hi, hk], jeq]
    cases b <;> simp

/-- `shlStage X R b j`, the count `r` in `R`: `[X] := [X] 2^(64 · 2^j) mod
2^(64 w)` if bit `b + j` of `r` is set, a bit that is zero where `2^j ≥ w`. -/
theorem shlStage_ok {s : State} {B : Addr} {Z w N X : Nat} {R : Reg} {r b j : Nat} (h : Ws s B Z w N)
    (hX : X < N) (hN : N ≤ 2048) (hR : s.gpr R = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) (hRr : R ∉ stRegs)
    (hj : j ≤ 10) (hbj : b + j < 64) (hbit : w ≤ 2 ^ j → r / 2 ^ (b + j) % 2 = 0) :
    WP isa (shlStage X R b j) s fun t => Ws t B Z w N ∧ Frame B w [X] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w X) w = (if r / 2 ^ (b + j) % 2 = 1 then
        wordsVal s.mem B (arr w X) w * 2 ^ (64 * 2 ^ j) % 2 ^ (64 * w) else wordsVal s.mem B (arr w X) w) ∧
      Keep stRegs s t := by
  have fit := h.arr_fit hX
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have hw0 := h.wpos
  have hpj : 2 ^ j ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hj
  have hpj0 := Nat.two_pow_pos j
  have hXa := hdr_le_arr w X
  have hhdr : hdr = 256 := rfl
  unfold shlStage
  refine WP.seq (WP.mono (WP.keep [.t3, .t4, .a4] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (2 ^ j) ∧
      u.gpr .t4 = (if r / 2 ^ (b + j) % 2 = 1 then BitVec.allOnes 64 else 0) ∧ u.mem = s.mem) (by
    unfold stageMask
    brun [hR, exec_li_nat (show 2 ^ j < 2048 by omega_using [hpj]), fin64_exec_li_zero, exec_srl_imm hbj]
    rw [ite_eq_right (fun e => hRr (by rw [e]; decide))]
    exact mask_bit hr _) (by rfl) (by rfl))
    fun u ⟨⟨u3, u4, um⟩, uk⟩ => ?_)
  have hu := h.of_keep uk
  have u9 : u.gpr .s9 = BitVec.ofNat 64 w := hu.s9
  refine WP.ite (decide (w ≤ 2 ^ j)) (by
    show some (decide (u.gpr .s9 ≤ u.gpr .t3)) = _
    rw [u3, u9]; congr 1; exact decide_eq_decide.mpr (bv_le_ofNat (by omega_using [hwl]) (by omega_using [hpj]))) (fun hc => ?_) (fun hc => ?_)
  · have hb0 := hbit (of_decide_eq_true hc)
    refine WP.block_nil_iff.mpr ⟨hu, by rw [um]; exact Frame.refl _ _ _ _ _, ?_, uk.mono (by decide)⟩
    rw [um]; simp [hb0]
  · have hlt : 2 ^ j < w := by have := of_decide_eq_false hc; omega_using [this]
    rw [WP.seq_iff]
    refine ptr_ok hu (by decide) (by decide) (show X < 2048 by omega_using [hX, hN]) ?_
    refine WP.mono (WP.keep [.t0, .t1, .t5] (Q := fun v => v.gpr .t0 = off B (arr w X + 8 * w) - BitVec.ofNat 64 8 ∧
        v.gpr .t1 = off B (arr w X + 8 * w) - BitVec.ofNat 64 8 - BitVec.ofNat 64 (8 * 2 ^ j) ∧
        v.gpr .t5 = BitVec.ofNat 64 (w - 2 ^ j) ∧ v.mem = u.mem) (by
      brun [u3, u9, shl3_ofNat, off_add, bv_sub_lit (show w < 2 ^ 64 by omega_using [hwl]) (show 2 ^ j ≤ w by omega_using [hlt])])
      (by rfl) (by rfl)) fun v ⟨⟨v0, v1, v5, vm⟩, vk⟩ => ?_
    have kv : Keep [.t3, .t4, .a4, .t0, .t1, .t5] s v :=
      ((uk.trans ((Keep.write _ _ _).trans vk)).mono (by decide))
    have hv := h.of_keep kv
    have v4 : v.gpr .t4 = if r / 2 ^ (b + j) % 2 = 1 then BitVec.allOnes 64 else 0 := by
      rw [vk.gpr (by decide), gpr_write, ite_eq_right (by decide)]; exact u4
    have v3 : v.gpr .t3 = BitVec.ofNat 64 (2 ^ j) := by
      rw [vk.gpr (by decide), gpr_write, ite_eq_right (by decide)]; exact u3
    have hvm : v.mem = s.mem := vm.trans um
    have al := arr_al w X
    generalize hn : w - 2 ^ j = n at v5
    have v0' : v.gpr .t0 = off B (arr w X + 8 * (2 ^ j + n)) - BitVec.ofNat 64 8 := by
      rw [v0, show 2 ^ j + n = w by omega_using [hlt, hn]]
    have v1' : v.gpr .t1 = off B (arr w X + 8 * n) - BitVec.ofNat 64 8 := by
      rw [v1, BitVec.sub_sub, ← BitVec.ofNat_add, off_sub B (show 8 + 8 * 2 ^ j ≤ arr w X + 8 * w by omega_using [hlt]),
        off_sub B (show 8 ≤ arr w X + 8 * n by omega_using [hbit, fit, nw, hSz, hwl, hw0, hpj, hpj0, hXa, hhdr, hlt, al, hn])]
      congr 1; omega_using [hlt, hn]
    -- The moves, from the top: word `2^j + i` := word `i` if the bit is set.
    rw [stageBody, WP.seq_iff]
    refine WP.mono (moveDown_ok (b := decide (r / 2 ^ (b + j) % 2 = 1)) (P := 2 ^ j) (n := n) hv.scr v0'
      v1' v5 (by simpa using v4) (by omega_using [hlt, hn]) (by omega_using [hwl, hpj0, hn]) (by omega_using [hpj0]) al (by omega_using [hXa, hhdr]) (by omega_using [hr, hbit, fit, nw, hSz, hwl, hw0, hpj, hpj0, hXa, hhdr, hlt, al, hn]))
      fun t₁ ⟨l0, lv, lo, lk⟩ => ?_
    rw [hvm] at lv lo
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.a3, .t5] (Q := fun t₂ => t₂.gpr .a3 =
        (if decide (r / 2 ^ (b + j) % 2 = 1) then BitVec.allOnes 64 else 0) ^^^ -1#64 ∧
        t₂.gpr .t5 = BitVec.ofNat 64 (2 ^ j) ∧ t₂.mem = t₁.mem) (by
      have l4 : t₁.gpr .t4 = if decide (r / 2 ^ (b + j) % 2 = 1) then BitVec.allOnes 64 else 0 := by
        rw [lk.gpr (by decide)]; simpa using v4
      have l3 : t₁.gpr .t3 = BitVec.ofNat 64 (2 ^ j) := by rw [lk.gpr (by decide)]; exact v3
      brun [mov, l4, l3, BitVec.add_zero]) (by rfl) (by rfl)) fun t₂ ⟨⟨m3, m5, mm⟩, mk⟩ => ?_
    have l0' : t₂.gpr .t0 = off B (arr w X + 8 * 2 ^ j) - BitVec.ofNat 64 8 := by rw [mk.gpr (by decide)]; exact l0
    refine WP.mono (clearDown_ok (hv.scr.congr (lk.trans mk).2.2) l0' m5 m3 (by omega_using [hpj0]) (by omega_using [hpj]) al (by omega_using [hXa, hhdr])
      (by omega_using [hr, hbit, fit, nw, hSz, hwl, hw0, hpj, hpj0, hXa, hhdr, hlt, al, hn])) fun t ⟨cv, co, ck⟩ => ?_
    rw [mm] at co cv
    have kk : Keep stRegs s t := (((kv.trans lk).trans mk).trans ck).mono (by decide)
    refine ⟨h.of_keep kk, ?_, ?_, kk⟩
    · exact Frame.of_arr (o := X) (d := 0) (n := 8 * w) (by
        have := (lo.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [hlt, hn])).trans
          ((co.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [hlt])))
        simpa using this) (by omega_using [hSz]) (by simp)
    · -- `w = 2^j + n` words: the cleared ones, then the moved ones.
      have e := wordsVal_append t.mem B (arr w X) (2 ^ j) n
      rw [show 2 ^ j + n = w by omega_using [hlt, hn]] at e
      rw [e, cv, Outside.wordsVal co (by omega_using []) (by omega_using [hr, hbit, fit, nw, hSz, hwl, hw0, hpj, hpj0, hXa, hhdr, hlt, al, hn]), lv]
      have e2 := wordsVal_append s.mem B (arr w X) n (2 ^ j)
      rw [show n + 2 ^ j = w by omega_using [hlt, hn]] at e2
      by_cases hb : r / 2 ^ (b + j) % 2 = 1
      · simp only [hb, decide_true, ite_true, Nat.zero_add]
        have hw : 2 ^ (64 * w) = 2 ^ (64 * n) * 2 ^ (64 * 2 ^ j) := by rw [← Nat.pow_add]; congr 1; omega_using [hlt, hn]
        rw [e2, hw, Nat.mul_mod_mul_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _),
          Nat.mul_comm]
      · simp only [hb, decide_false, Bool.false_eq_true, ite_false]
        have e3 := wordsVal_append s.mem B (arr w X) (2 ^ j) n
        rw [show 2 ^ j + n = w by omega_using [hlt, hn]] at e3
        rw [e3, Outside.wordsVal lo (by omega_using []) (by omega_using [hr, hbit, fit, nw, hSz, hwl, hw0, hpj, hpj0, hXa, hhdr, hlt, al, hn, hb])]

/-- `shlStages X R b k`, the count `r` in `R`, `⌊r / 2^b⌋ < w`:
`[X] := [X] 2^(64 (⌊r / 2^b⌋ mod 2^k)) mod 2^(64 w)`. -/
theorem shlStages_ok {s : State} {B : Addr} {Z w N X : Nat} {R : Reg} {r b K : Nat} (h : Ws s B Z w N)
    (hX : X < N) (hN : N ≤ 2048) (hR : s.gpr R = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) (hRr : R ∉ stRegs)
    (hb : b + K ≤ 64) (hK : K ≤ 11) (hc : r / 2 ^ b < w) : ∀ k ≤ K,
    WP isa (shlStages X R b k) s fun t => Ws t B Z w N ∧ Frame B w [X] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w X) w =
        wordsVal s.mem B (arr w X) w * 2 ^ (64 * (r / 2 ^ b % 2 ^ k)) % 2 ^ (64 * w) ∧ Keep stRegs s t
  | 0, _ => by
    refine WP.block_nil_iff.mpr ⟨h, Frame.refl _ _ _ _ _, ?_, Keep.refl _ _⟩
    rw [Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]
  | k + 1, hk => by
    rw [shlStages]
    refine WP.seq (WP.mono (shlStages_ok h hX hN hR hr hRr hb hK hc k (by omega_using [hk])) fun u ⟨hu, fu, vu, ku⟩ => ?_)
    have uR : u.gpr R = BitVec.ofNat 64 r := (ku.gpr hRr).trans hR
    refine WP.mono (shlStage_ok (j := k) hu hX hN uR hr hRr (by omega_using [hK, hk]) (by omega_using [hb, hk]) fun hw => ?_)
      fun t ⟨ht, ft, vt, kt⟩ => ⟨ht, fu.trans ft, ?_, (ku.trans kt).mono (by decide)⟩
    · rw [bit_shift, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hc hw)]
    · rw [vt, vu, VG.Proof.Bignum.ShiftStages.mod_two_pow_succ, ← bit_shift]
      split
      · rename_i hbit
        rw [hbit, Nat.one_mul, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, Nat.mul_add]
      · rename_i hbit
        rw [show r / 2 ^ (b + k) % 2 = 0 by omega_using [hbit], Nat.zero_mul, Nat.add_zero]

/-! ## The bits -/

/-- The loop of `shrBy`'s bits: `n` words from `dX`, word `i` := word `i` of
`⌊Y / 2^sh⌋` for `Y` the `n + 1` words there, from its words `i` and `i + 1`. -/
theorem shrBitsLoop_ok {s : State} {B : Addr} {Z dX n sh : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dX) (h5 : s.gpr .t5 = BitVec.ofNat 64 n) (ha5 : (s.gpr .a5).toNat % 64 = sh)
    (ha6 : (s.gpr .a6).toNat % 64 = 63 - sh) (hsh : sh < 64) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hX8 : dX % 8 = 0) (hZ : dX + 8 * (n + 1) ≤ Z) :
    WP isa (countLoop .t5 [.load .d .a7 .t0 0, .load .d .a3 .t0 8, .shiftReg .srl .d .a7 .a7 .a5,
        .shift .sll .d .a3 .a3 1, .shiftReg .sll .d .a3 .a3 .a6, .logic .or .a7 .a7 .a3, .store .d .a7 .t0 0,
        .addi .t0 .t0 8]) s fun t => t.gpr .t0 = off B (dX + 8 * n) ∧
      wordsVal t.mem B dX n = wordsVal s.mem B dX (n + 1) / 2 ^ sh % 2 ^ (64 * n) ∧
      Outside B dX (8 * n) s.mem t.mem ∧ Keep [.t0, .t5, .a7, .a3] s t := by
  have hnw := hs.nowrap
  generalize hY : wordsVal s.mem B dX (n + 1) = Y
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dX + 8 * i) ∧ Outside B dX (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dX i = Y / 2 ^ sh % 2 ^ (64 * i) ∧ Keep [.t0, .t5, .a7, .a3] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨j0, jout, jeq, jk⟩ _ => ?_)
    ⟨by rw [h0]; rfl, Outside.refl _ _ _ _, by simp [wordsVal, Nat.mod_one], Keep.refl _ _⟩ h5)
    fun t ⟨t0, tout, teq, tk⟩ => ⟨t0, teq, tout, tk⟩
  have hs' := hs.congr jk.2.2
  have j5 : (t.gpr .a5).toNat % 64 = sh := by rw [jk.gpr (by decide)]; exact ha5
  have j6 : (t.gpr .a6).toNat % 64 = 63 - sh := by rw [jk.gpr (by decide)]; exact ha6
  have wa : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega_using []) (by omega_using [hZ, hnw, hi])
  have wb : word t.mem B (dX + 8 * i + 8) = word s.mem B (dX + 8 * (i + 1)) := by
    rw [show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega_using []]; exact jout.word (by omega_using []) (by omega_using [hZ, hnw, hi])
  refine WP.mono (WP.keep [.t0, .t5, .a7, .a3] (Q := fun t' =>
      t'.gpr .t0 = off B (dX + 8 * i + 8) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dX + 8 * i))
          ((word t.mem B (dX + 8 * i) >>> ((t.gpr .a5).toNat % 64)) |||
            ((word t.mem B (dX + 8 * i + 8) <<< 1) <<< ((t.gpr .a6).toNat % 64)))) (by
    brun [j0, BitVec.add_zero, exec_addi_nat (show 8 < 2048 by decide), exec_srlReg, exec_sllReg,
      exec_sll_imm (show 1 < 64 by decide),
      hs'.ld (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi]) (by omega_using [hX8]),
      hs'.ld (show dX + 8 * i + 8 + 8 ≤ Z by omega_using [hZ, hi]), hs'.al8 (show dX + 8 * i + 8 + 8 ≤ Z by omega_using [hZ, hi]) (by omega_using [hX8]),
      hs'.st (show dX + 8 * i + 8 ≤ Z by omega_using [hZ, hi])]) (by rfl) (by rfl))
    fun t' ⟨⟨l0, l5, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans lk |>.mono (by decide)⟩, l5⟩
  · rw [l0, show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega_using []]
  · rw [lm]; exact out_step _ jout (by omega_using [hZ, hnw, hi])
  · rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_using [hZ, hnw, hi]), jeq, j5, j6, wa, wb, window_val _ _ hsh,
      ← wordsVal_word (m := s.mem) (base := B) (o := dX) (n := n + 1) (j := i) (by omega_using [hi]),
      ← wordsVal_word (m := s.mem) (base := B) (o := dX) (n := n + 1) (j := i + 1) (by omega_using [hi]), hY,
      ← VG.Proof.Bignum.WordStep.shr_words _ _ hsh, mod_succ_words, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      Nat.add_comm sh]

/-- The registers `shrBy` and `shlBy` write. -/
abbrev shRegs : List Reg := [.t0, .t1, .t3, .t4, .t5, .a7, .a3, .a4, .a5, .a6]

/-- `shrBy X R`, the count `r < 2^13` in `R`, `⌊r / 64⌋ < w`, `2 ≤ w`:
`[X] := ⌊[X] / 2^r⌋` (its `w` words). -/
theorem shrBy_ok {s : State} {B : Addr} {Z w N X : Nat} {R : Reg} {r : Nat} (h : Ws s B Z w N)
    (hX : X < N) (hN : N ≤ 2048) (hR : s.gpr R = BitVec.ofNat 64 r) {n : Nat} (hn : n ≤ 11) (hr : r < 2 ^ (6 + n))
    (hRr : R ∉ shRegs) (hw : 2 ≤ w) (hc : r / 64 < w) :
    WP isa (shrBy X R n) s fun t => Ws t B Z w N ∧ Frame B w [X] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w X) w = wordsVal s.mem B (arr w X) w / 2 ^ r ∧ Keep shRegs s t := by
  have fit := h.arr_fit hX
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have al := arr_al w X
  have hRs : R ∉ stRegs := by
    intro e; apply hRr
    simp only [stRegs, List.mem_cons, List.not_mem_nil, or_false] at e
    simp only [shRegs, List.mem_cons, List.not_mem_nil, or_false]
    rcases e with e | e | e | e | e | e | e | e <;> simp [e]
  -- The words.
  have hr64 : r < 2 ^ 64 := Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega_using [hn]))
  refine WP.seq (WP.mono (shrStages_ok h hX hN hR hr64 hRs (by omega_using [hn]) hn
    (by rw [show (2 : Nat) ^ 6 = 64 from rfl]; exact hc) n (Nat.le_refl _)) fun u ⟨hu, fu, vu, ku⟩ => ?_)
  rw [show r / 2 ^ 6 % 2 ^ n = r / 64 by
    rw [show (2 : Nat) ^ 6 = 64 from rfl]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [Nat.pow_add] at hr; omega_using [hr]))] at vu
  have uR : u.gpr R = BitVec.ofNat 64 r := (ku.gpr hRs).trans hR
  -- The bits.
  rw [WP.seq_iff]
  refine ptr_ok hu (by decide) (by decide) (show X < 2048 by omega_using [hX, hN]) ?_
  obtain ⟨sh1, sh2⟩ := shifts_val r (by omega_using [hr64])
  refine WP.mono (WP.keep [.a5, .a6, .t5] (Q := fun v => v.gpr .a5 = BitVec.ofNat 64 r &&& BitVec.ofNat 64 63 ∧
      v.gpr .a6 = BitVec.ofNat 64 r &&& BitVec.ofNat 64 63 ^^^ BitVec.ofNat 64 63 ∧
      v.gpr .t5 = BitVec.ofNat 64 (w - 1) ∧ v.mem = u.mem) (by
    brun [hu.s9, bv_sub_lit (show w < 2 ^ 64 by omega_using [hwl]) (show 1 ≤ w by omega_using [hw])]
    rw [ite_eq_right (fun e => hRr (by rw [e]; decide)), uR]
    exact ⟨rfl, rfl⟩) (by rfl) (by rfl)) fun v ⟨⟨v5, v6, vt5, vm⟩, vk⟩ => ?_
  have v0 : v.gpr .t0 = off B (arr w X) := by rw [vk.gpr (by decide)]; simp [gpr_write]
  have hv := hu.of_keep ((Keep.write _ _ _).trans vk |>.mono (rs' := [.t0, .a5, .a6, .t5]) (by decide))
  rw [← v5] at sh1; rw [← v6] at sh2
  generalize hY : wordsVal u.mem B (arr w X) w = Y at vu
  rw [WP.seq_iff]
  refine WP.mono (shrBitsLoop_ok (n := w - 1) (sh := r % 64) hv.scr v0 vt5 sh1 (by rw [sh2]) (by omega_using []) (by omega_using [hw])
    (by omega_using [hwl]) al (by omega_using [fit, hSz])) fun t₁ ⟨l0, lv, lo, lk⟩ => ?_
  rw [show w - 1 + 1 = w by omega_using [hw], vm, hY] at lv
  rw [vm] at lo
  have hs₁ := hv.scr.congr lk.2.2
  have l5 : (t₁.gpr .a5).toNat % 64 = r % 64 := by rw [lk.gpr (by decide)]; exact sh1
  refine WP.mono (WP.keep [.a7] (Q := fun t => t.mem = t₁.mem.writeW (off B (arr w X + 8 * (w - 1)))
      (word t₁.mem B (arr w X + 8 * (w - 1)) >>> ((t₁.gpr .a5).toNat % 64))) (by
    brun [l0, BitVec.add_zero, exec_srlReg, hs₁.ld (show arr w X + 8 * (w - 1) + 8 ≤ Z by omega_using [fit, hSz]),
      hs₁.al8 (show arr w X + 8 * (w - 1) + 8 ≤ Z by omega_using [fit, hSz]) (by omega_using [al]),
      hs₁.st (show arr w X + 8 * (w - 1) + 8 ≤ Z by omega_using [fit, hSz])]) (by rfl) (by rfl)) fun t ⟨tm, tk⟩ => ?_
  have kk : Keep shRegs s t := ((((ku.trans ((Keep.write _ _ _).trans vk)).trans lk).trans tk)).mono (by decide)
  have o1 := writeW_outside t₁.mem B (d := arr w X + 8 * (w - 1))
    (word t₁.mem B (arr w X + 8 * (w - 1)) >>> ((t₁.gpr .a5).toNat % 64)) (by omega_using [fit, nw, hSz])
  rw [← tm] at o1
  refine ⟨h.of_keep kk, fu.trans ?_, ?_, kk⟩
  · exact Frame.of_arr (o := X) (d := 0) (n := 8 * w) (by
      have := (lo.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [])).trans
        (o1.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [hw]))
      simpa using this) (by omega_using [hSz]) (by simp)
  · -- The top word `⌊Y_{w-1} / 2^sh⌋`, and the low words.
    have wt : word t₁.mem B (arr w X + 8 * (w - 1)) = word u.mem B (arr w X + 8 * (w - 1)) :=
      lo.word (by omega_using []) (by omega_using [fit, nw, hSz])
    have hYl : Y < 2 ^ (64 * w) := hY ▸ wordsVal_lt _ _ _ _
    have e := fin64_wordsVal_write_top t₁.mem B (arr w X) (w - 1)
      (word t₁.mem B (arr w X + 8 * (w - 1)) >>> ((t₁.gpr .a5).toNat % 64)) (by omega_using [fit, nw, hSz])
    rw [← tm, show w - 1 + 1 = w by omega_using [hw]] at e
    rw [e, lv, l5, wt, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      ← wordsVal_word (m := u.mem) (base := B) (o := arr w X) (n := w) (j := w - 1) (by omega_using [hw]), hY,
      Nat.mod_eq_of_lt (show Y / 2 ^ (64 * (w - 1)) < 2 ^ 64 by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
        exact Nat.lt_of_lt_of_le hYl (Nat.pow_le_pow_right (by decide) (by omega_using []))),
      show Y / 2 ^ (64 * (w - 1)) / 2 ^ (r % 64) = Y / 2 ^ (r % 64) / 2 ^ (64 * (w - 1)) by
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm],
      Nat.mod_add_div, vu, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * (r / 64) + r % 64 = r by omega_using []]

/-- A word of a shift up by `sh < 64` bits, from it and the word below. -/
theorem orShl (x y : BitVec 64) {sh : Nat} (hsh : sh < 64) :
    ((x <<< sh) ||| ((y >>> 1) >>> (63 - sh))).toNat = x.toNat * 2 ^ sh % 2 ^ 64 + y.toNat / 2 ^ (64 - sh) := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - sh) * 2 ^ sh := by rw [← Nat.pow_add]; congr 1; omega_using [hsh]
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 1 + (63 - sh) = 64 - sh by omega_using [hsh], e64, Nat.mul_mod_mul_right]
  have hlt : y.toNat / 2 ^ (64 - sh) < 2 ^ sh := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e64]; exact y.isLt
  rw [Nat.mul_comm (x.toNat % _), ← Nat.two_pow_add_eq_or_of_lt hlt]

/-- Word `k ≥ 1` of `Y 2^sh`, from words `k` and `k - 1` of `Y`. -/
theorem shl_word (Y k : Nat) {sh : Nat} (hk : 1 ≤ k) (hsh : sh < 64) :
    Y * 2 ^ sh / 2 ^ (64 * k) % 2 ^ 64 =
      Y / 2 ^ (64 * k) % 2 ^ 64 * 2 ^ sh % 2 ^ 64 + Y / 2 ^ (64 * (k - 1)) % 2 ^ 64 / 2 ^ (64 - sh) := by
  rcases Nat.eq_zero_or_pos sh with rfl | hs0
  · rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.mod_mod, Nat.sub_zero,
      Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.add_zero]
  · have e : Y * 2 ^ sh / 2 ^ (64 * k) = Y / 2 ^ (64 * (k - 1) + (64 - sh)) := by
      rw [show 64 * k = sh + (64 * (k - 1) + (64 - sh)) by omega_using [hk, hsh], Nat.pow_add, Nat.mul_comm Y,
        Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
    rw [e, VG.Proof.Bignum.WordStep.shr_words _ _ (by omega_using [hs0]), show k - 1 + 1 = k by omega_using [hk],
      show (2 : Nat) ^ 64 = 2 ^ (64 - (64 - sh)) * 2 ^ (64 - sh) by rw [← Nat.pow_add]; congr 1; omega_using [],
      show 64 - (64 - sh) = sh by omega_using [hsh], Nat.mul_comm (2 ^ sh) (2 ^ (64 - sh)), Nat.mul_mod_mul_right]
    omega_using []

/-- A word below the top of a number reduced modulo `2^M`. -/
theorem mod_word {a M K : Nat} (h : K + 64 ≤ M) : a % 2 ^ M / 2 ^ K % 2 ^ 64 = a / 2 ^ K % 2 ^ 64 := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self a, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

theorem wordsVal_pos {m : Mem} {B : Addr} {d n : Nat} (h : 1 ≤ n) :
    wordsVal m B d n = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_using [h]⟩
  rfl

/-- The loop of `shlBy`'s bits: from the top, word `k ≥ 1` of `n + 1` words
`Y` at `dX` := word `k` of `Z = Y 2^sh mod 2^(64 (n + 1))`, from words `k` and
`k - 1`. -/
theorem shlBitsLoop_ok {s : State} {B : Addr} {Z dX n sh : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B (dX + 8 * (n + 1)) - BitVec.ofNat 64 8)
    (h1 : s.gpr .t1 = off B (dX + 8 * n) - BitVec.ofNat 64 8) (h5 : s.gpr .t5 = BitVec.ofNat 64 n)
    (ha5 : (s.gpr .a5).toNat % 64 = sh) (ha6 : (s.gpr .a6).toNat % 64 = 63 - sh) (hsh : sh < 64) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 32) (hX8 : dX % 8 = 0) (hX : 8 ≤ dX) (hZ : dX + 8 * (n + 1) ≤ Z) :
    WP isa (countLoop .t5 [.load .d .a7 .t0 0, .load .d .a3 .t1 0, .shiftReg .sll .d .a7 .a7 .a5,
        .shift .srl .d .a3 .a3 1, .shiftReg .srl .d .a3 .a3 .a6, .logic .or .a7 .a7 .a3, .store .d .a7 .t0 0,
        .addi .t0 .t0 (-8), .addi .t1 .t1 (-8)]) s fun t => t.gpr .t0 = off B (dX + 8) - BitVec.ofNat 64 8 ∧
      wordsVal t.mem B (dX + 8) n = wordsVal s.mem B dX (n + 1) * 2 ^ sh % 2 ^ (64 * (n + 1)) / 2 ^ 64 ∧
      Outside B (dX + 8) (8 * n) s.mem t.mem ∧ Keep [.t0, .t1, .t5, .a7, .a3] s t := by
  have hnw := hs.nowrap
  generalize hY : wordsVal s.mem B dX (n + 1) = Y
  have hYl : Y < 2 ^ (64 * (n + 1)) := hY ▸ wordsVal_lt _ _ _ _
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dX + 8 * (n + 1 - i)) - BitVec.ofNat 64 8 ∧
      t.gpr .t1 = off B (dX + 8 * (n - i)) - BitVec.ofNat 64 8 ∧
      Outside B (dX + 8 * (n + 1 - i)) (8 * i) s.mem t.mem ∧
      wordsVal t.mem B (dX + 8 * (n + 1 - i)) i = Y * 2 ^ sh % 2 ^ (64 * (n + 1)) / 2 ^ (64 * (n + 1 - i)) ∧
      Keep [.t0, .t1, .t5, .a7, .a3] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ _ => ?_)
    ⟨by rw [h0, Nat.sub_zero], by rw [h1, Nat.sub_zero], Outside.refl _ _ _ _, ?_, Keep.refl _ _⟩ h5)
    fun t ⟨t0, _, tout, teq, tk⟩ => ⟨by rw [t0, show n + 1 - n = 1 by omega_using [], Nat.mul_one],
      by rw [show n + 1 - n = 1 by omega_using [], Nat.mul_one] at teq tout; exact teq, by
        rw [show n + 1 - n = 1 by omega_using [], Nat.mul_one] at tout; exact tout, tk⟩
  rotate_left
  · rw [Nat.sub_zero, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))]; rfl
  have hs' := hs.congr jk.2.2
  have j5 : (t.gpr .a5).toNat % 64 = sh := by rw [jk.gpr (by decide)]; exact ha5
  have j6 : (t.gpr .a6).toNat % 64 = 63 - sh := by rw [jk.gpr (by decide)]; exact ha6
  generalize hk : n - i = k
  have e0 : t.gpr .t0 = off B (dX + 8 * k) := by
    rw [j0, off_sub B (show 8 ≤ dX + 8 * (n + 1 - i) by omega_using [hX])]; congr 1; omega_using [hi, hk]
  have e1 : t.gpr .t1 = off B (dX + 8 * (k - 1)) := by
    rw [j1, off_sub B (show 8 ≤ dX + 8 * (n - i) by omega_using [hX])]; congr 1; omega_using [hi, hk]
  have wa : word t.mem B (dX + 8 * k) = word s.mem B (dX + 8 * k) := jout.word (by omega_using [hi, hk]) (by omega_using [hZ, hnw, hk])
  have wb : word t.mem B (dX + 8 * (k - 1)) = word s.mem B (dX + 8 * (k - 1)) := jout.word (by omega_using [hi, hk]) (by omega_using [hZ, hnw, hk])
  refine WP.mono (WP.keep [.t0, .t1, .t5, .a7, .a3] (Q := fun t' =>
      t'.gpr .t0 = off B (dX + 8 * k) - BitVec.ofNat 64 8 ∧
        t'.gpr .t1 = off B (dX + 8 * (k - 1)) - BitVec.ofNat 64 8 ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dX + 8 * k))
          ((word t.mem B (dX + 8 * k) <<< ((t.gpr .a5).toNat % 64)) |||
            ((word t.mem B (dX + 8 * (k - 1)) >>> 1) >>> ((t.gpr .a6).toNat % 64)))) (by
    brun [e0, e1, BitVec.add_zero, exec_srlReg, exec_sllReg, exec_srl_imm (show 1 < 64 by decide),
      hs'.ld (show dX + 8 * k + 8 ≤ Z by omega_using [hZ, hk]), hs'.al8 (show dX + 8 * k + 8 ≤ Z by omega_using [hZ, hk]) (by omega_using [hX8]),
      hs'.ld (show dX + 8 * (k - 1) + 8 ≤ Z by omega_using [hZ, hk]), hs'.al8 (show dX + 8 * (k - 1) + 8 ≤ Z by omega_using [hZ, hk]) (by omega_using [hX8]),
      hs'.st (show dX + 8 * k + 8 ≤ Z by omega_using [hZ, hk])]) (by rfl) (by rfl))
    fun t' ⟨⟨l0, l1, l5, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans lk |>.mono (by decide)⟩, l5⟩
  · rw [l0, show dX + 8 * k = dX + 8 * (n + 1 - (i + 1)) by omega_using [hk]]
  · rw [l1, show dX + 8 * (k - 1) = dX + 8 * (n - (i + 1)) by omega_using [hk]]
  · rw [lm, show dX + 8 * (n + 1 - (i + 1)) = dX + 8 * k by omega_using [hk]]
    exact ((jout.mono (o' := dX + 8 * k) (n' := 8 * (i + 1)) (by omega_using [hk]) (by omega_using [hk]))).trans
      ((writeW_outside _ B (d := dX + 8 * k) _ (by omega_using [hZ, hnw, hk])).mono (by omega_using []) (by omega_using []))
  · have o1 := writeW_outside t.mem B (d := dX + 8 * k)
      ((word t.mem B (dX + 8 * k) <<< ((t.gpr .a5).toNat % 64)) |||
        ((word t.mem B (dX + 8 * (k - 1)) >>> 1) >>> ((t.gpr .a6).toNat % 64))) (by omega_using [hZ, hnw, hk])
    rw [lm, show dX + 8 * (n + 1 - (i + 1)) = dX + 8 * k by omega_using [hk]]
    simp only [wordsVal]
    rw [word_writeW_self, o1.wordsVal (by omega_using []) (by omega_using [hZ, hnw, hi, hk]), show dX + 8 * k + 8 = dX + 8 * (n + 1 - i) by omega_using [hi, hk],
      jeq, j5, j6, wa, wb, orShl _ _ hsh,
      ← wordsVal_word (m := s.mem) (base := B) (o := dX) (n := n + 1) (j := k) (by omega_using [hk]),
      ← wordsVal_word (m := s.mem) (base := B) (o := dX) (n := n + 1) (j := k - 1) (by omega_using [hk]), hY,
      ← shl_word Y k (by omega_using [hi, hk]) hsh, ← mod_word (M := 64 * (n + 1)) (by omega_using [hk]),
      show n + 1 - i = k + 1 by omega_using [hi, hk], show n + 1 - (i + 1) = k by omega_using [hk], show 64 * (k + 1) = 64 * k + 64 by omega_using [],
      Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact Nat.mod_add_div _ _

/-- `shlBy X R`, the count `r < 2^13` in `R`, `⌊r / 64⌋ < w`, `2 ≤ w`:
`[X] := [X] 2^r mod 2^(64 w)` (its `w` words). -/
theorem shlBy_ok {s : State} {B : Addr} {Z w N X : Nat} {R : Reg} {r : Nat} (h : Ws s B Z w N)
    (hX : X < N) (hN : N ≤ 2048) (hR : s.gpr R = BitVec.ofNat 64 r) {n : Nat} (hn : n ≤ 11) (hr : r < 2 ^ (6 + n))
    (hRr : R ∉ shRegs) (hw : 2 ≤ w) (hc : r / 64 < w) :
    WP isa (shlBy X R n) s fun t => Ws t B Z w N ∧ Frame B w [X] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w X) w = wordsVal s.mem B (arr w X) w * 2 ^ r % 2 ^ (64 * w) ∧ Keep shRegs s t := by
  have fit := h.arr_fit hX
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have al := arr_al w X
  have hXa := hdr_le_arr w X
  have hhdr : hdr = 256 := rfl
  have hRs : R ∉ stRegs := by
    intro e; apply hRr
    simp only [stRegs, List.mem_cons, List.not_mem_nil, or_false] at e
    simp only [shRegs, List.mem_cons, List.not_mem_nil, or_false]
    rcases e with e | e | e | e | e | e | e | e <;> simp [e]
  -- The words.
  have hr64 : r < 2 ^ 64 := Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega_using [hn]))
  refine WP.seq (WP.mono (shlStages_ok h hX hN hR hr64 hRs (by omega_using [hn]) hn
    (by rw [show (2 : Nat) ^ 6 = 64 from rfl]; exact hc) n (Nat.le_refl _)) fun u ⟨hu, fu, vu, ku⟩ => ?_)
  rw [show r / 2 ^ 6 % 2 ^ n = r / 64 by
    rw [show (2 : Nat) ^ 6 = 64 from rfl]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [Nat.pow_add] at hr; omega_using [hr]))] at vu
  have uR : u.gpr R = BitVec.ofNat 64 r := (ku.gpr hRs).trans hR
  -- The bits.
  rw [WP.seq_iff]
  refine ptr_ok hu (by decide) (by decide) (show X < 2048 by omega_using [hX, hN]) ?_
  obtain ⟨sh1, sh2⟩ := shifts_val r (by omega_using [hr64])
  refine WP.mono (WP.keep [.t0, .a5, .a6, .t5, .t1] (Q := fun v =>
      v.gpr .t0 = off B (arr w X + 8 * w) - BitVec.ofNat 64 8 ∧
      v.gpr .a5 = BitVec.ofNat 64 r &&& BitVec.ofNat 64 63 ∧
      v.gpr .a6 = BitVec.ofNat 64 r &&& BitVec.ofNat 64 63 ^^^ BitVec.ofNat 64 63 ∧
      v.gpr .t5 = BitVec.ofNat 64 (w - 1) ∧
      v.gpr .t1 = off B (arr w X + 8 * w) - BitVec.ofNat 64 8 - BitVec.ofNat 64 8 ∧ v.mem = u.mem) (by
    have hR0 : (R = Reg.t0) = False := eq_false (fun e => hRr (by rw [e]; decide))
    have hR5 : (R = Reg.t5) = False := eq_false (fun e => hRr (by rw [e]; decide))
    brun [hu.s9, shl3_ofNat, off_add, bv_sub_lit (show w < 2 ^ 64 by omega_using [hwl]) (show 1 ≤ w by omega_using [hw]), hR0, hR5, uR]
    ) (by rfl) (by rfl)) fun v ⟨⟨v0, v5, v6, vt5, v1, vm⟩, vk⟩ => ?_
  have hv := hu.of_keep ((Keep.write _ _ _).trans vk |>.mono (rs' := [.t0, .a5, .a6, .t5, .t1]) (by decide))
  rw [← v5] at sh1; rw [← v6] at sh2
  generalize hY : wordsVal u.mem B (arr w X) w = Y at vu
  have v0' : v.gpr .t0 = off B (arr w X + 8 * (w - 1 + 1)) - BitVec.ofNat 64 8 := by
    rw [v0, show w - 1 + 1 = w by omega_using [hw]]
  have v1' : v.gpr .t1 = off B (arr w X + 8 * (w - 1)) - BitVec.ofNat 64 8 := by
    rw [v1, off_sub B (show 8 ≤ arr w X + 8 * w by omega_using [hw]), off_sub B (show 8 ≤ arr w X + 8 * w - 8 by omega_using [hw]),
      off_sub B (show 8 ≤ arr w X + 8 * (w - 1) by omega_using [hw])]
    congr 1; omega_using [hw]
  rw [WP.seq_iff]
  refine WP.mono (shlBitsLoop_ok (n := w - 1) (sh := r % 64) hv.scr v0' v1' vt5 sh1 (by rw [sh2]) (by omega_using [])
    (by omega_using [hw]) (by omega_using [hwl]) al (by omega_using [hXa, hhdr]) (by omega_using [hr, hw, hc, fit, nw, hSz, hwl, al, hXa, hhdr, hr64, sh2, sh1])) fun t₁ ⟨l0, lv, lo, lk⟩ => ?_
  rw [show w - 1 + 1 = w by omega_using [hw], vm, hY] at lv
  rw [vm] at lo
  have hs₁ := hv.scr.congr lk.2.2
  have l5 : (t₁.gpr .a5).toNat % 64 = r % 64 := by rw [lk.gpr (by decide)]; exact sh1
  have l0' : t₁.gpr .t0 = off B (arr w X) := by
    rw [l0, off_sub B (show 8 ≤ arr w X + 8 by omega_using []), Nat.add_sub_cancel]
  refine WP.mono (WP.keep [.a7] (Q := fun t => t.mem = t₁.mem.writeW (off B (arr w X))
      (word t₁.mem B (arr w X) <<< ((t₁.gpr .a5).toNat % 64))) (by
    brun [l0', BitVec.add_zero, exec_sllReg, hs₁.ld (show arr w X + 8 ≤ Z by omega_using [fit, hSz]),
      hs₁.al8 (show arr w X + 8 ≤ Z by omega_using [fit, hSz]) al, hs₁.st (show arr w X + 8 ≤ Z by omega_using [fit, hSz])]) (by rfl) (by rfl))
    fun t ⟨tm, tk⟩ => ?_
  have kk : Keep shRegs s t := ((((ku.trans ((Keep.write _ _ _).trans vk)).trans lk).trans tk)).mono (by decide)
  have o1 := writeW_outside t₁.mem B (d := arr w X) (word t₁.mem B (arr w X) <<< ((t₁.gpr .a5).toNat % 64))
    (by omega_using [fit, nw, hSz])
  rw [← tm] at o1
  refine ⟨h.of_keep kk, fu.trans ?_, ?_, kk⟩
  · exact Frame.of_arr (o := X) (d := 0) (n := 8 * w) (by
      have := (lo.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [hw])).trans
        (o1.mono (o' := arr w X) (n' := 8 * w) (by omega_using []) (by omega_using [hw]))
      simpa using this) (by omega_using [hSz]) (by simp)
  · -- The bottom word `Y_0 2^sh mod 2^64`, and the words above.
    have wt : word t₁.mem B (arr w X) = word u.mem B (arr w X) := lo.word (by omega_using []) (by omega_using [fit, nw, hSz])
    have w0 := wordsVal_word (m := u.mem) (base := B) (o := arr w X) (n := w) (j := 0) (by omega_using [hw])
    simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one] at w0
    rw [wordsVal_pos (show 1 ≤ w by omega_using [hw]), tm, word_writeW_self,
      (writeW_outside t₁.mem B (d := arr w X) _ (by omega_using [fit, nw, hSz])).wordsVal (by omega_using []) (by omega_using [hr, hw, hc, fit, nw, hSz, hwl, al, hXa, hhdr, hr64, sh2, sh1, l5]), lv, l5, wt,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ← w0, hY, Nat.mod_mul_mod,
      ← Nat.mod_mod_of_dvd (Y * 2 ^ (r % 64)) (Nat.pow_dvd_pow 2 (by omega_using [hw] : 64 ≤ 64 * w)), Nat.mod_add_div, vu,
      Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, show 64 * (r / 64) + r % 64 = r by omega_using []]

/-! ## Trailing zeros -/

open VG.Proof.Bignum.ShiftStages (tz dvd_iff tz_lt dvd_gcd_iff stage_tz greedy greedy_pows pows greedy_cons
  greedy_nil)

/-- The trailing zeros of `n ≠ 0` are the `T` that the powers of two dividing it reach. -/
theorem tz_eq_of {n T : Nat} (h0 : n ≠ 0) (h : ∀ s, 2 ^ s ∣ n ↔ s ≤ T) : tz n = T := by
  apply Nat.le_antisymm
  · exact (h _).mp ((dvd_iff h0 _).mpr (Nat.le_refl _))
  · exact (dvd_iff h0 _).mp ((h _).mpr (Nat.le_refl _))

/-- The trailing zeros of `a ∨ b`, for `a ≠ 0`, are those of `gcd(a, b)`. -/
theorem tz_or_gcd {a b : Nat} (ha : a ≠ 0) : tz (a ||| b) = tz (Nat.gcd a b) := by
  have hab : a ||| b ≠ 0 := fun e => ha (Nat.or_eq_zero_iff.mp e).1
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  refine tz_eq_of hab fun s => ?_
  rw [← dvd_iff hg, ← dvd_gcd_iff, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    Nat.or_mod_two_pow, Nat.or_eq_zero_iff]

/-- The trailing zeros of `V`, from its lowest nonzero word, word `i₀`. -/
theorem tz_words {V i₀ : Nat} (hlow : V % 2 ^ (64 * i₀) = 0) (hy : V / 2 ^ (64 * i₀) % 2 ^ 64 ≠ 0) :
    tz V = 64 * i₀ + tz (V / 2 ^ (64 * i₀) % 2 ^ 64) := by
  generalize hQ : V / 2 ^ (64 * i₀) = Q at hy
  have hV : V = 2 ^ (64 * i₀) * Q := by rw [← hQ]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)).symm
  have hV0 : V ≠ 0 := by intro e; rw [e] at hQ; rw [← hQ] at hy; simp at hy
  have hy0 := hy
  refine tz_eq_of hV0 fun s => ?_
  by_cases hs : s ≤ 64 * i₀
  · constructor
    · intro _; omega_using [hs]
    · intro _; rw [hV]; exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hs) (Nat.dvd_mul_right _ _)
  · obtain ⟨t, rfl⟩ : ∃ t, s = 64 * i₀ + t := ⟨s - 64 * i₀, by omega_using [hs]⟩
    rw [Nat.add_le_add_iff_left, ← dvd_iff hy0, hV, Nat.pow_add, Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos _)]
    by_cases ht : t ≤ 64
    · rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 ht)]
    · constructor
      · intro d; exfalso
        have : 2 ^ 64 ∣ Q := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega_using [ht])) d
        exact hy (Nat.mod_eq_zero_of_dvd this)
      · intro d; exfalso
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hy) d
        have : 2 ^ 64 < 2 ^ t := Nat.pow_lt_pow_right (by decide) (by omega_using [ht])
        have := Nat.mod_lt Q (Nat.two_pow_pos 64)
        omega_arith

/-- A stage's test of a word: its low `2^k` bits, shifted to the top. -/
theorem lowbits_zero (x : BitVec 64) {s : Nat} (hs : s ≤ 64) :
    (x <<< (64 - s)).toNat = x.toNat % 2 ^ s * 2 ^ (64 - s) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) by rw [← Nat.pow_add]; congr 1; omega_using [hs], Nat.mul_mod_mul_right]

/-- A stage's increment: `2^k` if the word's low `2^k` bits are zero, else 0. -/
theorem stage_inc (x : BitVec 64) {k : Nat} (hk : k ≤ 5) :
    (((if (0 : BitVec 64) < x <<< (64 - 2 ^ k) then 1 else 0) ^^^ 1#64) <<< k).toNat =
      if x.toNat % 2 ^ (2 ^ k) = 0 then 2 ^ k else 0 := by
  have h2k : 2 ^ k ≤ 32 := by
    calc 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hk
      _ = 32 := rfl
  have e := lowbits_zero x (s := 2 ^ k) (by omega_using [h2k])
  have hp := Nat.two_pow_pos (64 - 2 ^ k)
  have hlt : (0 : BitVec 64) < x <<< (64 - 2 ^ k) ↔ x.toNat % 2 ^ (2 ^ k) ≠ 0 := by
    rw [BitVec.lt_def, e, show (0 : BitVec 64).toNat = 0 from rfl]
    constructor
    · intro h z; rw [z, Nat.zero_mul] at h; omega_using [h]
    · intro h; exact Nat.mul_pos (Nat.pos_of_ne_zero h) hp
  by_cases z : x.toNat % 2 ^ (2 ^ k) = 0
  · rw [ite_eq_right (fun h => hlt.mp h z), ite_eq_left z]
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show ((0 : BitVec 64) ^^^ 1#64).toNat = 1 from rfl, Nat.one_mul,
      Nat.mod_eq_of_lt (by have : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega_using [hk]); omega_using [h2k])]
  · rw [ite_eq_left (hlt.mpr z), ite_eq_right z]
    rw [show ((1 : BitVec 64) ^^^ 1#64) = 0 from rfl, BitVec.toNat_shiftLeft]; simp

/-- The stages `ks` of the trailing zeros of a word `y ≠ 0`, from `acc` of them taken
(`a2`), `a3` the word shifted down by them, `a4` zero: `a2` the greedy count of the
stages `2^k`. -/
theorem tzStages_ok {s : State} {y : Nat} (hy : y ≠ 0) (hy64 : y < 2 ^ 64) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k ≤ 5) → ∀ acc, acc ≤ tz y → s.gpr .a2 = BitVec.ofNat 64 acc →
      s.gpr .a3 = BitVec.ofNat 64 (y / 2 ^ acc) → s.gpr .a4 = 0 →
      WP isa (.block (ks.flatMap tzStage)) s fun t => (t.gpr .a2 =
        BitVec.ofNat 64 (greedy (tz y) (ks.map (2 ^ ·)) acc) ∧ t.mem = s.mem) ∧ Keep [.t4, .t5, .a2, .a3] s t
  | [], _, acc, _, h2, _, _ => WP.block_nil_iff.mpr ⟨⟨h2, rfl⟩, Keep.refl _ _⟩
  | k :: ks, hks, acc, hacc, h2, h3, h4 => by
    have hk : k ≤ 5 := hks k (by simp)
    have hT := tz_lt (Nat.pos_of_ne_zero hy) hy64
    rw [List.flatMap_cons, WP.block_append_iff]
    generalize hz : (if y / 2 ^ acc % 2 ^ (2 ^ k) = 0 then 2 ^ k else 0) = c
    have hc : c ≤ 32 := by
      rw [← hz]; split
      · calc 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hk
          _ = 32 := rfl
      · omega_using []
    have hx : (BitVec.ofNat 64 (y / 2 ^ acc)).toNat = y / 2 ^ acc :=
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hy64)]
    have inc := stage_inc (BitVec.ofNat 64 (y / 2 ^ acc)) hk
    rw [hx, hz] at inc
    have hgr : (if acc + 2 ^ k ≤ tz y then acc + 2 ^ k else acc) = acc + c := by
      rw [← hz]; have := stage_tz hy hacc (2 ^ k); split <;> split <;> omega_arith
    refine WP.mono (WP.keep [.t4, .t5, .a2, .a3] (Q := fun u => u.gpr .a2 = BitVec.ofNat 64 (acc + c) ∧
        u.gpr .a3 = BitVec.ofNat 64 (y / 2 ^ (acc + c)) ∧ u.gpr .a4 = 0 ∧ u.mem = s.mem) (by
      unfold tzStage
      brun [h2, h3, h4, exec_sll_imm (show 64 - 2 ^ k < 64 by have := Nat.two_pow_pos k; omega_using [this]),
        exec_sll_imm (show k < 64 by omega_using [hk]), exec_srlReg]
      constructor
      · apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, inc, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega_using [hacc, hT]),
          Nat.mod_eq_of_lt (show acc + c < 2 ^ 64 by omega_using [hacc, hT, hc])]
      · apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, inc, Nat.shiftRight_eq_div_pow, hx, Nat.mod_eq_of_lt (show c < 64 by omega_using [hc]),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hy64), Nat.div_div_eq_div_mul,
          ← Nat.pow_add]) (by rfl) (by rfl)) fun u ⟨⟨u2, u3, u4, um⟩, uk⟩ => ?_
    refine WP.mono (tzStages_ok hy hy64 ks (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) (acc + c)
      (by rw [← hgr]; split <;> omega_arith) u2 u3 u4) fun t ⟨⟨t2, tm⟩, tk⟩ => ⟨⟨?_, by rw [tm, um]⟩, (uk.trans tk).mono (by decide)⟩
    rw [t2, List.map_cons, greedy_cons, hgr]

/-- What `tz`'s scan knows after `i` words of `f`: if a nonzero word was found,
the first, `j₀`, and its value `y`; else that none is. -/
def ScanI (f : Nat → BitVec 64) (i : Nat) (found : Bool) (j₀ : Nat) (y : BitVec 64) : Prop :=
  if found then j₀ < i ∧ f j₀ ≠ 0 ∧ (∀ j < j₀, f j = 0) ∧ y = f j₀ else (∀ j < i, f j = 0) ∧ j₀ = 0 ∧ y = 0

/-- A selection by a mask `0 - m`, `m` one or zero. -/
theorem selb (x h : BitVec 64) (b : Bool) :
    x ^^^ ((x ^^^ h) &&& (0 - (if b then 1 else 0))) = if b then h else x := by
  cases b
  · show x ^^^ ((x ^^^ h) &&& (0 - 0)) = x
    rw [show (0 : BitVec 64) - 0 = 0#64 from rfl, BitVec.and_zero, BitVec.xor_zero]
  · show x ^^^ ((x ^^^ h) &&& (0 - 1)) = h
    rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]

/-- The registers `tz`'s scan writes. -/
abbrev scanRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a7, .a3, .a5, .a6]

theorem bit_lt (x : BitVec 64) : ((if (0 : BitVec 64) < x then 1 else 0 : BitVec 64)) =
    if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · have hx : (0 : BitVec 64) < x := by
      rw [BitVec.lt_def]
      exact Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [ite_eq_left hx, ite_eq_right h]

/-- `countLoop .t3 tzScan` over `n` words at `dA` and `dB`: the first nonzero word of
`f j = [A]_j ∨ [B]_j`, its index into `a6` and its value into `a3`, `a5` whether found. -/
theorem tzScan_ok {s : State} {B : Addr} {Z dA dB n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dA) (h1 : s.gpr .t1 = off B dB) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h2 : s.gpr .t2 = 0) (h4 : s.gpr .a4 = 0) (h5 : s.gpr .a5 = 0) (h6 : s.gpr .a6 = 0) (ha3 : s.gpr .a3 = 0)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0) (hAZ : dA + 8 * n ≤ Z)
    (hBZ : dB + 8 * n ≤ Z) :
    WP isa (countLoop .t3 tzScan) s fun t => t.mem = s.mem ∧ t.gpr .a4 = 0 ∧
      (∃ found j₀ y, t.gpr .a5 = (if found then 1 else 0) ∧ t.gpr .a6 = BitVec.ofNat 64 j₀ ∧ t.gpr .a3 = y ∧
        ScanI (fun j => word s.mem B (dA + 8 * j) ||| word s.mem B (dB + 8 * j)) n found j₀ y) ∧
      Keep scanRegs s t := by
  have hnw := hs.nowrap
  generalize hf : (fun j => word s.mem B (dA + 8 * j) ||| word s.mem B (dB + 8 * j)) = f
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dA + 8 * i) ∧ t.gpr .t1 = off B (dB + 8 * i) ∧ t.gpr .t2 = BitVec.ofNat 64 i ∧
      t.gpr .a4 = 0 ∧ t.mem = s.mem ∧
      (∃ found j₀ y, t.gpr .a5 = (if found then 1 else 0) ∧ t.gpr .a6 = BitVec.ofNat 64 j₀ ∧ t.gpr .a3 = y ∧
        ScanI f i found j₀ y) ∧ Keep scanRegs s t
  refine WP.mono (wp_countdown (cnt := .t3) (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨j0, j1, j2, j4, jm, ⟨found, j₀, y, j5, j6, ja3, jI⟩, jk⟩ _ => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, h2, h4, rfl,
      ⟨false, 0, 0, h5, h6, ha3, by simp [ScanI]⟩, Keep.refl _ _⟩ h3)
    fun t ⟨_, _, _, t4, tm, tI, tk⟩ => ⟨tm, t4, tI, tk⟩
  have hs' := hs.congr jk.2.2
  have wa : t.mem.readW (off B (dA + 8 * i)) 64 = word s.mem B (dA + 8 * i) := by rw [jm]
  have wb : t.mem.readW (off B (dB + 8 * i)) 64 = word s.mem B (dB + 8 * i) := by rw [jm]
  have hfi : word s.mem B (dA + 8 * i) ||| word s.mem B (dB + 8 * i) = f i := by rw [← hf]
  refine WP.mono (WP.keep scanRegs (Q := fun t' =>
      t'.gpr .t0 = off B (dA + 8 * i) + BitVec.ofNat 64 8 ∧ t'.gpr .t1 = off B (dB + 8 * i) + BitVec.ofNat 64 8 ∧
      t'.gpr .t2 = BitVec.ofNat 64 i + BitVec.ofNat 64 1 ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
      t'.gpr .a5 = t.gpr .a5 ||| (if f i = 0 then 0 else 1) ∧
      t'.gpr .a6 = t.gpr .a6 ^^^ ((t.gpr .a6 ^^^ BitVec.ofNat 64 i) &&&
        (0 - ((t.gpr .a5 ^^^ 1#64) &&& (if f i = 0 then 0 else 1)))) ∧
      t'.gpr .a3 = t.gpr .a3 ^^^ ((t.gpr .a3 ^^^ f i) &&&
        (0 - ((t.gpr .a5 ^^^ 1#64) &&& (if f i = 0 then 0 else 1)))) ∧ t'.mem = t.mem) (by
    unfold tzScan
    brun [j0, j1, j2, j4, wa, wb, hfi, bit_lt, BitVec.add_zero, exec_addi_nat (show 8 < 2048 by decide),
      exec_addi_nat (show 1 < 2048 by decide),
      hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_using [hAZ, hi]), hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_using [hAZ, hi]) (by omega_using [hA8]),
      hs'.ld (show dB + 8 * i + 8 ≤ Z by omega_using [hBZ, hi]), hs'.al8 (show dB + 8 * i + 8 ≤ Z by omega_using [hBZ, hi]) (by omega_using [hB8])])
    (by rfl) (by rfl)) fun t' ⟨⟨l0, l1, l2, l3, l5, l6, la3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, by rw [lm, jm], ?_,
      jk.trans lk |>.mono (by decide)⟩, l3⟩
  · rw [l0, off_add, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_using []]
  · rw [l1, off_add, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_using []]
  · rw [l2, ← BitVec.ofNat_add]
  · rw [lk.gpr (by decide), j4]
  · rw [j5] at l5 l6 la3; rw [j6] at l6; rw [ja3] at la3
    -- The mask: one exactly where none was found and word `i` is not zero.
    have hm : ((if found then (1 : BitVec 64) else 0) ^^^ 1#64) &&& (if f i = 0 then 0 else 1) =
        if (!found && !decide (f i = 0)) then 1 else 0 := by
      cases found <;> by_cases hz : f i = 0 <;> simp only [hz] <;> decide
    rw [hm, selb] at l6 la3
    unfold ScanI at jI ⊢
    cases found
    · simp only [Bool.false_eq_true, ite_false] at jI
      obtain ⟨jz, rfl, rfl⟩ := jI
      by_cases hz : f i = 0
      · simp only [hz, decide_true, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false] at l5 l6 la3
        refine ⟨false, 0, 0, by rw [l5]; decide, l6, la3, ?_⟩
        simp only [Bool.false_eq_true, ite_false, and_true]
        intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact jz j hj
        · exact hz
      · simp only [hz, decide_false, Bool.not_false, Bool.and_self, ite_true, ite_false] at l5 l6 la3
        refine ⟨true, i, f i, by rw [l5]; decide, l6, la3, ?_⟩
        simp only [ite_true]
        exact ⟨by omega_using [], hz, jz, trivial⟩
    · simp only [ite_true] at jI
      obtain ⟨jlt, jnz, jz, rfl⟩ := jI
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false] at l6 la3
      refine ⟨true, j₀, f j₀, ?_, l6, la3, ?_⟩
      · rw [l5]; by_cases hz : f i = 0 <;> simp only [hz, ite_true, ite_false] <;> decide
      · simp only [ite_true]
        exact ⟨by omega_using [jlt], jnz, jz, trivial⟩

/-- A number whose words below `k` are zero is a multiple of `2^(64 k)`. -/
theorem low_zero {V : Nat} : ∀ k, (∀ j < k, V / 2 ^ (64 * j) % 2 ^ 64 = 0) → V % 2 ^ (64 * k) = 0
  | 0, _ => by rw [Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by
    rw [mod_succ_words, low_zero k fun j hj => h j (by omega_using [hj]), h k (by omega_using [])]; rfl

/-- Word `j` of an or of two numbers of `w` words. -/
theorem or_word {m : Mem} {B : Addr} {dA dB w j : Nat} (hj : j < w) :
    (word m B (dA + 8 * j) ||| word m B (dB + 8 * j)).toNat =
      (wordsVal m B dA w ||| wordsVal m B dB w) / 2 ^ (64 * j) % 2 ^ 64 := by
  rw [BitVec.toNat_or, Nat.or_div_two_pow, Nat.or_mod_two_pow, wordsVal_word hj, wordsVal_word hj]

/-- The registers `tz` writes. -/
abbrev tzRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a7, .a2, .a3, .a4, .a5, .a6]

/-- `ctz A Bx dst`: the trailing zeros of `[A] ∨ [Bx]` (`w` words, not zero) into `dst`. -/
theorem tz_ok {s : State} {B : Addr} {Z w N A Bx : Nat} {dst : Reg} (h : Ws s B Z w N) (hA : A < N)
    (hB : Bx < N) (hN : N ≤ 2048) (hdst : dst ∉ tzRegs)
    (hV : wordsVal s.mem B (arr w A) w ||| wordsVal s.mem B (arr w Bx) w ≠ 0) :
    WP isa (ctz A Bx dst) s fun t => t.mem = s.mem ∧
      t.gpr dst = BitVec.ofNat 64 (tz (wordsVal s.mem B (arr w A) w ||| wordsVal s.mem B (arr w Bx) w)) ∧
      Keep (dst :: tzRegs) s t := by
  have fitA := h.arr_fit hA
  have fitB := h.arr_fit hB
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have hw0 := h.wpos
  generalize hVd : wordsVal s.mem B (arr w A) w ||| wordsVal s.mem B (arr w Bx) w = V at hV ⊢
  unfold ctz
  refine WP.seq ?_
  refine ptr2_ok h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (show A < 2048 by omega_using [hA, hN]) (show Bx < 2048 by omega_using [hB, hN]) fun u u0 u1 ku um => ?_
  refine WP.mono (WP.keep [.a4, .t2, .a5, .a6, .a3, .t3] (Q := fun v => v.gpr .a4 = 0 ∧ v.gpr .t2 = 0 ∧
      v.gpr .a5 = 0 ∧ v.gpr .a6 = 0 ∧ v.gpr .a3 = 0 ∧ v.gpr .t3 = BitVec.ofNat 64 w ∧ v.mem = u.mem) (by
    have u9 : u.gpr .s9 = BitVec.ofNat 64 w := (ku.gpr (by decide)).trans h.s9
    brun [mov, fin64_exec_li_zero, u9, BitVec.add_zero]) (by rfl) (by rfl)) fun v ⟨⟨v4, v2, v5, v6, v3, vt3, vm⟩, vk⟩ => ?_
  have v0 : v.gpr .t0 = off B (arr w A) := (vk.gpr (by decide)).trans u0
  have v1 : v.gpr .t1 = off B (arr w Bx) := (vk.gpr (by decide)).trans u1
  have hsv := h.scr.congr ((ku.trans vk).2.2)
  refine WP.seq (WP.mono (tzScan_ok hsv v0 v1 vt3 v2 v4 v5 v6 v3 (by omega_using [hw0]) (by omega_using [hwl]) (arr_al w A) (arr_al w Bx)
    (by omega_using [fitA, hSz]) (by omega_using [fitB, hSz])) fun t₁ ⟨tm, t4, ⟨found, j₀, y, t5, t6, t3, tI⟩, tk⟩ => ?_)
  rw [vm, um] at tm
  rw [vm, um] at tI
  -- A nonzero word was found, the lowest.
  have wf : ∀ j < w, (word s.mem B (arr w A + 8 * j) ||| word s.mem B (arr w Bx + 8 * j)).toNat =
      V / 2 ^ (64 * j) % 2 ^ 64 := fun j hj => by rw [← hVd]; exact or_word hj
  have hVl : V < 2 ^ (64 * w) := by
    rw [← hVd]; exact Nat.or_lt_two_pow (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)
  cases found
  · exfalso
    simp only [ScanI, Bool.false_eq_true, ite_false] at tI
    have := low_zero (V := V) w fun j hj => by rw [← wf j hj, tI.1 j hj]; rfl
    exact hV (by rw [← Nat.mod_eq_of_lt hVl]; exact this)
  simp only [ScanI, ite_true] at tI
  obtain ⟨hj₀, hy0, hlow, rfl⟩ := tI
  have hlowV : V % 2 ^ (64 * j₀) = 0 := low_zero j₀ fun j hj => by rw [← wf j (by omega_using [hj₀, hj]), hlow j hj]; rfl
  have hyV := wf j₀ hj₀
  generalize hyN : (word s.mem B (arr w A + 8 * j₀) ||| word s.mem B (arr w Bx + 8 * j₀)).toNat = yN at hyV
  have hyN0 : yN ≠ 0 := fun e => hy0 (BitVec.eq_of_toNat_eq (by rw [hyN, e]; rfl))
  have hyl : yN < 2 ^ 64 := by rw [← hyN]; exact BitVec.isLt _
  have htz := tz_words hlowV (by rw [← hyV]; exact hyN0)
  rw [← hyV] at htz
  -- The stages within the word.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.a2] (Q := fun u => u.gpr .a2 = BitVec.ofNat 64 0 ∧ u.mem = t₁.mem)
    (by brun [fin64_exec_li_zero]; rfl) (by rfl) (by rfl)) fun u₂ ⟨⟨a2, m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tzStages_ok hyN0 hyl [5, 4, 3, 2, 1, 0] (by decide) 0 (Nat.zero_le _) a2
    (by rw [k2.gpr (by decide), t3, Nat.pow_zero, Nat.div_one, ← hyN, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [k2.gpr (by decide), t4])) fun u₃ ⟨⟨a3, m3⟩, k3⟩ => ?_
  rw [show ([5, 4, 3, 2, 1, 0] : List Nat).map (2 ^ ·) = pows 5 from rfl,
    greedy_pows 5 _ 0 (Nat.zero_le _) (by have := tz_lt (Nat.pos_of_ne_zero hyN0) hyl; omega_using [this])] at a3
  have a6 : u₃.gpr .a6 = BitVec.ofNat 64 j₀ := by rw [k3.gpr (by decide), k2.gpr (by decide), t6]
  have hd6 : (dst = Reg.a6) = False := eq_false (fun e => hdst (by rw [e]; decide))
  have fin : WP isa (.block [.shift .sll .d .a6 .a6 6, .add dst .a6 .a2]) u₃ fun t =>
      t = (u₃.write .a6 (BitVec.ofNat 64 j₀ <<< 6)).write dst (BitVec.ofNat 64 j₀ <<< 6 + BitVec.ofNat 64 (tz yN)) := by
    brun [a6, a3, hd6, exec_sll_imm (show 6 < 64 by decide)]
  refine WP.mono fin fun t e => ?_
  subst e
  refine ⟨by simp only [mem_write]; rw [m3, m2, tm], ?_, ?_⟩
  · rw [gpr_write_self, htz]
    apply BitVec.eq_of_toNat_eq
    have := tz_lt (Nat.pos_of_ne_zero hyN0) hyl
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j₀ < 2 ^ 64 by omega_using [hwl, hj₀]), Nat.mod_eq_of_lt (show tz yN < 2 ^ 64 by omega_using [this]),
      Nat.mod_eq_of_lt (show j₀ * 2 ^ 6 < 2 ^ 64 by omega_using [hwl, hj₀]), Nat.mod_eq_of_lt (show j₀ * 2 ^ 6 + tz yN < 2 ^ 64 by omega_using [hwl, hj₀, this]),
      Nat.mod_eq_of_lt (show 64 * j₀ + tz yN < 2 ^ 64 by omega_using [hwl, hj₀, this])]
    omega_using []
  · have sub : ∀ {rs : List Reg}, (∀ r ∈ rs, r ∈ tzRegs) → ∀ r ∈ rs, r ∈ dst :: tzRegs :=
      fun h r hr => List.mem_cons_of_mem _ (h r hr)
    have kA : Keep (dst :: tzRegs) s v := (ku.trans vk).mono (sub (by decide))
    have kB : Keep (dst :: tzRegs) v t₁ := tk.mono (sub (by decide))
    have kC : Keep (dst :: tzRegs) t₁ u₃ := (k2.trans k3).mono (sub (by decide))
    have kD : Keep (dst :: tzRegs) u₃ ((u₃.write .a6 (BitVec.ofNat 64 j₀ <<< 6)).write dst
        (BitVec.ofNat 64 j₀ <<< 6 + BitVec.ofNat 64 (tz yN))) :=
      ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono (by simp)
    exact ((kA.trans kB).trans (kC.trans kD)).mono (by simp)

end VG.Proof.Rsa.RISCV64.Keys
