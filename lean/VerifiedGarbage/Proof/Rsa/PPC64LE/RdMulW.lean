module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.MontKey
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbLoops
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
import VerifiedGarbage.Proof.Rsa.MontCheckMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: products by rows of words

`mulW_ok`: `Recover.mulW o x y`, with `R` in `r4` (`1 ≤ R ≤ w / 2`, `w` even), leaves
`[o] = [x] [y] mod 2^(32 w)` over the low `R` words of `[x]`: `[o]` zeroed, then for each word
`x_i` the row `[o]_{i..} += x_i [y]` of `w / 2 - i` words (`InvBatch.macWBody`, `macWLoop_ok`), the
carry dropped. `d e`, `a` and `b²` are its instances.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.InvBatch (keep_wv keep_word)
open VG.Proof.Rsa.PPC64LE.Loops (macWLoop_ok zerosW_ok AheadW macRegs)
open VG.Proof.Rsa.PPC64LE.MontKey (mkRegs)
open VG.Impl.Rsa.PPC64LE.Keys (ptr seqs countLoop)
open VG.Impl.Rsa.PPC64LE.Recover (mulW mulWRow)
open VG.Proof.Rsa.KeyWorkspace (arr S arr_disj)

theorem shr_ofNat {a k : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem off_diff (B : Addr) (a d : Nat) : off B (a + d) - off B a = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := B.isLt
  omega

theorem off_add (B : Addr) (a d : Nat) : off B a + BitVec.ofNat 64 d = off B (a + d) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ofNat_sub_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The state between the rows: `i` rows done. -/
structure WInv (s t : State) (B : Addr) (Z w N o x y R : Nat) (i : Nat) : Prop where
  ws : Ws t B Z w N
  r4 : t.gpr .r4 = BitVec.ofNat 64 (R - i)
  r10 : t.gpr .r10 = off B (arr w x + 8 * i)
  keep : KeyWorkspace.Keep B w [o] [] s.mem t.mem
  val : wordsVal t.mem B (arr w o) (w / 2) =
    wordsVal s.mem B (arr w x) i * wordsVal s.mem B (arr w y) (w / 2) % 2 ^ (64 * (w / 2))
  regs : Keep mkRegs s t

/-- A row's set-up: `x_i`, `[o]`'s and `[y]`'s pointers, `w / 2 - i` words and no carry. -/
theorem rowSet_ok {t : State} {B : Addr} {Z w N o x y i : Nat} (hw : Ws t B Z w N) (ho : o < N) (hx : x < N)
    (hy : y < N) (hN : N ≤ 256) (hi : i < w / 2) (h10 : t.gpr .r10 = off B (arr w x + 8 * i)) :
    WP isa (.block (([.load .d .r11 .r10 0] : List Instr) ++ ptr .r5 o ++ ptr .r6 x ++
      ([.sub .r6 .r10 .r6, .lsr .d .r8 .r29 1, .lsr .d .r3 .r6 3, .sub .r8 .r8 .r3, .add .r5 .r5 .r6,
        .addi .r6 .r5 0] : List Instr) ++ ptr .r7 y ++ ([.li .r9 0] : List Instr))) t fun u =>
      u.gpr .r5 = off B (arr w o + 8 * i) ∧ u.gpr .r6 = off B (arr w o + 8 * i) ∧
      u.gpr .r7 = off B (arr w y) ∧ u.gpr .r8 = BitVec.ofNat 64 (w / 2 - i) ∧ u.gpr .r9 = 0 ∧
      u.gpr .r11 = word t.mem B (arr w x + 8 * i) ∧ u.mem = t.mem ∧
      Keep [.r3, .r5, .r6, .r7, .r8, .r9, .r11] t u := by
  have fo := hw.arr_fit ho
  have fx := hw.arr_fit hx
  have hS : S w = 4 * (w + 2) := rfl
  have := hw.wle
  have hnw := hw.nowrap
  rw [show ([.load .d .r11 .r10 0] : List Instr) ++ ptr .r5 o ++ ptr .r6 x ++
      ([.sub .r6 .r10 .r6, .lsr .d .r8 .r29 1, .lsr .d .r3 .r6 3, .sub .r8 .r8 .r3, .add .r5 .r5 .r6,
        .addi .r6 .r5 0] : List Instr) ++ ptr .r7 y ++ ([.li .r9 0] : List Instr) =
      [.load .d .r11 .r10 0] ++ (ptr .r5 o ++ (ptr .r6 x ++
      (([.sub .r6 .r10 .r6, .lsr .d .r8 .r29 1, .lsr .d .r3 .r6 3, .sub .r8 .r8 .r3, .add .r5 .r5 .r6,
        .addi .r6 .r5 0] : List Instr) ++ (ptr .r7 y ++ ([.li .r9 0] : List Instr))))) by
    simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = word t.mem B (arr w x + 8 * i) ∧ u.mem = t.mem)
    (by mcrun [h10, BitVec.add_zero, exec_load_d, hw.scr.ld (show arr w x + 8 * i + 8 ≤ Z by omega)])
    (by decide)) fun u1 ⟨⟨a11, am⟩, k1⟩ => ?_
  have h1 := hw.of_keep k1
  refine ptr_ok h1 (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega) ?_
  refine ptr_ok (h1.of_keep (Keep.write _ _ _)) (r := .r6) (by decide) (by decide) (by decide)
    (show x < 2 ^ 15 by omega) ?_
  rw [WP.block_append_iff]
  have u10 : u1.gpr .r10 = off B (arr w x + 8 * i) := (k1.gpr _ (by decide)).trans h10
  have u29 : u1.gpr .r29 = BitVec.ofNat 64 w := h1.r29
  have d6 := off_diff B (arr w x) (8 * i)
  have s8 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (w / 2) := by
    rw [shr_ofNat (by omega)]
  have s3 : BitVec.ofNat 64 (8 * i) >>> 3 = BitVec.ofNat 64 i := by
    rw [shr_ofNat (by omega)]; congr 1; omega
  refine WP.mono (WP.keep [.r3, .r5, .r6, .r8] (Q := fun u => u.gpr .r5 = off B (arr w o + 8 * i) ∧
    u.gpr .r6 = off B (arr w o + 8 * i) ∧ u.gpr .r8 = BitVec.ofNat 64 (w / 2 - i) ∧ u.mem = u1.mem) (by
      prun [gpr_write, mem_write, u10, u29, BitVec.add_zero, d6, s8, s3, off_add,
        ofNat_sub_ofNat (show i ≤ w / 2 by omega) (show w / 2 < 2 ^ 64 by omega)]) (by decide))
    fun u2 ⟨⟨b5, b6, b8, bm⟩, k2⟩ => ?_
  have h2 := (h1.of_keep ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _))).of_keep k2
  refine ptr_ok h2 (r := .r7) (by decide) (by decide) (by decide) (show y < 2 ^ 15 by omega) ?_
  refine WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r9 = 0 ∧ u.mem = u2.mem)
    (by prun [gpr_write, mem_write]; rfl) (by decide)) fun u3 ⟨⟨c9, cm⟩, k3⟩ => ?_
  have kall : Keep [.r3, .r5, .r6, .r7, .r8, .r9, .r11] t u3 :=
    ((((k1.trans ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _))).trans k2).trans (Keep.write _ .r7 _)).trans
      k3).mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, c9, ?_, ?_, kall⟩
  · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact b5
  · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact b6
  · rw [k3.gpr _ (by decide)]; simp only [gpr_write, ite_true]
  · rw [k3.gpr _ (by decide)]; simp only [gpr_write]; exact b8
  · rw [k3.gpr _ (by decide)]; simp only [gpr_write]
    rw [k2.gpr _ (by decide)]; simp only [gpr_write]; exact a11
  · simp only [cm, bm, am]

theorem row_ok {s t : State} {B : Addr} {Z w N o x y R i : Nat} (hN : N ≤ 256) (ho : o < N) (hx : x < N)
    (hy : y < N) (hox : o ≠ x) (hoy : o ≠ y) (hi : i < R) (hRw : 2 * R ≤ w) (h : WInv s t B Z w N o x y R i) :
    WP isa (mulWRow o x y) t fun t' => WInv s t' B Z w N o x y R (i + 1) ∧
      t'.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1 := by
  have hw := h.ws
  have fo := hw.arr_fit ho
  have fx := hw.arr_fit hx
  have fy := hw.arr_fit hy
  have hS : S w = 4 * (w + 2) := rfl
  have := hw.wle
  have hnw := hw.nowrap
  have dox := arr_disj (w := w) hox
  have doy := arr_disj (w := w) hoy
  have hk : ∀ k, 8 * k ≤ 4 * w → 8 * k ≤ S w := fun k hk => by omega
  -- `x_i` as it was.
  have xi : word t.mem B (arr w x + 8 * i) = word s.mem B (arr w x + 8 * i) :=
    keep_word (b := 64) (o := 8 * i) h.keep (j := x) (by simp only [S]; omega)
      (by simp only [List.mem_singleton]; exact fun _ e => e ▸ hox) (by simp) (hw.fit64 hx)
  rw [mulWRow, WP.seq_iff]
  refine WP.mono (rowSet_ok hw ho hx hy hN (by omega) h.r10) fun u ⟨u5, u6, u7, u8, u9, u11, um, ku⟩ => ?_
  have hu := hw.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (macWLoop_ok hu.scr u5 u6 u7 u8 (by omega) (by omega) (by omega) (by omega) (by omega)
    (Or.inl (Nat.le_refl _)) (by unfold AheadW; omega)) fun v ⟨veq, _, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  refine WP.mono (WP.keep [.r4, .r10] (Q := fun t' => t'.gpr .r10 = v.gpr .r10 + BitVec.ofNat 64 8 ∧
      t'.gpr .r4 = v.gpr .r4 - BitVec.ofNat 64 1 ∧ t'.mem = v.mem) (by prun) (by decide))
    fun t' ⟨⟨e10, e4, em⟩, kt⟩ => ?_
  have k : Keep mkRegs t t' := ((ku.trans kv).trans kt).mono (by decide)
  have v4 : v.gpr .r4 = t.gpr .r4 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  have v10 : v.gpr .r10 = t.gpr .r10 := (kv.gpr _ (by decide)).trans (ku.gpr _ (by decide))
  rw [um, u9, u11, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at veq
  rw [um] at vout
  refine ⟨⟨hv.of_keep kt, ?_, ?_, ?_, ?_, h.regs.trans' k⟩, by rw [e4, v4]⟩
  · rw [e4, v4, h.r4]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [e10, v10, h.r10, off_add, show arr w x + 8 * i + 8 = arr w x + 8 * (i + 1) by omega]
  · rw [em]
    exact h.keep.trans (KeyWorkspace.Keep.of_arr (d := 8 * i) vout (by omega) (by simp))
  · -- The row's arithmetic.
    rw [em]
    have split : ∀ (m : Mem) (d : Nat), wordsVal m B d (w / 2) =
        wordsVal m B d i + 2 ^ (64 * i) * wordsVal m B (d + 8 * i) (w / 2 - i) := fun m d => by
      have := VG.Proof.Mont.PPC64LE.wordsVal_append m B d i (w / 2 - i); rwa [show i + (w / 2 - i) = w / 2 by omega] at this
    have lo : wordsVal v.mem B (arr w o) i = wordsVal t.mem B (arr w o) i :=
      vout.wordsVal (Or.inl (Nat.le_refl _)) (by omega)
    have ys : wordsVal t.mem B (arr w y) (w / 2) = wordsVal s.mem B (arr w y) (w / 2) :=
      keep_wv h.keep (hk _ (by omega)) (by simp only [List.mem_singleton]; exact fun _ e => e ▸ hoy) (by simp)
        (hw.fit64 hy)
    have yk : wordsVal t.mem B (arr w y) (w / 2 - i) % 2 ^ (64 * (w / 2 - i)) =
        wordsVal s.mem B (arr w y) (w / 2) % 2 ^ (64 * (w / 2 - i)) := by
      have := VG.Proof.Mont.PPC64LE.wordsVal_append t.mem B (arr w y) (w / 2 - i) i
      rw [show w / 2 - i + i = w / 2 by omega, ys] at this
      rw [this, Nat.add_mul_mod_self_left]
    have row := VG.Proof.Rsa.mulLo_row (P := 2 ^ (64 * i)) (Q := 2 ^ (64 * (w / 2 - i)))
      (L := wordsVal t.mem B (arr w o) i) (H := wordsVal t.mem B (arr w o + 8 * i) (w / 2 - i))
      (H' := wordsVal v.mem B (arr w o + 8 * i) (w / 2 - i)) (x := (word s.mem B (arr w x + 8 * i)).toNat)
      (Y := wordsVal s.mem B (arr w y) (w / 2)) (Nat.two_pow_pos _) (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)
      (by rw [← xi]; exact veq) yk
    have W : 2 ^ (64 * i) * 2 ^ (64 * (w / 2 - i)) = 2 ^ (64 * (w / 2)) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [split, lo, row, ← split, W, h.val, VG.Proof.Mont.PPC64LE.wordsVal_append s.mem B (arr w x) i 1]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mul, Nat.mul_assoc]

/-- `[o] := [x] [y] mod 2^(32 w)` over the low `R` words of `[x]` (`R` in `r4`). -/
theorem mulW_ok {s : State} {B : Addr} {Z w N o x y R : Nat} (h : Ws s B Z w N) (hN : N ≤ 256) (ho : o < N)
    (hx : x < N) (hy : y < N) (hox : o ≠ x) (hoy : o ≠ y) (hw2 : w % 2 = 0)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 R) (hR1 : 1 ≤ R) (hRw : 2 * R ≤ w) :
    WP isa (mulW o x y) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) (w / 2) =
        wordsVal s.mem B (arr w x) R * wordsVal s.mem B (arr w y) (w / 2) % 2 ^ (64 * (w / 2)) ∧
      Keep mkRegs s t := by
  have fo := h.arr_fit ho
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have hnw := h.nowrap
  rw [mulW]; simp only [seqs]; rw [WP.seq_iff]
  -- `[o]`'s pointer, `w / 2` and 0.
  have s8 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (w / 2) := by
    rw [shr_ofNat (by omega)]
  have hb1 : WP isa (.block (ptr .r5 o ++ ([.lsr .d .r8 .r29 1, .li .r0 0] : List Instr))) s fun u =>
      u.gpr .r5 = off B (arr w o) ∧ u.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ u.gpr .r0 = 0 ∧ u.mem = s.mem ∧
      Keep [.r0, .r5, .r8] s u := by
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega) ?_
    refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ u.gpr .r0 = 0 ∧
      u.mem = s.mem) (by prun [gpr_write, mem_write, h.r29, s8]; rfl) (by decide))
      fun u ⟨⟨u8, u0, um⟩, ku⟩ => ⟨by rw [ku.gpr _ (by decide)]; simp [gpr_write], u8, u0, um,
        ((Keep.write _ .r5 _).trans ku).mono (by decide)⟩
  refine WP.mono hb1 fun u ⟨u5, u8, u0, um, ku⟩ => ?_
  have hu := h.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (zerosW_ok hu.scr u5 u8 u0 (by omega) (by omega) (by omega)) fun v ⟨z, vout, kv⟩ => ?_
  have hv := hu.of_keep kv
  rw [WP.seq_iff]
  -- `x`'s pointer.
  rw [show ptr .r10 x = ptr .r10 x ++ ([] : List Instr) by simp]
  refine ptr_ok hv (r := .r10) (by decide) (by decide) (by decide) (show x < 2 ^ 15 by omega) (WP.block_nil ?_)
  have kt0 : Keep [.r10] v (v.write .r10 (off B (arr w x))) := Keep.write _ _ _
  have ht0 := hv.of_keep kt0
  have I0 : WInv s (v.write .r10 (off B (arr w x))) B Z w N o x y R 0 := by
    refine ⟨ht0, ?_, by simp [gpr_write], ?_, ?_, ?_⟩
    · rw [kt0.gpr _ (by decide), kv.gpr _ (by decide), ku.gpr _ (by decide), Nat.sub_zero]; exact h4
    · simp only [mem_write]; rw [← um]
      exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using vout) (by omega) (by simp)
    · simp only [mem_write]; rw [z]; simp [wordsVal]
    · exact ((ku.trans kv).trans kt0).mono (by decide)
  have a4 : (v.write .r10 (off B (arr w x))).gpr .r4 = BitVec.ofNat 64 R := by
    rw [kt0.gpr _ (by decide), kv.gpr _ (by decide), ku.gpr _ (by decide)]; exact h4
  refine WP.mono (wp_countdown (body := mulWRow o x y) (cnt := .r4) (N := R) (by omega) hR1
    (fun i t => WInv s t B Z w N o x y R i)
    (fun i hi t ht _ => row_ok hN ho hx hy hox hoy hi hRw ht) I0 a4)
    fun t ht => ⟨ht.ws, ht.keep, ht.val, ht.regs⟩

end VG.Proof.Rsa.PPC64LE.Recover
