module

public import VerifiedGarbage.Impl.Rsa.RISCV64.WordDiv
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2Lazy
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Bignum.WordStepLazy
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Division by words for the RSA key operations on RISC-V

`WordDiv.divCore a r m t none` and `WordDiv.divW a r m t`, on the working
space of `Proof/Rsa/RISCV64/KeyLayout.lean` (`w` words; a divisor of `v`
words and a dividend of `Wd`, for `divW` `v = w / 2` and `Wd = w`):

* `fixTop_ok`: `[m]`'s top word (`w / 2 - 1`) plus 1 if it is zero;
* `wdPrep_ok`: the divisor normalized and its reciprocal in the temporary
  (`Precompute.lz`, `normTail`, `recip`, at the arrays' offsets);
* `divInit_ok`: the first number of the division, `⌊X / 2^o⌋` for `X = [a]`
  and `o = 63 (S - 1)`, `S = Y + ⌈Y / 63⌉` steps for `Y = Wd - v + 1`
  (`sOf`, `stepCount_ok`, `divSetup_ok`, a copy of `X`'s top words shifted,
  `copyWord_ok`);
* `chunk_ok`: the next 63-bit chunk of `X` (`window_val`, `clamp_val`);
* `divCore_ok`: `[r]`'s first `v` words `:=` `[a] mod [m]`'s, for `[r]`'s
  first `v + 1` words zero and `[m]`'s top word not zero, by
  `PreR2Lazy.steps_ok` with `chunk` and `PreR2Lazy.finish_ok`; `divW_ok`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr)
open VG.Impl.Rsa.RISCV64.WordDiv (halfW fixTop normSetup prep stepCount divSetup copyWord divInit chunk steps
  divCore divW)
open VG.Impl.Bignum.RISCV64.Precompute (lz normTail recip step finish)

theorem srl1_ofNat {w : Nat} (hw : w < 2 ^ 64) : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (w / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (by omega)]

theorem kwd_exec_li_one {s : State} {d : Reg} : exec (.li d 1) s = some (s.write d 1#64) := by
  rw [exec_li (by decide)]; rfl

/-- `x + [x = 0]`: never zero. -/
theorem wdFix_val (x : BitVec 64) : (x + if x < 1#64 then 1 else 0).toNat = x.toNat + if x.toNat = 0 then 1 else 0 := by
  by_cases h : x.toNat = 0
  · have : x = 0 := BitVec.eq_of_toNat_eq h
    subst this; decide
  · have hlt : ¬ x < 1#64 := fun hc => h (by rw [BitVec.lt_def] at hc; simpa using hc)
    simp only [hlt, h, ite_false, Nat.add_zero]
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]

/-- The registers `fixTop` writes. -/
abbrev wdFixRegs : List Reg := [.a7, .t0, .t3, .t5, .t6]

/-- `fixTop m`: `[m]`'s word `v - 1` (`v = w / 2`) plus 1 if it is zero. -/
theorem fixTop_ok {s : State} {B : Addr} {Z w N m : Nat} (h : Ws s B Z w N) (hm : m < N) (hN : N ≤ 2048)
    (hw : 2 ≤ w) :
    WP isa (.block (fixTop m)) s fun t => Ws t B Z w N ∧ Frame B w [m] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w m) (w / 2) = wordsVal s.mem B (arr w m) (w / 2) +
        (if (word s.mem B (arr w m + 8 * (w / 2 - 1))).toNat = 0 then 2 ^ (64 * (w / 2 - 1)) else 0) ∧
      0 < (word t.mem B (arr w m + 8 * (w / 2 - 1))).toNat ∧
      t.gpr .a7 = off B (arr w m) ∧ t.gpr .t0 = BitVec.ofNat 64 (w / 2) ∧ Keep wdFixRegs s t ∧
      Outside B (arr w m + 8 * (w / 2 - 1)) 8 s.mem t.mem := by
  have fit := h.arr_fit hm
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  refine ptr_ok h (by decide) (by decide) (show m < 2048 by omega) ?_
  have ea := ea_top B (d := arr w m) (w := w / 2) (c := 8) (by omega) (by omega)
  rw [show arr w m + 8 * (w / 2) - 8 = arr w m + 8 * (w / 2 - 1) by omega] at ea
  generalize hT : word s.mem B (arr w m + 8 * (w / 2 - 1)) = T
  have rT : s.mem.readW (off B (arr w m + 8 * (w / 2 - 1))) 64 = T := hT
  refine WP.mono (WP.keep wdFixRegs (Q := fun t => t.gpr .a7 = off B (arr w m) ∧
      t.gpr .t0 = BitVec.ofNat 64 (w / 2) ∧
      t.mem = s.mem.writeW (off B (arr w m + 8 * (w / 2 - 1))) (T + if T < 1#64 then 1 else 0)) (by
    unfold halfW
    brun [h.s9, srl1_ofNat (show w < 2 ^ 64 by omega), kwd_exec_li_one, ea, rT, BitVec.add_zero,
      h.scr.ld (show arr w m + 8 * (w / 2 - 1) + 8 ≤ Z by omega),
      h.scr.al8 (show arr w m + 8 * (w / 2 - 1) + 8 ≤ Z by omega) (by have := arr_al w m; omega),
      h.scr.st (show arr w m + 8 * (w / 2 - 1) + 8 ≤ Z by omega)])
    (by rfl) (by rfl)) fun t ⟨⟨t7, t0, tm⟩, k⟩ => ?_
  have kk : Keep wdFixRegs s t := ((Keep.write _ _ _).trans k).mono (by decide)
  refine ⟨h.of_keep kk, ?_, ?_, ?_, t7, t0, kk, by rw [tm]; exact writeW_outside _ B _ (by omega)⟩
  · rw [tm]
    exact Frame.of_arr (writeW_outside _ B _ (by omega)) (by omega) (by simp)
  · have e1 := fin64_wordsVal_write_top s.mem B (arr w m) (w / 2 - 1) (T + if T < 1#64 then 1 else 0) (by omega)
    have e2 := wordsVal_succ_top s.mem B (arr w m) (w / 2 - 1)
    rw [show w / 2 - 1 + 1 = w / 2 by omega] at e1 e2
    rw [tm, e1, e2, wdFix_val, ← hT]
    split <;> simp only [Nat.mul_add, Nat.mul_one, Nat.add_zero, Nat.add_assoc] <;> omega
  · rw [tm, word_writeW_self, wdFix_val]
    split <;> omega

/-- The registers `prep` writes. -/
abbrev prepRegs : List Reg := [.a7, .a6, .t0, .t3, .t5, .a1, .a4, .s0, .s1, .s2, .s3, .s4]

/-- What the word steps need of the temporary at `dT`: `P = 2^z`, `d'`, its
reciprocal `v` and `d'ₗ`, for the divisor `M` of `v` words. -/
structure Norm (m : Mem) (B : Addr) (dT M v z : Nat) : Prop where
  hP : (word m B dT).toNat = 2 ^ z
  hz : z ≤ 63
  hd63 : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (v - 1))
  hd : (word m B (dT + 8)).toNat = M * 2 ^ z / 2 ^ (64 * (v - 1))
  hv : (word m B (dT + 16)).toNat = (2 ^ 128 - 1) / (word m B (dT + 8)).toNat - 2 ^ 64
  hdl : (word m B (dT + 8)).toNat * 2 ^ 64 + (word m B (dT + 24)).toNat = M * 2 ^ z / 2 ^ (64 * (v - 2))

/-- `Norm` in a memory that agrees on the temporary's four words. -/
theorem Norm.congr {m m' : Mem} {B : Addr} {dT M v z : Nat} (h : Norm m B dT M v z)
    (e0 : word m' B dT = word m B dT) (e8 : word m' B (dT + 8) = word m B (dT + 8))
    (e16 : word m' B (dT + 16) = word m B (dT + 16)) (e24 : word m' B (dT + 24) = word m B (dT + 24)) :
    Norm m' B dT M v z :=
  ⟨by rw [e0]; exact h.hP, h.hz, h.hd63, by rw [e8]; exact h.hd, by rw [e16, e8]; exact h.hv,
    by rw [e8, e24]; exact h.hdl⟩

/-- `prep m t`: the divisor `[m]` (`v` words in `t0`, its top word not zero)
normalized and its reciprocal, in `[t]`'s first four words; `a7` and `a6`
its address and the temporary's, and `a4` zero. -/
theorem wdPrep_ok {s : State} {B : Addr} {Z w N m t v : Nat} (h : Ws s B Z w N) (hm : m < N) (ht : t < N)
    (hN : N ≤ 2048) (hmt : m ≠ t) (hv : 4 ≤ v) (hvw : v ≤ w) (ht0 : s.gpr .t0 = BitVec.ofNat 64 v)
    (hT : 0 < (word s.mem B (arr w m + 8 * (v - 1))).toNat) :
    WP isa (prep m t) s fun u => Ws u B Z w N ∧ Frame B w [t] [] s.mem u.mem ∧ Keep prepRegs s u ∧
      u.gpr .a7 = off B (arr w m) ∧ u.gpr .a6 = off B (arr w t) ∧ u.gpr .t0 = BitVec.ofNat 64 v ∧
      u.gpr .a4 = 0 ∧ ∃ z, Norm u.mem B (arr w t) (wordsVal s.mem B (arr w m) v) v z := by
  have fitm := h.arr_fit hm
  have fitt := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have dmt := arr_disj (w := w) hmt
  unfold prep
  simp only [VG.Impl.Rsa.RISCV64.Keys.seqs]
  generalize hM : wordsVal s.mem B (arr w m) v = M
  -- The pointers.
  refine WP.seq ?_
  rw [normSetup, ← List.append_nil (ptr .a7 m ++ ptr .a6 t)]
  refine ptr2_ok h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (show m < 2048 by omega) (show t < 2048 by omega) fun s₂ g27 g26 k12' m2' => WP.block_nil_iff.mpr ?_
  have k12 : Keep [.a7, .a6, .t0] s s₂ := k12'.mono (by decide)
  have e0 : s₂.gpr .t0 = BitVec.ofNat 64 v := (k12'.gpr (by decide)).trans ht0
  have h2 : Ws s₂ B Z w N := h.of_keep k12
  -- `z`.
  refine WP.seq (WP.mono (lz_ok (dN := arr w m) (w := v) h2.scr g27 e0 (by omega) (arr_al w m) (by omega)
    (by rw [m2']; exact hT)) fun s₃ ⟨⟨z1, zb1, zb2, m3⟩, k3⟩ => ?_)
  rw [m2'] at z1 zb1 zb2
  have h3 : Ws s₃ B Z w N := h2.of_keep k3
  have g3 : ∀ r ∈ [Reg.a7, .a6, .t0], s₃.gpr r = s₂.gpr r := fun r hr => k3.gpr (by revert r hr; decide)
  -- `P`, `d'` and `d'ₗ`.
  refine WP.seq (WP.mono (normTail_ok (dN := arr w m) (dT := arr w t) (w := v) h3.scr
    ((g3 .a6 (by decide)).trans g26) ((g3 .a7 (by decide)).trans g27) ((g3 .t0 (by decide)).trans e0) z1
    (by omega) (by omega) (arr_al w m) (arr_al w t) (by omega) (by omega)
    (by rw [m3, m2']; exact zb1) (by rw [m3, m2']; exact zb2))
    fun s₄ ⟨⟨n0, nz, nd, nd63, ndl, n2, no⟩, k4⟩ => ?_)
  rw [m3, m2', hM] at nd nd63 ndl
  have h4 : Ws s₄ B Z w N := h3.of_keep k4
  have g4 : ∀ r ∈ [Reg.a7, .a6, .t0], s₄.gpr r = s₃.gpr r := fun r hr => k4.gpr (by revert r hr; decide)
  -- `v`.
  refine WP.mono (recip_ok (dT := arr w t) h4.scr ((g4 .a6 (by decide)).trans ((g3 .a6 (by decide)).trans g26))
    (arr_al w t) (by omega) (by rw [n2]; omega)) fun u ⟨⟨rv, r4, ro⟩, k5⟩ => ?_
  have k := (((k12.trans k3).trans k4).trans k5).mono (rs' := prepRegs) (by decide)
  have g5 : ∀ r ∈ [Reg.a7, .a6, .t0], u.gpr r = s₄.gpr r := fun r hr => k5.gpr (by revert r hr; decide)
  have fr : Frame B w [t] [] s.mem u.mem := by
    rw [← m2', ← m3]
    have o := no.trans (ro.mono (o' := arr w t) (n' := 32) (by omega) (by omega))
    exact Frame.of_arr (o := t) (d := 0) (n := 32) (fun x hx => o x (by simpa using hx)) (by omega) (by simp)
  refine ⟨h.of_keep k, fr, k, (g5 _ (by decide)).trans ((g4 _ (by decide)).trans ((g3 _ (by decide)).trans g27)),
    (g5 _ (by decide)).trans ((g4 _ (by decide)).trans ((g3 _ (by decide)).trans g26)),
    (g5 _ (by decide)).trans ((g4 _ (by decide)).trans ((g3 _ (by decide)).trans e0)), r4, ?_⟩
  have w0 : word u.mem B (arr w t) = word s₄.mem B (arr w t) := ro.word (by omega) (by omega)
  have w8 : word u.mem B (arr w t + 8) = word s₄.mem B (arr w t + 8) := ro.word (by omega) (by omega)
  have w24 : word u.mem B (arr w t + 24) = word s₄.mem B (arr w t + 24) := ro.word (by omega) (by omega)
  refine ⟨zOf (word s.mem B (arr w m + 8 * (v - 1))).toNat, by rw [w0]; exact n0, nz, nd63,
    by rw [w8]; exact nd, by rw [rv, w8, n2], by rw [w8, w24]; exact ndl⟩

/-- The registers `divW` writes. -/
abbrev divWRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

theorem exec_srlReg {s : State} {d n m : Reg} :
    exec (.shiftReg .srl .d d n m) s = some (s.write d (s.gpr n >>> ((s.gpr m).toNat % 64))) := rfl

/-- The 64 bits of `X` from bit `64 J + o`, from its words `J` and `J + 1`. -/
theorem window_val (lo hi : BitVec 64) {o : Nat} (ho : o < 64) :
    ((lo >>> o) ||| ((hi <<< 1) <<< (63 - o))).toNat = lo.toNat / 2 ^ o + hi.toNat % 2 ^ o * 2 ^ (64 - o) := by
  rw [← BitVec.shiftLeft_add, show 1 + (63 - o) = 64 - o by omega]
  exact VG.Proof.Bignum.WordStep.shr_or_shl lo hi (by omega)

/-- `o mod 64`, and `63 - o mod 64`, as the shifts read them. -/
theorem shifts_val (o : Nat) (ho : o < 2 ^ 64) :
    (BitVec.ofNat 64 o &&& BitVec.ofNat 64 63).toNat % 64 = o % 64 ∧
      (BitVec.ofNat 64 o &&& BitVec.ofNat 64 63 ^^^ BitVec.ofNat 64 63).toNat % 64 = 63 - o % 64 := by
  have e : (BitVec.ofNat 64 o &&& BitVec.ofNat 64 63) = BitVec.ofNat 64 (o % 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho,
      show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (show o % 64 < 2 ^ 64 by omega)]
  rw [e]
  refine ⟨by rw [BitVec.toNat_ofNat]; omega, ?_⟩
  have hx : BitVec.ofNat 64 (o % 64) ^^^ BitVec.ofNat 64 63 = BitVec.ofNat 64 (63 - o % 64) := by
    have hlt : o % 64 < 64 := Nat.mod_lt _ (by decide)
    generalize o % 64 = k at hlt ⊢
    revert k; decide
  rw [hx, BitVec.toNat_ofNat]; omega

/-- The steps of a division of `Wd` words by `v`: `S = Y + c` for `Y = Wd - v + 1`
and `c = ⌈Y / 63⌉ = cOf (Y - 1)`. -/
def sOf (v Wd : Nat) : Nat := Wd - v + 1 + cOf (Wd - v)

/-- `c = cOf y = ⌈(y + 1) / 63⌉`, for `y < 189`. -/
theorem cOf_bounds' {y : Nat} (hy : y ≤ 187) : y + 1 ≤ 63 * cOf y ∧ 63 * cOf y ≤ y + 63 ∧ cOf y ≤ 3 := by
  unfold cOf; split <;> split <;> omega

/-- The steps of a division of `Wd` words by `v`, and the first chunk's offset
`o = 63 (S - 1)`, whose word `⌊o / 64⌋` is `Wd - v`: `64 Y - 63 ≤ o < 64 Y`. -/
theorem div_counts {v Wd : Nat} (hY : Wd - v ≤ 187) :
    64 * (Wd - v + 1) ≤ 63 * sOf v Wd ∧ 63 * sOf v Wd ≤ 64 * (Wd - v + 1) + 62 ∧
      63 * (sOf v Wd - 1) / 64 = Wd - v ∧ sOf v Wd ≤ Wd - v + 4 := by
  have := cOf_bounds' hY
  unfold sOf
  omega

/-- A difference of literals that does not wrap. -/
theorem bv_sub_lit {a b : Nat} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

/-- `stepCount`, `v` in `t0` and `Wd` in `t6`: `S` in `a1`. -/
theorem stepCount_ok {s : State} {v Wd : Nat} (ht0 : s.gpr .t0 = BitVec.ofNat 64 v)
    (ht6 : s.gpr .t6 = BitVec.ofNat 64 Wd) (hvW : v < Wd) (hWd : Wd < 2 ^ 20) (hY : Wd - v ≤ 187) :
    WP isa (.block stepCount) s fun t => (t.gpr .a1 = BitVec.ofNat 64 (sOf v Wd) ∧ t.mem = s.mem) ∧
      Keep [.s4, .s0, .s1, .a1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have ey : BitVec.ofNat 64 Wd - BitVec.ofNat 64 v + BitVec.ofNat 64 1 = BitVec.ofNat 64 (Wd - v + 1) := by
    rw [bv_sub_lit (by omega) (by omega), BitVec.ofNat_add]
  unfold stepCount
  brun [exec_li, ht0, ht6, ey, sltu_lit (a := 63) (w := Wd - v + 1) (by decide) (by omega),
    sltu_lit (a := 126) (w := Wd - v + 1) (by decide) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [Mont.off, BitVec.toNat_add, BitVec.toNat_ofNat, sOf, cOf]
  split <;> split <;> split <;> split <;> omega

/-- `divSetup a r`, `v` in `t0` and `Wd` in `t6`: `a5`, `a2`, the steps `S`
(`a1`), the first chunk's offset `o` (`t1`), and the copy's pointers, count and
shifts. -/
theorem divSetup_ok {s : State} {B : Addr} {Z w N a r v Wd : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hN : N ≤ 2048) (ht0 : s.gpr .t0 = BitVec.ofNat 64 v) (ht6 : s.gpr .t6 = BitVec.ofNat 64 Wd)
    (hv : 1 ≤ v) (hvW : v < Wd) (hWd : Wd ≤ w + 2) (hY : Wd - v ≤ 187) :
    let S := sOf v Wd
    let o := 63 * (S - 1)
    WP isa (.block (divSetup a r)) s fun u => u.gpr .a5 = off B (arr w a) ∧ u.gpr .a2 = off B (arr w r) ∧
      u.gpr .a1 = BitVec.ofNat 64 S ∧ u.gpr .t1 = BitVec.ofNat 64 o ∧
      u.gpr .t3 = off B (arr w a + 8 * (o / 64)) ∧ u.gpr .t4 = off B (arr w r) ∧
      u.gpr .t5 = BitVec.ofNat 64 (Wd - o / 64 - 1) ∧ (u.gpr .s3).toNat % 64 = o % 64 ∧
      (u.gpr .a3).toNat % 64 = 63 - o % 64 ∧ u.mem = s.mem ∧
      Keep [.a5, .a2, .a1, .t1, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .a3, .s4] s u := by
  intro S o
  have fita := h.arr_fit ha
  have nw := h.nowrap
  have hwl := h.wle
  have hc := div_counts hY
  rw [divSetup]
  simp only [List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (show a < 2048 by omega) ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (show r < 2048 by omega) ?_
  generalize hs₁ : (s.write .a5 (off B (arr w a))).write .a2 (off B (arr w r)) = s₁
  have k1 : Keep [.a5, .a2] s s₁ := by
    rw [← hs₁]; exact ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono (by decide)
  have g5 : s₁.gpr .a5 = off B (arr w a) := by rw [← hs₁]; simp [gpr_write]
  have g2 : s₁.gpr .a2 = off B (arr w r) := by rw [← hs₁]; simp [gpr_write]
  refine WP.block_append (WP.mono (stepCount_ok ((k1.gpr (by decide)).trans ht0)
    ((k1.gpr (by decide)).trans ht6) hvW (by omega) hY)
    fun s₂ ⟨⟨a12, m2⟩, k2⟩ => ?_)
  have ho : o < 2 ^ 20 := by omega
  obtain ⟨sh1, sh2⟩ := shifts_val o (by omega)
  refine WP.mono (WP.keep [.t1, .t3, .t4, .t5, .s1, .s2, .s3, .a3] (Q := fun u =>
      u.gpr .t1 = BitVec.ofNat 64 o ∧ u.gpr .t3 = off B (arr w a + 8 * (o / 64)) ∧ u.gpr .t4 = off B (arr w r) ∧
      u.gpr .t5 = BitVec.ofNat 64 (Wd - o / 64 - 1) ∧ (u.gpr .s3).toNat % 64 = o % 64 ∧
      (u.gpr .a3).toNat % 64 = 63 - o % 64 ∧ u.mem = s₂.mem) (by
    brun [a12, (k2.gpr (by decide)).trans g2, (k2.gpr (by decide)).trans g5, (k2.gpr (by decide)).trans
      ((k1.gpr (by decide)).trans ht6)]
    have eo : (BitVec.ofNat 64 S - 1#64) <<< 6 - (BitVec.ofNat 64 S - 1#64) = BitVec.ofNat 64 o := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
        show (1#64).toNat = 1 from rfl]
      omega
    rw [eo]
    refine ⟨rfl, ?_, ?_, sh1, sh2⟩
    · rw [BitVec.add_comm, show off B (arr w a + 8 * (o / 64)) = off B (arr w a) + BitVec.ofNat 64 (8 * (o / 64)) from
        (off_add _ _ _).symm]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
        show (2 : Nat) ^ 6 = 64 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, Nat.mul_comm]
    · have e6 : BitVec.ofNat 64 o >>> 6 = BitVec.ofNat 64 (o / 64) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show o / 2 ^ 6 < 2 ^ 64 by omega)]
      rw [e6, bv_sub_lit (by omega) (by omega), show (1#64) = BitVec.ofNat 64 1 from rfl,
        bv_sub_lit (by omega) (by omega)]) (by rfl) (by rfl)) fun u ⟨⟨u1, u3, u4, u5, us3, ua3, um⟩, uk⟩ => ?_
  have k := (k1.trans k2).trans uk
  refine ⟨(uk.gpr (by decide)).trans ((k2.gpr (by decide)).trans g5),
    (uk.gpr (by decide)).trans ((k2.gpr (by decide)).trans g2), (uk.gpr (by decide)).trans a12, u1, u3, u4, u5,
    us3, ua3, by rw [um, m2, ← hs₁]; rfl, k.mono (by decide)⟩


/-- What the copy keeps after `i` words: the pointers, the shifts, and
`[r]`'s low `i` words `⌊X / 2^o⌋`'s, for `X` `[a]`'s first `Wd` words. -/
def CInv (s : State) (B : Addr) (w Wd a r J o : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (arr w a + 8 * (J + i)) ∧ t.gpr .t4 = off B (arr w r + 8 * i) ∧
    (t.gpr .s3).toNat % 64 = o % 64 ∧ (t.gpr .a3).toNat % 64 = 63 - o % 64 ∧
    Outside B (arr w r) (8 * i) s.mem t.mem ∧
    wordsVal t.mem B (arr w r) i = wordsVal s.mem B (arr w a) Wd / 2 ^ o % 2 ^ (64 * i) ∧
    Keep [.s0, .s2, .t3, .t4, .t5] s t

theorem copyWord_ok {s : State} {B : Addr} {Z w N a r J o Wd : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hra : r ≠ a) (hJ : J = o / 64) (hWd : Wd ≤ w + 2) {i : Nat} (hi : J + i + 1 < Wd) {t : State} (hI : CInv s B w Wd a r J o i t) :
    WP isa (.block (copyWord ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      CInv s B w Wd a r J o (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have fita := h.arr_fit ha
  have fitr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have dra := arr_disj (w := w) hra
  obtain ⟨j3, j4, j3s, j3a, jout, jv, jk⟩ := hI
  have hs' := h.scr.congr jk.2.2
  have wl : word t.mem B (arr w a + 8 * (J + i)) = word s.mem B (arr w a + 8 * (J + i)) :=
    jout.word (by omega) (by omega)
  have wh : word t.mem B (arr w a + 8 * (J + i) + 8) = word s.mem B (arr w a + 8 * (J + i + 1)) := by
    rw [show arr w a + 8 * (J + i) + 8 = arr w a + 8 * (J + i + 1) by omega]; exact jout.word (by omega) (by omega)
  generalize hlo : word s.mem B (arr w a + 8 * (J + i)) = lo at wl
  generalize hhi : word s.mem B (arr w a + 8 * (J + i + 1)) = hi at wh
  generalize hv : (lo >>> ((t.gpr .s3).toNat % 64)) ||| ((hi <<< 1) <<< ((t.gpr .a3).toNat % 64)) = v
  refine WP.mono (WP.keep [.s0, .s2, .t3, .t4, .t5] (Q := fun t' =>
      t'.gpr .t3 = off B (arr w a + 8 * (J + i) + 8) ∧ t'.gpr .t4 = off B (arr w r + 8 * i + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem.writeW (off B (arr w r + 8 * i)) v) (by
    have rl : t.mem.readW (off B (arr w a + 8 * (J + i))) 64 = lo := wl
    have rh : t.mem.readW (off B (arr w a + 8 * (J + i) + 8)) 64 = hi := wh
    unfold copyWord
    brun [j3, j4, rl, rh, exec_srlReg, exec_sllReg, hv, BitVec.add_zero,
      hs'.ld (show arr w a + 8 * (J + i) + 8 ≤ Z by omega),
      hs'.al8 (show arr w a + 8 * (J + i) + 8 ≤ Z by omega) (by have := arr_al w a; omega),
      hs'.ld (show arr w a + 8 * (J + i) + 8 + 8 ≤ Z by omega),
      hs'.al8 (show arr w a + 8 * (J + i) + 8 + 8 ≤ Z by omega) (by have := arr_al w a; omega),
      hs'.st (show arr w r + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show arr w r + 8 * i + 8 ≤ Z by omega) (by have := arr_al w r; omega)])
    (by rfl) (by rfl)) fun t' ⟨⟨u3, u4, u5, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, (jk.trans uk).mono (by decide)⟩, u5⟩
  · rw [u3, show arr w a + 8 * (J + i) + 8 = arr w a + 8 * (J + (i + 1)) by omega]
  · rw [u4, show arr w r + 8 * i + 8 = arr w r + 8 * (i + 1) by omega]
  · rw [uk.gpr (by decide)]; exact j3s
  · rw [uk.gpr (by decide)]; exact j3a
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := arr w r + 8 * i) _ (by omega)).mono (by omega) (by omega))
  · have ho : o % 64 < 64 := Nat.mod_lt _ (by decide)
    have hvv : v.toNat = wordsVal s.mem B (arr w a) Wd / 2 ^ o / 2 ^ (64 * i) % 2 ^ 64 := by
      rw [← hv, j3s, j3a, window_val lo hi ho, ← hlo, ← hhi,
        ← wordsVal_word (m := s.mem) (base := B) (o := arr w a) (n := Wd) (j := J + i) (by omega),
        ← wordsVal_word (m := s.mem) (base := B) (o := arr w a) (n := Wd) (j := J + i + 1) (by omega),
        Nat.div_div_eq_div_mul, ← Nat.pow_add, ← VG.Proof.Bignum.WordStep.shr_words _ _ ho,
        show 64 * (J + i) + o % 64 = o + 64 * i by subst hJ; omega]
    rw [um, fin64_wordsVal_write_top _ _ _ _ _ (by omega), jv, hvv, mod_succ_words]

/-- The registers `divInit` writes. -/
abbrev divInitRegs : List Reg := [.a5, .a2, .a1, .t1, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .a3, .s4]

/-- `divInit a r`, `v` in `t0`, `Wd` in `t6` and `[r]`'s first `v + 1` words
zero: `V := ⌊X / 2^o⌋` there, for `X` `[a]`'s first `Wd` words, `S` steps,
`o = 63 (S - 1)`; `a5`, `a2`, `a1` and `t1` as the steps need them. -/
theorem divInit_ok {s : State} {B : Addr} {Z w N a r v Wd : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hN : N ≤ 2048) (hra : r ≠ a) (ht0 : s.gpr .t0 = BitVec.ofNat 64 v) (ht6 : s.gpr .t6 = BitVec.ofNat 64 Wd)
    (hv : 2 ≤ v) (hvW : v < Wd) (hWd : Wd ≤ w + 2) (hY : Wd - v ≤ 187)
    (hr0 : wordsVal s.mem B (arr w r) (v + 1) = 0) :
    let S := sOf v Wd
    let o := 63 * (S - 1)
    WP isa (divInit a r) s fun u =>
      wordsVal u.mem B (arr w r) (v + 1) = wordsVal s.mem B (arr w a) Wd / 2 ^ o ∧
      u.gpr .a5 = off B (arr w a) ∧ u.gpr .a2 = off B (arr w r) ∧ u.gpr .a1 = BitVec.ofNat 64 S ∧
      u.gpr .t1 = BitVec.ofNat 64 o ∧ Outside B (arr w r) (8 * (v + 1)) s.mem u.mem ∧ Keep divInitRegs s u := by
  intro S o
  have fita := h.arr_fit ha
  have fitr := h.arr_fit hr
  have nw := h.nowrap
  have hS' : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have dra := arr_disj (w := w) hra
  have hc := div_counts hY
  unfold divInit
  refine WP.seq (WP.mono (divSetup_ok h ha hr hN ht0 ht6 (by omega) hvW hWd hY)
    fun s₁ ⟨u5, u2, u1, ut1, u3, u4, ut5, us3, ua3, um, uk⟩ => ?_)
  generalize hJ : o / 64 = J at u3 ut5 hc
  have hJv : J = Wd - v := hc.2.2.1
  have h₁ : Ws s₁ B Z w N := h.of_keep uk
  have I0 : CInv s₁ B w Wd a r J o 0 s₁ := ⟨by rw [u3]; rfl, by rw [u4]; rfl, us3, ua3,
    Outside.refl _ _ _ _, by rw [Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl, Keep.refl _ _⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := Wd - J - 1) (by omega) (by omega)
    (CInv s₁ B w Wd a r J o)
    (fun i hi t hI _ => copyWord_ok h₁ ha hr hra hJ.symm hWd (by omega) hI) I0 ut5)
    fun s₂ ⟨j3, j4, j3s, _, jout, jv, jk⟩ => ?_)
  rw [um] at jout jv
  have hs₂ := h.scr.congr (uk.trans jk).2.2
  have wl : word s₂.mem B (arr w a + 8 * (J + (Wd - J - 1))) = word s.mem B (arr w a + 8 * (Wd - 1)) := by
    rw [show J + (Wd - J - 1) = Wd - 1 by omega]; exact jout.word (by omega) (by omega)
  generalize hlo : word s.mem B (arr w a + 8 * (Wd - 1)) = lo at wl
  refine WP.mono (WP.keep [.s0] (Q := fun t => t.mem = s₂.mem.writeW (off B (arr w r + 8 * (Wd - J - 1)))
      (lo >>> ((s₂.gpr .s3).toNat % 64))) (by
    have rl : s₂.mem.readW (off B (arr w a + 8 * (J + (Wd - J - 1)))) 64 = lo := wl
    brun [j3, j4, rl, exec_srlReg, hs₂.ld (show arr w a + 8 * (J + (Wd - J - 1)) + 8 ≤ Z by omega),
      hs₂.al8 (show arr w a + 8 * (J + (Wd - J - 1)) + 8 ≤ Z by omega) (by have := arr_al w a; omega),
      hs₂.st (show arr w r + 8 * (Wd - J - 1) + 8 ≤ Z by omega),
      hs₂.al8 (show arr w r + 8 * (Wd - J - 1) + 8 ≤ Z by omega) (by have := arr_al w r; omega)])
    (by rfl) (by rfl)) fun u ⟨tm, tk⟩ => ?_
  have k := ((uk.trans jk).trans tk)
  have g : ∀ q ∈ [Reg.a5, .a2, .a1, .t1], u.gpr q = s₁.gpr q := fun q hq =>
    (jk.trans tk).gpr (by revert q hq; decide)
  have ho : o % 64 < 64 := Nat.mod_lt _ (by decide)
  -- `X`'s top word shifted: `⌊X / 2^o⌋`'s word `Wd - J - 1`, its last.
  have hX : wordsVal s.mem B (arr w a) Wd < 2 ^ (64 * Wd) := wordsVal_lt _ _ _ _
  have htop : (lo >>> ((s₂.gpr .s3).toNat % 64)).toNat =
      wordsVal s.mem B (arr w a) Wd / 2 ^ o / 2 ^ (64 * (Wd - J - 1)) % 2 ^ 64 := by
    rw [j3s, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← hlo,
      ← wordsVal_word (m := s.mem) (base := B) (o := arr w a) (n := Wd) (j := Wd - 1) (by omega),
      Nat.div_div_eq_div_mul, ← Nat.pow_add, show o + 64 * (Wd - J - 1) = 64 * (Wd - 1) + o % 64 by omega,
      VG.Proof.Bignum.WordStep.shr_words _ _ ho, show Wd - 1 + 1 = Wd by omega,
      Nat.div_eq_of_lt hX, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
  have hlow : wordsVal u.mem B (arr w r) (Wd - J - 1 + 1) = wordsVal s.mem B (arr w a) Wd / 2 ^ o := by
    rw [tm, fin64_wordsVal_write_top _ _ _ _ _ (by omega), jv, htop, ← mod_succ_words, Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega))
  have o2 : Outside B (arr w r) (8 * (v + 1)) s.mem u.mem := by
    rw [tm]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside s₂.mem B (d := arr w r + 8 * (Wd - J - 1)) _ (by omega)).mono (by omega) (by omega))
  refine ⟨?_, (g .a5 (by decide)).trans u5, (g .a2 (by decide)).trans u2, (g .a1 (by decide)).trans u1,
    (g .t1 (by decide)).trans ut1, o2, k.mono (by decide)⟩
  -- The words above: still zero.
  have hz : wordsVal u.mem B (arr w r + 8 * (Wd - J - 1 + 1)) (v + 1 - (Wd - J - 1 + 1)) = 0 := by
    have o3 : Outside B (arr w r) (8 * (Wd - J)) s.mem u.mem := by
      rw [tm]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside s₂.mem B (d := arr w r + 8 * (Wd - J - 1)) _ (by omega)).mono (by omega) (by omega))
    rw [Outside.wordsVal o3 (by omega) (by omega)]
    exact wordsVal_zero_part hr0 (by omega)
  rw [show v + 1 = (Wd - J - 1 + 1) + (v + 1 - (Wd - J - 1 + 1)) by omega, wordsVal_append, hlow, hz,
    Nat.mul_zero, Nat.add_zero]

/-- The next chunk's offset, `max(o - 63, 0)` for `o = 63 k`, as `chunk`
computes it. -/
theorem clamp_val {k : Nat} (hk : 63 * k < 2 ^ 63) :
    (BitVec.ofNat 64 (63 * k) - 63#64 &&& ((BitVec.ofNat 64 (63 * k) - 63#64).sshiftRight 63 ^^^ -1#64)) =
      BitVec.ofNat 64 (63 * (k - 1)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · decide
  · rw [show (63#64) = BitVec.ofNat 64 63 from rfl, bv_sub_lit (by omega) (by omega),
      show 63 * k - 63 = 63 * (k - 1) by omega]
    have hm : (BitVec.ofNat 64 (63 * (k - 1))).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm]
    have h0 : BitVec.ofNat 64 (63 * (k - 1)) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      show 63 * (k - 1) / 2 ^ 63 = 0
      exact Nat.div_eq_of_lt (by omega)
    rw [h0, BitVec.zero_xor, show (-1#64 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]

/-- `⌊o / 64⌋ 8` plus a base, as the shifts compute it. -/
theorem ea_word (B : Addr) {d o : Nat} (ho : o < 2 ^ 20) :
    BitVec.ofNat 64 o >>> 6 <<< 3 + off B d = off B (d + 8 * (o / 64)) := by
  rw [BitVec.add_comm, show off B (d + 8 * (o / 64)) = off B d + BitVec.ofNat 64 (8 * (o / 64)) from
    (off_add _ _ _).symm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 6 = 64 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, Nat.mul_comm]

/-- The registers `chunk` writes. -/
abbrev chunkRegs : List Reg := [.t1, .t3, .t4, .t5, .a0, .t6]

/-- `chunk`, `t1 = 63 k` and `a5` `[a]`'s address, whose words are `X`'s:
`t1 := 63 (k - 1)` (0 for `k = 0`) and `t6 := ` the 64 bits of `X` from there
shifted up a bit, so that `⌊t₆ / 2⌋ = ⌊X / 2^(63 (k - 1))⌋ mod 2^63`. -/
theorem chunk_ok {u : State} {B : Addr} {Z w a k Wd : Nat} {X : Nat} (hs : Scr u B Z)
    (h1 : u.gpr .t1 = BitVec.ofNat 64 (63 * k)) (h5 : u.gpr .a5 = off B (arr w a)) (hk : 63 * k < 2 ^ 20)
    (hkw : 63 * (k - 1) / 64 + 2 ≤ Wd) (hZ : arr w a + 8 * Wd ≤ Z) (hX : wordsVal u.mem B (arr w a) Wd = X) :
    WP isa (.block chunk) u fun u' => (u'.gpr .t1 = BitVec.ofNat 64 (63 * (k - 1)) ∧
      (u'.gpr .t6).toNat / 2 = X / 2 ^ (63 * (k - 1)) % 2 ^ 63 ∧ u'.mem = u.mem) ∧ Keep chunkRegs u u' := by
  have hnw := hs.nowrap
  generalize ho : 63 * (k - 1) = o at hkw ⊢
  have ho' : o < 2 ^ 20 := by omega
  obtain ⟨sh1, sh2⟩ := shifts_val o (by omega)
  have ea := ea_word B (d := arr w a) ho'
  have al := arr_al w a
  have wl := (wordsVal_word (m := u.mem) (base := B) (o := arr w a) (n := Wd) (j := o / 64) (by omega)).symm
  have wh := (wordsVal_word (m := u.mem) (base := B) (o := arr w a) (n := Wd) (j := o / 64 + 1) (by omega)).symm
  generalize hlo : word u.mem B (arr w a + 8 * (o / 64)) = lo at wl
  generalize hhi : word u.mem B (arr w a + 8 * (o / 64 + 1)) = hi at wh
  have rl : u.mem.readW (off B (arr w a + 8 * (o / 64))) 64 = lo := hlo
  have rh : u.mem.readW (off B (arr w a + 8 * (o / 64) + 8)) 64 = hi := by
    rw [show arr w a + 8 * (o / 64) + 8 = arr w a + 8 * (o / 64 + 1) by omega]; exact hhi
  refine WP.keep chunkRegs ?_ (by rfl) (by rfl)
  have cv := clamp_val (k := k) (by omega)
  rw [ho] at cv
  unfold chunk
  brun [h1, h5, cv, ea, rl, rh, exec_srlReg, exec_sllReg, BitVec.add_zero,
    hs.ld (show arr w a + 8 * (o / 64) + 8 ≤ Z by omega),
    hs.al8 (show arr w a + 8 * (o / 64) + 8 ≤ Z by omega) (by omega),
    hs.ld (show arr w a + 8 * (o / 64) + 8 + 8 ≤ Z by omega),
    hs.al8 (show arr w a + 8 * (o / 64) + 8 + 8 ≤ Z by omega) (by omega)]
  rw [sh1, sh2, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, window_val lo hi (Nat.mod_lt _ (by decide)), wl, wh,
    ← VG.Proof.Bignum.WordStep.shr_words _ _ (Nat.mod_lt _ (by decide)), show 64 * (o / 64) + o % 64 = o by omega, hX,
    ← Nat.mod_mod_of_dvd (X / 2 ^ o) (show 2 ^ 63 ∣ 2 ^ 64 from Nat.pow_dvd_pow 2 (by decide))]
  have hz := Nat.mod_lt (X / 2 ^ o) (show 0 < 2 ^ 64 by decide)
  generalize X / 2 ^ o % 2 ^ 64 = z at hz ⊢
  omega

/-- `divCore a r m t none`, `v` in `t0` and `Wd` in `t6`: `[r]`'s first `v`
words := `X mod M`, for `X` `[a]`'s first `Wd` words and `M` `[m]`'s first
`v`, whose top word is not zero, and `[r]`'s first `v + 1` words zero; its
word `v` zero, the rest of `[r]` as it was, `[m]` and `[a]` unchanged, the
temporary `[t]` written. -/
theorem divCore_ok {s : State} {B : Addr} {Z w N a r m t v Wd : Nat} (h : Ws s B Z w N) (hN : N ≤ 2048)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (hra : r ≠ a) (hrm : r ≠ m) (hrt : r ≠ t) (hmt : m ≠ t)
    (hat : a ≠ t) (hv : 4 ≤ v) (hvw : v ≤ w) (hvW : v < Wd) (hWd : Wd ≤ w + 2) (hY : Wd - v ≤ 187)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 v) (ht6 : s.gpr .t6 = BitVec.ofNat 64 Wd)
    (hr0 : wordsVal s.mem B (arr w r) (v + 1) = 0) (hT : 0 < (word s.mem B (arr w m + 8 * (v - 1))).toNat) :
    WP isa (divCore a r m t none) s fun u => Ws u B Z w N ∧ Frame B w [r, t] [] s.mem u.mem ∧ Keep divWRegs s u ∧
      wordsVal u.mem B (arr w r) v = wordsVal s.mem B (arr w a) Wd % wordsVal s.mem B (arr w m) v ∧
      word u.mem B (arr w r + 8 * v) = 0 ∧
      wordsVal u.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) =
        wordsVal s.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) := by
  have fita := h.arr_fit ha
  have fitr := h.arr_fit hr
  have fitm := h.arr_fit hm
  have fitt := h.arr_fit ht
  have nw := h.nowrap
  have hS : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have drt := arr_disj (w := w) hrt
  have drm := arr_disj (w := w) hrm
  have dra := arr_disj (w := w) hra
  have dmt := arr_disj (w := w) hmt
  have dat := arr_disj (w := w) hat
  have hwl := h.wle
  have hc := div_counts hY
  generalize hX : wordsVal s.mem B (arr w a) Wd = X
  generalize hM : wordsVal s.mem B (arr w m) v = M
  have hM1 : 2 ^ (64 * (v - 1)) ≤ M := by
    have e := wordsVal_succ_top s.mem B (arr w m) (v - 1)
    rw [show v - 1 + 1 = v by omega, hM] at e
    have := Nat.le_mul_of_pos_right (2 ^ (64 * (v - 1))) hT
    omega
  simp only [divCore, VG.Impl.Rsa.RISCV64.Keys.seqs]
  -- The divisor normalized.
  refine WP.seq (WP.mono (wdPrep_ok h hm ht hN hmt hv hvw ht0 hT)
    fun u₁ ⟨h1, f1, k1, a7, a6, t0, a4, z, nm⟩ => ?_)
  rw [hM] at nm
  have t6 : u₁.gpr .t6 = BitVec.ofNat 64 Wd := (k1.gpr (by decide)).trans ht6
  have r1 : wordsVal u₁.mem B (arr w r) (v + 1) = 0 := by
    rw [f1.words (fun k hk => by simp at hk; subst hk; omega) (by simp) (by omega), hr0]
  have x1 : wordsVal u₁.mem B (arr w a) Wd = X := by
    rw [← hX, f1.words (fun k hk => by simp at hk; subst hk; omega) (by simp) (by omega)]
  have m1 : wordsVal u₁.mem B (arr w m) v = M := by
    rw [← hM, f1.words (fun k hk => by simp at hk; subst hk; omega) (by simp) (by omega)]
  -- `V := ⌊X / 2^o⌋`.
  refine WP.seq (WP.mono (divInit_ok h1 ha hr hN hra t0 t6 (by omega) hvW hWd hY r1)
    fun u₂ ⟨v2, a52, a22, a12, t12, o2, k2⟩ => ?_)
  rw [x1] at v2
  have h2 := h1.of_keep k2
  have g2 : ∀ q ∈ [Reg.a6, .a7, .t0, .a4], u₂.gpr q = u₁.gpr q := fun q hq => k2.gpr (by revert q hq; decide)
  have m2 : wordsVal u₂.mem B (arr w m) v = M := by rw [Outside.wordsVal o2 (by omega) (by omega), m1]
  have tw : ∀ j, j < 4 → word u₂.mem B (arr w t + 8 * j) = word u₁.mem B (arr w t + 8 * j) := fun j hj =>
    Outside.word o2 (by omega) (by omega)
  have nm2 := nm.congr (by simpa using tw 0 (by decide)) (tw 1 (by decide)) (tw 2 (by decide)) (tw 3 (by decide))
  have xa2 : wordsVal u₂.mem B (arr w a) Wd = X := by rw [Outside.wordsVal o2 (by omega) (by omega)]; exact x1
  -- The steps.
  generalize hSd : sOf v Wd = S at a12 t12 hc v2
  have hX0 : X / 2 ^ (63 * S) < 2 * M := by
    have hXl : X < 2 ^ (64 * Wd) := hX ▸ wordsVal_lt _ _ _ _
    have : X / 2 ^ (63 * S) < 2 ^ (64 * (v - 1)) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      exact Nat.lt_of_lt_of_le hXl (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  refine WP.seq (WP.mono (steps_ok (mid := chunk) (midRegs := chunkRegs) (X := X) (S := S) (z := z)
    (dV := arr w r) (dN := arr w m) (dT := arr w t)
    (Q := fun j u => u.gpr .t1 = BitVec.ofNat 64 (63 * (S - 1 - j)) ∧ u.gpr .a5 = off B (arr w a) ∧
      u.wr = u₂.wr ∧ Outside B (arr w r) (8 * (v + 1)) u₂.mem u.mem)
    h2.scr a22 ((g2 .a6 (by decide)).trans a6) ((g2 .a7 (by decide)).trans a7) ((g2 .t0 (by decide)).trans t0)
    ((g2 .a4 (by decide)).trans a4) a12 (by omega) (by omega) (by omega) (by omega) (arr_al w r) (arr_al w m)
    (arr_al w t) (by omega) (by omega) (by omega) (by omega) (by omega) nm2.hP nm2.hz (by rw [m2]; exact nm2.hd63)
    (by rw [m2]; exact nm2.hd) nm2.hv (by rw [m2]; exact nm2.hdl) (by rw [v2]) (by rw [m2]; exact hX0)
    ⟨by rw [t12, Nat.sub_zero], a52, rfl, Outside.refl _ _ _ _⟩
    (fun j u u' ⟨q1, q5, qw, qo⟩ ku ou => ⟨(ku.gpr (by decide)).trans q1, (ku.gpr (by decide)).trans q5,
      ku.2.2.trans qw, qo.trans ou⟩)
    (fun j hj u ⟨q1, q5, qw, qo⟩ => by
      have xa : wordsVal u.mem B (arr w a) Wd = X := by
        rw [Outside.wordsVal qo (by omega) (by omega)]; exact xa2
      refine WP.mono (chunk_ok (Wd := Wd) (h2.scr.congr qw) q1 q5 (by omega) (by omega) (by omega) xa)
        fun u' ⟨⟨c1, c6, cm⟩, ck⟩ => ⟨by rw [c6, show S - 1 - j - 1 = S - 2 - j by omega], cm, ck,
          by rw [c1, show S - 1 - j - 1 = S - 1 - (j + 1) by omega], (ck.gpr (by decide)).trans q5,
          ck.2.2.trans qw, by rw [cm]; exact qo⟩)
    (by decide)) fun u₃ ⟨⟨r3, hr3, hrm3, hV3, o3⟩, k3, _⟩ => ?_)
  rw [m2] at hr3 hrm3
  have h3 := h2.of_keep k3
  have g3 : ∀ q ∈ [Reg.a2, .a7, .t0, .a4], u₃.gpr q = u₂.gpr q := fun q hq => k3.gpr (by revert q hq; decide)
  have m3 : wordsVal u₃.mem B (arr w m) v = M := by rw [Outside.wordsVal o3 (by omega) (by omega), m2]
  -- `x := ⌊V / 2^63⌋ mod M`.
  refine WP.mono (finish_ok (dV := arr w r) (dN := arr w m) h3.scr ((g3 .a2 (by decide)).trans a22)
    ((g3 .a7 (by decide)).trans ((g2 .a7 (by decide)).trans a7))
    ((g3 .t0 (by decide)).trans ((g2 .t0 (by decide)).trans t0))
    ((g3 .a4 (by decide)).trans ((g2 .a4 (by decide)).trans a4)) (arr_al w r) (arr_al w m) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [hV3, m3]; exact hr3)) fun u ⟨⟨ux, u0, o4, _⟩, k4⟩ => ?_
  have o24 : Outside B (arr w r + 0) (8 * (v + 1)) u₁.mem u.mem := by
    have := (o2.trans o3).trans o4; simpa using this
  refine ⟨h3.of_keep k4, (f1.mono (js' := [r, t]) (ds' := [])).trans (Frame.of_arr (js := [r, t]) o24 (by omega)
    (by simp)), ?_, ?_, u0, ?_⟩
  · exact ((((k1.mono (rs' := divWRegs) (by decide)).trans (k2.mono (rs' := divWRegs) (by decide))).trans
      (k3.mono (rs' := divWRegs) (by decide))).trans (k4.mono (rs' := divWRegs) (by decide))).mono (by decide)
  · rw [ux, hV3, m3, hrm3]
  · rw [Outside.wordsVal ((o2.trans o3).trans o4) (by omega) (by omega),
      f1.words (fun k hk => by simp at hk; subst hk; omega) (by simp) (by omega)]

/-- `divW a r m t`: `[r]`'s first `v = w / 2` words := `[a] mod M`, for `M`
`[m]`'s first `v` words, whose top word is not zero, and `[r]`'s first `v + 1`
words zero; its word `v` zero, the rest of `[r]` as it was, `[m]` and `[a]`
unchanged, the temporary `[t]` written. -/
theorem divW_ok {s : State} {B : Addr} {Z w N a r m t : Nat} (h : Ws s B Z w N) (hN : N ≤ 2048) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hra : r ≠ a) (hrm : r ≠ m) (hrt : r ≠ t) (hmt : m ≠ t) (hat : a ≠ t)
    (hw : 8 ≤ w) (hw' : w ≤ 256) (hw2 : w % 2 = 0) (hr0 : wordsVal s.mem B (arr w r) (w / 2 + 1) = 0)
    (hT : 0 < (word s.mem B (arr w m + 8 * (w / 2 - 1))).toNat) :
    WP isa (divW a r m t) s fun u => Ws u B Z w N ∧ Frame B w [r, t] [] s.mem u.mem ∧ Keep divWRegs s u ∧
      wordsVal u.mem B (arr w r) (w / 2) = num s.mem B w a % wordsVal s.mem B (arr w m) (w / 2) ∧
      word u.mem B (arr w r + 8 * (w / 2)) = 0 ∧
      wordsVal u.mem B (arr w r + 8 * (w / 2 + 1)) (w - 1 - w / 2) =
        wordsVal s.mem B (arr w r + 8 * (w / 2 + 1)) (w - 1 - w / 2) := by
  unfold divW
  refine WP.seq (WP.mono (WP.keep [.t0, .t6] (Q := fun u => u.gpr .t0 = BitVec.ofNat 64 (w / 2) ∧
      u.gpr .t6 = BitVec.ofNat 64 w ∧ u.mem = s.mem)
    (by unfold halfW; brun [h.s9, srl1_ofNat (show w < 2 ^ 64 by omega), BitVec.add_zero]) (by rfl) (by rfl))
    fun u ⟨⟨u0, u6, um⟩, uk⟩ => ?_)
  have hu := h.of_keep uk
  refine WP.mono (divCore_ok hu hN ha hr hm ht hra hrm hrt hmt hat (by omega) (by omega) (by omega) (by omega)
    (by omega) u0 u6 (by rw [um]; exact hr0) (by rw [um]; exact hT)) fun t ⟨w1, f1, k1, v1, z1, r1⟩ => ?_
  rw [um] at f1 v1 r1
  exact ⟨w1, f1, ((uk.trans k1).mono (by decide)), v1, z1, r1⟩

/-- A factor of a balanced modulus: with `p q = n ≥ 2^(64 (w - 1))` and
`q < 2^(32 w)`, `p > 2^(32 w - 64)`, so that `p` and `p - 1` are numbers of
exactly `w / 2` words. -/
theorem balanced_lo {n p q k w : Nat} (hpq : p * q = n) (hn : 256 ^ (k - 1) ≤ n) (hkw : 8 * w ≤ k + 7)
    (hq : q < 2 ^ (32 * w)) (hw : 2 ≤ w) (hw2 : w % 2 = 0) : 2 ^ (64 * (w / 2 - 1)) < p := by
  have e1 : 64 * (w / 2 - 1) = 32 * w - 64 := by omega
  have e2 : (256 : Nat) ^ (k - 1) = 2 ^ (8 * (k - 1)) := by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  have hn' : 2 ^ (32 * w - 64 + 32 * w) ≤ n := by
    rw [e2] at hn
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hn
  rw [e1]
  refine Nat.lt_of_not_le fun hp => ?_
  have := Nat.mul_le_mul hp (Nat.le_of_lt hq)
  rw [← Nat.pow_add, hpq] at this
  have : p * q < 2 ^ (32 * w - 64) * 2 ^ (32 * w) := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0, Nat.zero_mul]; exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right q hp) (Nat.mul_lt_mul_of_pos_left hq (Nat.two_pow_pos _))
  rw [← Nat.pow_add, hpq] at this
  omega

/-- The first `v` of `w` words, for a number below `2^(64 v)`. -/
theorem words_low {m : Mem} {B : Addr} {d w v X : Nat} (hv : v ≤ w) (h : wordsVal m B d w = X)
    (hX : X < 2 ^ (64 * v)) : wordsVal m B d v = X := by
  have e := wordsVal_append m B d v (w - v)
  rw [show v + (w - v) = w by omega, h] at e
  have l := wordsVal_lt m B d v
  rcases Nat.eq_zero_or_pos (wordsVal m B (d + 8 * v) (w - v)) with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * v)) z
    omega

/-- The top word of a number of `v` words at least `2^(64 (v - 1))` is not zero. -/
theorem top_pos {m : Mem} {B : Addr} {d v : Nat} (hv : 1 ≤ v) (h : 2 ^ (64 * (v - 1)) ≤ wordsVal m B d v) :
    0 < (word m B (d + 8 * (v - 1))).toNat := by
  have e := wordsVal_succ_top m B d (v - 1)
  rw [show v - 1 + 1 = v by omega] at e
  have l := wordsVal_lt m B d (v - 1)
  rcases Nat.eq_zero_or_pos (word m B (d + 8 * (v - 1))).toNat with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; omega
  · exact z

/-- A number of `w` words from its first `v`, word `v` zero and the rest zero. -/
theorem num_of_low {m : Mem} {B : Addr} {d w v X : Nat} (hv : v < w) (hx : wordsVal m B d v = X)
    (ht : word m B (d + 8 * v) = 0) (hr : wordsVal m B (d + 8 * (v + 1)) (w - 1 - v) = 0) : wordsVal m B d w = X := by
  have e1 := wordsVal_append m B d v (w - v)
  have e2 := wordsVal_append m B (d + 8 * v) 1 (w - 1 - v)
  rw [show v + (w - v) = w by omega] at e1
  rw [show 1 + (w - 1 - v) = w - v by omega, show d + 8 * v + 8 * 1 = d + 8 * (v + 1) by omega, hr] at e2
  have w1 : wordsVal m B (d + 8 * v) 1 = 0 := by simp only [wordsVal, ht]; rfl
  rw [w1, Nat.mul_zero, Nat.add_zero] at e2
  rw [e1, e2, Nat.mul_zero, Nat.add_zero, hx]

theorem bv_or0 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx : x.toNat ||| y.toNat = 0 := by rw [← BitVec.toNat_or, h]; rfl
    rw [Nat.or_eq_zero_iff] at hx
    exact ⟨BitVec.eq_of_toNat_eq hx.1, BitVec.eq_of_toNat_eq hx.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem bv_and7 (x : BitVec 64) : (x &&& 7#64 = 0) ↔ x.toNat % 8 = 0 := by
  constructor
  · intro h
    have : (x &&& 7#64).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
    exact this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; exact h

theorem bv_xor0 (x y : BitVec 64) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h; have := congrArg (· ^^^ y) h; simpa [BitVec.xor_assoc] using this
  · rintro rfl; simp

theorem bv_lt_ite0 (x y : BitVec 64) : (if x < y then (1 : BitVec 64) else 0) = 0 ↔ ¬ x < y := by
  by_cases h : x < y <;> simp [h]

/-- `2^(64 (v - 1)) ≤ x < 2^(64 v)`, for `v = w / 2`: what the division by
words needs of its divisor to be exact. -/
abbrev InW (w x : Nat) : Prop := 2 ^ (64 * (w / 2 - 1)) ≤ x ∧ x < 2 ^ (64 * (w / 2))

end VG.Proof.Rsa.RISCV64.Keys
