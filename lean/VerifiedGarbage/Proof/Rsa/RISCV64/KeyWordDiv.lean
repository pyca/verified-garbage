module

public import VerifiedGarbage.Impl.Rsa.RISCV64.WordDiv
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2Words
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Division by words for the RSA key operations on RISC-V

`WordDiv.divW a r m t`, on the working space of `Proof/Rsa/RISCV64/KeyLayout.lean`
(`w` words, `w` even, `v = w / 2` the divisor's words):

* `fixTop_ok`: `[m]`'s top word (`v - 1`) plus 1 if it is zero;
* `wdPrep_ok`: the divisor normalized and its reciprocal in the temporary
  (`Precompute.lz`, `normTail`, `recip`, at the arrays' offsets);
* `divW_ok`: `[r]`'s first `v` words `:=` `[a] mod [m]`'s, for `[r]`'s first
  `v + 1` words zero and `[m]`'s top word not zero, by `w` word steps
  (`PreR2Words.wordStepU_ok`) over `[a]`'s words, most significant first
  (`WordStep.wordDiv_step`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr)
open VG.Impl.Rsa.RISCV64.WordDiv (halfW fixTop normSetup stepsSetup step prep divW)
open VG.Impl.Bignum.RISCV64.Precompute (lz normTail recip wordStepU)

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

/-- `prep m t`: the divisor `[m]` (`v = w / 2` words, its top word not zero)
normalized and its reciprocal, in `[t]`'s first four words; `a7`, `a6` and
`t0` its address, the temporary's and `v`, and `a4` zero. -/
theorem wdPrep_ok {s : State} {B : Addr} {Z w N m t : Nat} (h : Ws s B Z w N) (hm : m < N) (ht : t < N)
    (hN : N ≤ 2048) (hmt : m ≠ t) (hw : 8 ≤ w)
    (hT : 0 < (word s.mem B (arr w m + 8 * (w / 2 - 1))).toNat) :
    WP isa (prep m t) s fun u => Ws u B Z w N ∧ Frame B w [t] [] s.mem u.mem ∧ Keep prepRegs s u ∧
      u.gpr .a7 = off B (arr w m) ∧ u.gpr .a6 = off B (arr w t) ∧ u.gpr .t0 = BitVec.ofNat 64 (w / 2) ∧
      u.gpr .a4 = 0 ∧ ∃ z, Norm u.mem B (arr w t) (wordsVal s.mem B (arr w m) (w / 2)) (w / 2) z := by
  have fitm := h.arr_fit hm
  have fitt := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have dmt := arr_disj (w := w) hmt
  unfold prep
  simp only [VG.Impl.Rsa.RISCV64.Keys.seqs]
  generalize hM : wordsVal s.mem B (arr w m) (w / 2) = M
  -- The pointers and `v`.
  refine WP.seq ?_
  rw [normSetup, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (show m < 2048 by omega) ?_
  have h1 : Ws (s.write .a7 (off B (arr w m))) B Z w N := h.of_keep (Keep.write _ _ _)
  refine ptr_ok h1 (by decide) (by decide) (show t < 2048 by omega) ?_
  generalize hs₁ : (s.write .a7 (off B (arr w m))).write .a6 (off B (arr w t)) = s₁
  have k1 : Keep [.a7, .a6] s s₁ := by
    rw [← hs₁]; exact ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono (by decide)
  have g7 : s₁.gpr .a7 = off B (arr w m) := by rw [← hs₁]; simp [gpr_write]
  have g6 : s₁.gpr .a6 = off B (arr w t) := by rw [← hs₁]; simp [gpr_write]
  have g9 : s₁.gpr .s9 = BitVec.ofNat 64 w := (k1.gpr (by decide)).trans h.s9
  refine WP.mono (WP.keep [.t0] (Q := fun u => u.gpr .t0 = BitVec.ofNat 64 (w / 2) ∧ u.mem = s₁.mem)
    (by unfold halfW; brun [g9, srl1_ofNat (show w < 2 ^ 64 by omega)]) (by rfl) (by rfl))
    fun s₂ ⟨⟨e0, m2⟩, k2⟩ => ?_
  have k12 : Keep [.a7, .a6, .t0] s s₂ := (k1.trans k2).mono (by decide)
  have m2' : s₂.mem = s.mem := by rw [m2, ← hs₁]; rfl
  have h2 : Ws s₂ B Z w N := h.of_keep k12
  have g27 : s₂.gpr .a7 = off B (arr w m) := (k2.gpr (by decide)).trans g7
  have g26 : s₂.gpr .a6 = off B (arr w t) := (k2.gpr (by decide)).trans g6
  -- `z`.
  refine WP.seq (WP.mono (lz_ok (dN := arr w m) (w := w / 2) h2.scr g27 e0 (by omega) (arr_al w m) (by omega)
    (by rw [m2']; exact hT)) fun s₃ ⟨⟨z1, zb1, zb2, m3⟩, k3⟩ => ?_)
  rw [m2'] at z1 zb1 zb2
  have h3 : Ws s₃ B Z w N := h2.of_keep k3
  have g3 : ∀ r ∈ [Reg.a7, .a6, .t0], s₃.gpr r = s₂.gpr r := fun r hr => k3.gpr (by revert r hr; decide)
  -- `P`, `d'` and `d'ₗ`.
  refine WP.seq (WP.mono (normTail_ok (dN := arr w m) (dT := arr w t) (w := w / 2) h3.scr
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
  refine ⟨zOf (word s.mem B (arr w m + 8 * (w / 2 - 1))).toNat, by rw [w0]; exact n0, nz, nd63,
    by rw [w8]; exact nd, by rw [rv, w8, n2], by rw [w8, w24]; exact ndl⟩

/-- The registers `divW` writes. -/
abbrev divWRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a6, .a7, .t0, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

theorem ea_top2 (B : Addr) {d w c : Nat} (hc : c ≤ 8 * w) (hn : B.toNat + d + 8 * w < 2 ^ 64) :
    off B d + BitVec.ofNat 64 w <<< 3 - BitVec.ofNat 64 c = off B (d + 8 * w - c) := by
  rw [BitVec.add_comm]; exact ea_top B hc hn

/-- `stepsSetup a r`: `a2`, `t2` and `a1`. -/
theorem stepsSetup_ok {s : State} {B : Addr} {Z w N a r : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hN : N ≤ 2048) :
    WP isa (.block (stepsSetup a r)) s fun u => u.gpr .a2 = off B (arr w r) ∧
      u.gpr .t2 = off B (arr w a + 8 * (w - 1)) ∧ u.gpr .a1 = BitVec.ofNat 64 w ∧ u.mem = s.mem ∧
      Keep [.a2, .t2, .t3, .a1] s u := by
  have fita := h.arr_fit ha
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have hw0 := h.wpos
  rw [stepsSetup, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (show r < 2048 by omega) ?_
  have h1 : Ws (s.write .a2 (off B (arr w r))) B Z w N := h.of_keep (Keep.write _ _ _)
  refine ptr_ok h1 (by decide) (by decide) (show a < 2048 by omega) ?_
  have ea := ea_top2 B (d := arr w a) (w := w) (c := 8) (by omega) (by omega)
  rw [show arr w a + 8 * w - 8 = arr w a + 8 * (w - 1) by omega] at ea
  refine WP.mono (WP.keep [.t3, .t2, .a1] (Q := fun u => u.gpr .t2 = off B (arr w a + 8 * (w - 1)) ∧
      u.gpr .a1 = BitVec.ofNat 64 w ∧ u.mem = s.mem) (by brun [h.s9, ea, BitVec.add_zero]) (by rfl) (by rfl))
    fun u ⟨⟨u2, u1, um⟩, k⟩ => ⟨?_, u2, u1, um, ((Keep.write _ _ _).trans ((Keep.write _ _ _).trans k)).mono
      (by decide)⟩
  rw [k.gpr (by decide)]; simp [gpr_write]

/-- What the word steps keep, after `i` of them: `[r]`'s first `v` words
`⌊X / 2^(64 (w - i))⌋ mod M`, for `X = [a]` and `M = [m]`'s first `v` words. -/
structure DivI (s : State) (B : Addr) (Z w N a r m t z : Nat) (i : Nat) (u : State) : Prop where
  ws : Ws u B Z w N
  fr : Frame B w [r, t] [] s.mem u.mem
  k : Keep divWRegs s u
  a2 : u.gpr .a2 = off B (arr w r)
  a6 : u.gpr .a6 = off B (arr w t)
  a7 : u.gpr .a7 = off B (arr w m)
  t0 : u.gpr .t0 = BitVec.ofNat 64 (w / 2)
  a4 : u.gpr .a4 = 0
  t2 : i < w → u.gpr .t2 = off B (arr w a + 8 * (w - 1 - i))
  nm : Norm u.mem B (arr w t) (wordsVal s.mem B (arr w m) (w / 2)) (w / 2) z
  x : wordsVal u.mem B (arr w r) (w / 2) =
    num s.mem B w a / 2 ^ (64 * (w - i)) % wordsVal s.mem B (arr w m) (w / 2)
  hi : wordsVal u.mem B (arr w r + 8 * (w / 2 + 1)) (w - 1 - w / 2) =
    wordsVal s.mem B (arr w r + 8 * (w / 2 + 1)) (w - 1 - w / 2)
  top : i = 0 ∨ word u.mem B (arr w r + 8 * (w / 2)) = 0

theorem off_sub8 (B : Addr) {d : Nat} (h : 8 ≤ d) : off B d - BitVec.ofNat 64 8 = off B (d - 8) := off_sub B h

/-- A step of `divW`. -/
theorem wdStep_ok {s : State} {B : Addr} {Z w N a r m t z : Nat} (ha : a < N) (hr : r < N)
    (hm : m < N) (ht : t < N) (hra : r ≠ a) (hrm : r ≠ m) (hrt : r ≠ t) (hmt : m ≠ t) (hat : a ≠ t)
    (hw : 8 ≤ w) (hw2 : w % 2 = 0) {i : Nat} (hi : i < w) {u : State} (I : DivI s B Z w N a r m t z i u) :
    WP isa step u fun u' => DivI s B Z w N a r m t z (i + 1) u' ∧ u'.gpr .a1 = u.gpr .a1 - BitVec.ofNat 64 1 := by
  have fita := I.ws.arr_fit ha
  have fitr := I.ws.arr_fit hr
  have fitm := I.ws.arr_fit hm
  have fitt := I.ws.arr_fit ht
  have nw := I.ws.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := I.ws.wle
  have drm := arr_disj (w := w) hrm
  have nm := I.nm
  have eM : wordsVal u.mem B (arr w m) (w / 2) = wordsVal s.mem B (arr w m) (w / 2) :=
    I.fr.words (fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · have := arr_disj (w := w) hrm; omega
      · have := arr_disj (w := w) hmt; omega) (by simp) (by omega)
  have eU : word u.mem B (arr w a + 8 * (w - 1 - i)) = word s.mem B (arr w a + 8 * (w - 1 - i)) :=
    I.fr.word (by omega) (by simp; exact ⟨hra, hat.symm⟩) (by simp) (by omega)
  unfold step
  refine WP.seq (WP.mono (wordStepU_ok (dX := arr w r) (dN := arr w m) (dT := arr w t)
    (dU := arr w a + 8 * (w - 1 - i)) (w := w / 2) (z := z) I.ws.scr I.a2 I.a6 I.a7 (I.t2 hi) I.t0 I.a4 (by omega)
    (by omega) (arr_al w r) (arr_al w m) (arr_al w t) (by have := arr_al w a; omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) nm.hP nm.hz (by rw [eM]; exact nm.hd63) (by rw [eM]; exact nm.hd) nm.hv
    (by rw [eM]; exact nm.hdl) (by rw [I.x, eM]; exact Nat.mod_lt _ (by
      have := nm.hd63
      rcases Nat.eq_zero_or_pos (wordsVal s.mem B (arr w m) (w / 2)) with e | e
      · rw [e, Nat.zero_mul, Nat.zero_div] at this; omega
      · exact e)))
    fun u₁ ⟨⟨x1, top1, o1⟩, k1⟩ => ?_)
  have o1' : Outside B (arr w r + 0) (8 * (w / 2 + 1)) u.mem u₁.mem := fun x hx => o1 x (by simpa using hx)
  have f1 : Frame B w [r, t] [] u.mem u₁.mem := Frame.of_arr o1' (by omega) (by simp)
  have g1 : ∀ q ∈ [Reg.a2, .a6, .a7, .t0, .a4, .t2, .a1], u₁.gpr q = u.gpr q := fun q hq =>
    k1.gpr (by revert q hq; decide)
  refine WP.mono (WP.keep [.t2, .a1] (Q := fun u' => u'.gpr .t2 = u₁.gpr .t2 - BitVec.ofNat 64 8 ∧
      u'.gpr .a1 = u₁.gpr .a1 - BitVec.ofNat 64 1 ∧ u'.mem = u₁.mem) (by brun) (by rfl) (by rfl))
    fun u' ⟨⟨e2, e1, em⟩, k2⟩ => ⟨?_, by rw [e1, g1 _ (by decide)]⟩
  have g2 : ∀ q ∈ [Reg.a2, .a6, .a7, .t0, .a4], u'.gpr q = u.gpr q := fun q hq =>
    (k2.gpr (by revert q hq; decide)).trans (g1 q (by revert q hq; decide))
  have kk : Keep divWRegs s u' := ((I.k.trans k1).trans k2).mono (by decide)
  have tw : ∀ j, j < 4 → word u'.mem B (arr w t + 8 * j) = word u.mem B (arr w t + 8 * j) := fun j hj => by
    rw [em]; exact o1.word (by have := arr_disj (w := w) hrt; omega) (by omega)
  refine ⟨I.ws.of_keep ((k1.trans k2).mono (rs' := divWRegs) (by decide)), I.fr.trans (by rw [em]; exact f1), kk,
    (g2 _ (by decide)).trans I.a2, (g2 _ (by decide)).trans I.a6, (g2 _ (by decide)).trans I.a7,
    (g2 _ (by decide)).trans I.t0, (g2 _ (by decide)).trans I.a4, fun hi' => ?_,
    nm.congr (by simpa using tw 0 (by decide)) (tw 1 (by decide)) (tw 2 (by decide)) (tw 3 (by decide)), ?_, ?_,
    .inr (by rw [em]; exact top1)⟩
  · rw [e2, g1 _ (by decide), I.t2 hi, off_sub8 B (by omega)]
    congr 1; omega
  · rw [em, x1, I.x, eM, eU]
    have hd := wordsVal_word (m := s.mem) (base := B) (o := arr w a) (n := w) (j := w - 1 - i) (by omega)
    exact VG.Proof.Bignum.WordStep.wordDiv_step' (W := 64) (n := w - 1 - i)
      (by rw [show w - 1 - i + 1 = w - i by omega]) hd.symm |>.trans (by rw [show w - 1 - i = w - (i + 1) by omega])
  · rw [em, ← I.hi]
    exact VG.Proof.Mont.Outside.wordsVal o1 (by omega) (by omega)


/-- `divW a r m t`: `[r]`'s first `v = w / 2` words := `[a] mod M`, for `M`
`[m]`'s first `v` words, whose top word is not zero, and `[r]` zero; its
word `v` zero, the rest of `[r]` as it was, `[m]` and `[a]` unchanged, the
temporary `[t]` written. -/
theorem divW_ok {s : State} {B : Addr} {Z w N a r m t : Nat} (h : Ws s B Z w N) (hN : N ≤ 2048) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hra : r ≠ a) (hrm : r ≠ m) (hrt : r ≠ t) (hmt : m ≠ t) (hat : a ≠ t)
    (hw : 8 ≤ w) (hw2 : w % 2 = 0) (hr0 : wordsVal s.mem B (arr w r) (w / 2) = 0)
    (hT : 0 < (word s.mem B (arr w m + 8 * (w / 2 - 1))).toNat) :
    WP isa (divW a r m t) s fun u => Ws u B Z w N ∧ Frame B w [r, t] [] s.mem u.mem ∧ Keep divWRegs s u ∧
      wordsVal u.mem B (arr w r) (w / 2) = num s.mem B w a % wordsVal s.mem B (arr w m) (w / 2) ∧
      word u.mem B (arr w r + 8 * (w / 2)) = 0 ∧
      wordsVal u.mem B (arr w r + 8 * (w / 2 + 1)) (w - 1 - w / 2) =
        wordsVal s.mem B (arr w r + 8 * (w / 2 + 1)) (w - 1 - w / 2) := by
  have fitr := h.arr_fit hr
  have fitt := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  unfold divW
  simp only [VG.Impl.Rsa.RISCV64.Keys.seqs]
  refine WP.seq (WP.mono (wdPrep_ok h hm ht hN hmt (by omega) hT) fun u₁ ⟨h1, f1, k1, a7, a6, t0, a4, z, nm⟩ => ?_)
  refine WP.seq (WP.mono (stepsSetup_ok h1 ha hr hN) fun u₂ ⟨a2, t2, a1, m2, k2⟩ => ?_)
  have g2 : ∀ q ∈ [Reg.a6, .a7, .t0, .a4], u₂.gpr q = u₁.gpr q := fun q hq => k2.gpr (by revert q hq; decide)
  have hX : num s.mem B w a < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
  have I0 : DivI s B Z w N a r m t z 0 u₂ := by
    have rr : wordsVal u₂.mem B (arr w r) (w / 2) = 0 := by
      rw [m2, f1.words (fun k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rw [hk]; have := arr_disj (w := w) hrt; omega) (by simp) (by omega), hr0]
    refine ⟨h1.of_keep k2, by rw [m2]; exact f1.mono, (k1.trans k2).mono (rs' := divWRegs) (by decide), a2,
      (g2 _ (by decide)).trans a6, (g2 _ (by decide)).trans a7, (g2 _ (by decide)).trans t0,
      (g2 _ (by decide)).trans a4, fun _ => by rw [t2]; congr 1, by rw [m2]; exact nm, ?_, ?_, .inl rfl⟩
    · rw [rr, Nat.sub_zero, Nat.div_eq_of_lt hX, Nat.zero_mod]
    · rw [m2]
      exact f1.words (fun k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rw [hk]; have := arr_disj (w := w) hrt; omega) (by simp) (by omega)
  refine WP.mono (wp_countdown (cnt := .a1) (N := w) (by omega) (by omega) (DivI s B Z w N a r m t z)
    (fun i hi u I _ => wdStep_ok ha hr hm ht hra hrm hrt hmt hat hw hw2 hi I) I0 a1) fun u I => ?_
  refine ⟨I.ws, I.fr, I.k, by rw [I.x, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one],
    I.top.resolve_left (by omega), I.hi⟩


end VG.Proof.Rsa.RISCV64.Keys
