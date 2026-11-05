module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Rows
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Digit
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Scalar
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the cached attempt's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's comb on RISC-V

`step_ok`: a row of the comb, a square, the digit's entry and a product.
`comb_ok`: `g^x mod p` from the context's rows. -/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Win (WCtx WinO A arr_eq arr1 arrO slot_lt win_of_arrays)
open VG.Proof.Bignum (slot slot_sep Arrays)

/-- `g^E R mod p`, in Montgomery form. -/
abbrev combM (G P w E : Nat) : Nat := Spec.Rsa.powMod G E P * 2 ^ (64 * w) % P

theorem combM_lt {G P w : Nat} (hP : 0 < P) (E : Nat) : combM G P w E < P := Nat.mod_lt _ hP

/-- A change of arrays 1 to 23 keeps the context. -/
theorem win_ctx {B C : Addr} {Z w n : Nat} {m m' : Mem} (h : WinO B w m m') (hZ : slot w 24 ≤ Z)
    (hsep : ∀ x, ofs C x < n → Z ≤ ofs B x) : Outside C n (2 ^ 64) m m' :=
  ctx_of_scr h (by have := Win.slot24 w; omega_arith) hsep

/-- x's octets, apart from the working space, are kept by a change of
arrays 1 to 23. -/
theorem win_byte {B X : Addr} {Z w n : Nat} {m m' : Mem} (h : WinO B w m m') (hZ : slot w 24 ≤ Z)
    (hsep : ∀ y, ofs B y < Z → off X n ≠ y) : m' (off X n) = m (off X n) :=
  h _ (Or.inr (by
    have := Win.slot24 w
    show slot w 1 + 23 * (8 * (w + 2)) ≤ (off X n - B).toNat
    by_cases hl : (off X n - B).toNat < Z
    · exact absurd rfl (hsep _ hl)
    · omega_arith))

/-- The registers a row writes. -/
def stepRegs : List Reg := Pub.montRegs ++ digitRegs ++ selERegs ++ [.s9]

/-- The comb with `n` rows left (`s9`), from `s₀`, the accumulator (array 6)
`Acc`; the context at `C` (`s10`), x's octets at `X` (`s8`). -/
structure CS (s₀ : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits n Acc : Nat) (u : State) :
    Prop where
  win : WCtx u B Z w P
  h10 : u.gpr .s10 = C
  ctx : CtxRd u B Z C w
  ents : ∀ a < 32, ent u.mem C w a = combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)
  h9 : u.gpr .s9 = BitVec.ofNat 64 n
  xc : XCtx u X xb (Spec.Rsa.FixedBaseComb.rows bits)
  xsep : ∀ n < xb.length, ∀ y, ofs B y < Z → off X n ≠ y
  acc : A u.mem B w 6 = Acc
  one : A u.mem B w 7 = 1
  out : WinO B w s₀.mem u.mem
  keep : Keep stepRegs s₀ u

/-- `CS` after a change of arrays 1 to 23 but 7, and registers of a row
but `s9`. -/
theorem CS.frame {s₀ u v : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n Acc n' Acc' : Nat}
    (h : CS s₀ B C X Z w xb P G bits n Acc u) {rs : List Reg} (ho : WinO B w u.mem v.mem)
    (h7 : A v.mem B w 7 = A u.mem B w 7) (k : Keep rs u v) (hrs : ∀ r ∈ rs, r ∈ stepRegs := by decide)
    (h9 : v.gpr .s9 = BitVec.ofNat 64 n') (hacc : A v.mem B w 6 = Acc') :
    CS s₀ B C X Z w xb P G bits n' Acc' v := by
  have hZ := h.win.hZ
  have hg : ∀ r ∈ ([.s10, .s11, .s7, .s8, .a7, .s5, .t0, .t1] : List Reg), r ∉ stepRegs := by decide
  have g : ∀ r ∈ ([.s10, .s11, .s7, .s8, .a7, .s5, .t0, .t1] : List Reg), v.gpr r = u.gpr r :=
    fun r hr => k.gpr fun h' => hg r hr (hrs r h')
  have hc' : ∀ r ∈ Win.ctxRegs, r ∉ stepRegs := by decide
  have hctx : Outside C (8 * ctxWords w) (2 ^ 64) u.mem v.mem := win_ctx ho hZ h.ctx.sep
  refine ⟨h.win.of k (fun r hr h' => hc' r hr (hrs r h')) ho, (g .s10 (by decide)).trans h.h10,
    h.ctx.congr k.2.1 k.2.2, fun a ha => by rw [ent_keep hctx h.ctx.hn ha]; exact h.ents a ha, h9,
    ⟨(g .s11 (by decide)).trans h.xc.h11, (g .s7 (by decide)).trans h.xc.h7, (g .s8 (by decide)).trans h.xc.h8,
      fun n hn => by rw [k.2.1, k.2.2]; exact h.xc.hrd n hn,
      fun n hn => by rw [win_byte ho hZ (h.xsep n hn)]; exact h.xc.hval n hn, h.xc.hL⟩,
    h.xsep, hacc, by rw [h7]; exact h.one, Outside.trans h.out ho,
    (h.keep.trans k).mono (fun r hr => by
      simp only [List.mem_append] at hr; rcases hr with hr | hr
      · exact hr
      · exact hrs r hr)⟩

/-- What a row needs besides `CS`. -/
structure RowP (P bits : Nat) : Prop where
  odd : P % 2 = 1
  one : 1 < P
  rows : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639

/-- One row: from `n + 1` rows left to `n`. -/
theorem step_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n : Nat} (hq : RowP P bits)
    (h : CS s₀ B C X Z w xb P G bits (n + 1)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (n + 1))) u)
    (hn : n < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa step u fun v =>
      CS s₀ B C X Z w xb P G bits n (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) n)) v := by
  have hZ := h.win.hZ
  have hnw := h.win.nw
  have hP : 0 < P := by have := hq.one; omega_arith
  have cop := VG.Proof.Bignum.coprime_pow2 hq.odd (64 * w)
  have h1 := hq.rows
  generalize hx : Spec.Rsa.os2ip xb = x at h ⊢
  unfold step
  simp only [seqs]
  -- The square.
  refine WP.seq (WP.mono (h.win.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h.acc]; exact combM_lt hP _))
    fun u₁ ⟨⟨_, lt1, eq1, fr1, o1⟩, k1⟩ => ?_)
  rw [h.acc] at eq1
  have a1 := Rsa.FixedBaseComb.mont_square_encoded cop lt1 rfl eq1
  have c1 := h.frame o1 (fr1 7 (by decide) (by decide) (by decide) (by decide)) k1 (by decide)
    (by rw [k1.gpr (by decide)]; exact h.h9) a1
  -- The digit.
  refine WP.seq (WP.mono (digit_ok c1.xc c1.h9 (by omega_arith)) fun u₂ ⟨⟨a2, m2⟩, k2⟩ => ?_)
  rw [hx, combDigit_eq] at a2
  have hd := Rsa.FixedBaseComb.digit_lt bits x n
  have c2 := c1.frame (Acc' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1)))
    (by rw [m2]; exact Outside.refl _ _ _ _) (by rw [m2]) k2 (by decide) (by rw [k2.gpr (by decide)]; exact c1.h9)
    (by rw [m2]; exact c1.acc)
  -- The entry.
  refine WP.seq (WP.mono (select_ok c2.win c2.ctx c2.h10 a2 hd) fun u₃ ⟨⟨a3, o3⟩, k3⟩ => ?_)
  rw [c2.ents _ hd] at a3
  have c3 := c2.frame (Acc' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1)))
    (win_of_arrays o3 (by simp)) (arr_eq o3 (by decide) (by simp) hnw) k3 (by decide)
    (by rw [k3.gpr (by decide)]; exact c2.h9) (by rw [arr_eq o3 (by decide) (by simp) hnw]; exact c2.acc)
  -- The product.
  refine WP.seq (WP.mono (c3.win.mont (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [a3]; exact combM_lt hP _))
    fun u₄ ⟨⟨_, lt4, eq4, fr4, o4⟩, k4⟩ => ?_)
  rw [c3.acc, a3] at eq4
  have a4 := Rsa.FixedBaseComb.mont_product_encoded cop lt4 rfl rfl eq4
  rw [← Rsa.FixedBaseComb.high_step bits x n hn] at a4
  have c4 := c3.frame o4 (fr4 7 (by decide) (by decide) (by decide) (by decide)) k4 (by decide)
    (by rw [k4.gpr (by decide)]; exact c3.h9) a4
  -- `n` rows left.
  refine WP.mono (WP.keep [.s9] (Q := fun v => v.gpr .s9 = BitVec.ofNat 64 n ∧ v.mem = u₄.mem) (by
    brun [c4.h9, exec_addi_neg_lit (show 1 ≤ 2048 by decide),
      ofNat_sub'' (show 1 ≤ n + 1 by omega_arith) (show n + 1 < 2 ^ 64 by omega_arith), Nat.add_sub_cancel])
    (by rfl) (by rfl)) fun v ⟨⟨a5, m5⟩, k5⟩ => ?_
  exact c4.frame (by rw [m5]; exact Outside.refl _ _ _ _) (by rw [m5]) k5 (by decide) a5 (by rw [m5]; exact c4.acc)

/-- The rows, from `rows` left, by `wp_countdown` on `s9`. -/
theorem rows_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat} (hq : RowP P bits)
    (h : CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) u)
    (hpos : 0 < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa (.loop step (.nonzero .s9)) u
      (CS s₀ B C X Z w xb P G bits 0 (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0))) := by
  have h1 := hq.rows
  refine WP.mono (wp_countdown (body := step) (cnt := .s9) (N := Spec.Rsa.FixedBaseComb.rows bits)
    (by omega_arith) hpos
    (fun i v => CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits - i)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits - i))) v)
    (fun i hi v hv hc => ?_) (by simpa using h) h.h9) fun v hv => by simpa using hv
  have e : Spec.Rsa.FixedBaseComb.rows bits - i = Spec.Rsa.FixedBaseComb.rows bits - (i + 1) + 1 := by omega_arith
  rw [e] at hv hc
  refine WP.mono (step_ok hq hv (by omega_arith)) fun v' hv' => ⟨hv', ?_⟩
  rw [hv'.h9, hc, ofNat_sub'' (by omega_arith) (by omega_arith), Nat.add_sub_cancel]

/-! ## The comb -/

/-- What the comb needs: the working space with p in array 0, the context
(its address in the header's word 4) and its entries, x's octets (at `a5`)
and the header's row count. -/
structure CombIn (s : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits : Nat) : Prop where
  scr : Scr s B Z
  w2 : 2 ≤ w
  w31 : w < 2 ^ 31
  hZ : slot w 24 ≤ Z
  a7 : s.gpr .a7 = off B (slot w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 w
  s6 : s.gpr .s6 = B
  hX : word s.mem B 8 = X
  s11 : s.gpr .s11 = BitVec.ofNat 64 xb.length
  hC : word s.mem B 32 = C
  hRw : word s.mem B 56 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  ctx : CtxRd s B Z C w
  ents : ∀ a < 32, ent s.mem C w a = combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)
  r2 : wordsVal s.mem C (rowOff w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % P
  hp : A s.mem B w 0 = P
  xrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1
  xsep : ∀ n < xb.length, ∀ y, ofs B y < Z → off X n ≠ y
  xval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]
  hL : 8 * xb.length < 2 ^ 31
  row : RowP P bits
  pos : 0 < bits

/-- The registers the comb writes. -/
def combRegs : List Reg := [.s10, .s8, .s7, .t2, .s0, .s1, .s2, .s3, .t1, .t3, .t4, .t5, .s9] ++ stepRegs

/-- `headBlock`: the context, x's address, the rows, and `t2 := 1`. -/
theorem head_ok {s : State} {B C X : Addr} {Z rows : Nat} (hs : Scr s B Z) (hZ : 64 ≤ Z) (h6 : s.gpr .s6 = B)
    (hX : word s.mem B 8 = X) (hC : word s.mem B 32 = C) (hRw : word s.mem B 56 = BitVec.ofNat 64 rows) :
    WP isa (.block headBlock) s fun u => (u.gpr .s10 = C ∧ u.gpr .s8 = X ∧
      u.gpr .s7 = BitVec.ofNat 64 rows ∧ u.gpr .t2 = BitVec.ofNat 64 1 ∧ u.mem = s.mem) ∧
      Keep [.s10, .s8, .s7, .t2] s u := by
  have h6' : s.gpr .s6 = off B 0 := by rw [h6]; simp [off]
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold headBlock hCtx hRows
  brun [h6', hs.ld (d := 32) (n := 8) (by omega_arith), hs.ld (d := 56) (n := 8) (by omega_arith),
    hs.ld (d := 8) (n := 8) (by omega_arith), hs.al8 (d := 8) (by omega_arith) (by decide),
    hs.al8 (d := 32) (by omega_arith) (by decide), hs.al8 (d := 56) (by omega_arith) (by decide),
    show (s.mem.readW (off B 32) 64) = C from hC, show s.mem.readW (off B 56) 64 = BitVec.ofNat 64 rows from hRw,
    show (s.mem.readW (off B 8) 64) = X from hX,
    Pub.pub_li1, BitVec.add_zero]

theorem low_odd {m : Mem} {B : Addr} {d w P : Nat} (hw : 1 ≤ w) (h : wordsVal m B d w = P) (hodd : P % 2 = 1) :
    (word m B d).toNat % 2 = 1 := by
  rw [fios_wordsVal_pred _ _ _ hw] at h
  omega_arith

theorem combRest_ok {s s₁ : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat}
    (h : CombIn s B C X Z w xb P G bits) (a10 : s₁.gpr .s10 = C) (a8 : s₁.gpr .s8 = X)
    (a7 : s₁.gpr .s7 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)) (a2 : s₁.gpr .t2 = BitVec.ofNat 64 1)
    (m1 : s₁.mem = s.mem) (k1 : Keep [.s10, .s8, .s7, .t2] s s₁) :
    WP isa combRest s₁ fun t =>
      (A t.mem B w 4 = Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P ∧
        A t.mem B w 0 = P ∧ WinO B w s.mem t.mem) ∧ Keep combRegs s t := by
  have hZ := h.hZ
  have hnw : B.toNat + slot w 24 ≤ 2 ^ 64 := by have := h.scr.nowrap; omega_arith
  have hw := h.w2; have hw' := h.w31
  have hq := h.row
  have hP : 0 < P := by have := hq.one; omega_arith
  have cop := VG.Proof.Bignum.coprime_pow2 hq.odd (64 * w)
  have h256 : 256 ≤ Z := by
    have : slot w 24 = 256 + 24 * (8 * (w + 2)) := rfl
    omega_arith
  have h0 : slot w 0 + 8 ≤ Z := by
    have : slot w 24 = 256 + 24 * (8 * (w + 2)) := rfl
    have : slot w 0 = 256 := by simp [slot, hdrBytes]
    omega_arith
  unfold combRest
  simp only [seqs]
  -- `-p⁻¹ mod 2⁶⁴`.
  refine WP.seq (WP.mono (minv_ok (h.scr.congr k1.2.2) ((k1.gpr (by decide)).trans h.a7) (slot_al w 0)
    (by omega_arith) (by rw [m1]; exact low_odd (by omega_arith) h.hp hq.odd)) fun s₂ ⟨⟨inv2, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have c2 : WCtx s₂ B Z w P := ⟨h.scr.congr k12.2.2, hw, hw', hZ, (k12.gpr (by decide)).trans h.a7,
    (k12.gpr (by decide)).trans h.s5, (k12.gpr (by decide)).trans h.t0, by rw [m2]; exact inv2,
    by rw [hm2]; exact h.hp⟩
  have hc2 : CtxRd s₂ B Z C w := h.ctx.congr k12.2.1 k12.2.2
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (loadRow_ok (a := 1) (j := 1) c2 hc2 ((k2.gpr (by decide)).trans a10)
    ((k2.gpr (by decide)).trans a2) (by decide) (by decide)) fun s₃ ⟨⟨r3, o3⟩, k3⟩ => ?_)
  rw [hm2, h.r2] at r3
  have c3 := c2.of k3 (by decide) (arrO o3 (by decide) (by decide))
  -- 1 in array 7.
  have h8 := slot_lt (w := w) (show 8 < 24 by decide)
  refine WP.seq (WP.mono (Pub.oneP_ok c3.scr (by omega_arith) hw' (by omega_arith) c3.a7 c3.s5 c3.t0)
    fun s₄ ⟨⟨one4, o4⟩, k4⟩ => ?_)
  have c4 := c3.of k4 (by decide) (arrO o4 (by decide) (by decide))
  have r4 : A s₄.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by rw [Win.arr_out o4 (by decide) (by decide) hnw]; exact r3
  -- Montgomery one in array 6.
  refine WP.seq (WP.mono (c4.mont (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [show A s₄.mem B w 7 = 1 from one4]; exact hq.one))
    fun s₅ ⟨⟨c5, lt5, eq5, fr5, o5⟩, k5⟩ => ?_)
  rw [r4, show A s₄.mem B w 7 = 1 from one4] at eq5
  have a5 : A s₅.mem B w 6 = combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb)
      (Spec.Rsa.FixedBaseComb.rows bits)) := by
    rw [Rsa.FixedBaseComb.high_top, combM, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt hq.one,
      Nat.one_mul]
    rw [← Nat.mod_eq_of_lt lt5]
    exact VG.Proof.Bignum.mont_cancel cop (by rw [eq5, Nat.mul_one, Nat.mod_mod])
  have one5 : A s₅.mem B w 7 = 1 := by rw [fr5 7 (by decide) (by decide) (by decide) (by decide)]; exact one4
  -- `rows` rows left.
  have k15 := (((k12.trans k3).trans k4).trans k5)
  refine WP.seq (WP.mono (WP.keep [.s9] (Q := fun v => v.gpr .s9 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      v.mem = s₅.mem) (by brun [((((k2.trans k3).trans k4).trans k5).gpr (r := .s7) (by decide)).trans a7,
        BitVec.add_zero]) (by rfl) (by rfl)) fun s₆ ⟨⟨a9, m6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  have hpos := Rsa.FixedBaseComb.rows_pos h.pos
  have o16 : WinO B w s.mem s₆.mem := by
    rw [m6, ← hm2]; exact ((Outside.trans (arrO o3 (by decide) (by decide)) (arrO o4 (by decide) (by decide)))).trans o5
  have c6 : CS s₆ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) s₆ := by
    have hctx : Outside C (8 * ctxWords w) (2 ^ 64) s.mem s₆.mem := win_ctx o16 hZ h.ctx.sep
    have g : ∀ r ∈ ([.s10, .s8, .s7] : List Reg), s₆.gpr r = s₁.gpr r := fun r hr =>
      ((((k2.trans k3).trans k4).trans k5).trans k6).gpr (by revert r hr; decide)
    refine ⟨c5.regs k6 (by decide) m6, (g .s10 (by decide)).trans a10, h.ctx.congr k16.2.1 k16.2.2,
      fun a ha => by rw [ent_keep hctx h.ctx.hn ha]; exact h.ents a ha, a9,
      ⟨(k16.gpr (by decide)).trans h.s11, (g .s7 (by decide)).trans a7, (g .s8 (by decide)).trans a8,
        fun n hn => by rw [k16.2.1, k16.2.2]; exact h.xrd n hn,
        fun n hn => by rw [win_byte o16 hZ (h.xsep n hn)]; exact h.xval n hn, h.hL⟩,
      h.xsep, by rw [m6]; exact a5, by rw [m6]; exact one5, Outside.refl _ _ _ _, Keep.refl _ _⟩
  -- The rows.
  refine WP.seq (WP.mono (rows_ok hq c6 hpos) fun v hv => ?_)
  -- Out of Montgomery form.
  refine WP.mono (hv.win.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hv.one]; exact hq.one)) fun t ⟨⟨ct, lt7, eq7, fr7, o7⟩, k7⟩ =>
      ⟨⟨?_, ?_, o16.trans (hv.out.trans o7)⟩, ?_⟩
  · rw [hv.acc, hv.one, Nat.mul_one, Nat.mod_mod] at eq7
    rw [← Nat.mod_eq_of_lt lt7, ← Nat.mod_eq_of_lt (show Spec.Rsa.powMod G _ P < P from by
      rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hP)]
    exact VG.Proof.Bignum.mont_cancel cop (by rw [eq7, VG.Proof.Bignum.powMod_eq, Nat.mod_mul_mod])
  · exact ct.n
  · exact ((k16.trans hv.keep).trans k7).mono (by decide)

theorem comb_ok {s : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat}
    (h : CombIn s B C X Z w xb P G bits) :
    WP isa comb s fun t =>
      (A t.mem B w 4 = Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P ∧
        A t.mem B w 0 = P ∧ WinO B w s.mem t.mem) ∧ Keep combRegs s t :=
  WP.seq (WP.mono (head_ok h.scr (by have := h.hZ; have : slot w 24 = 256 + 24 * (8 * (w + 2)) := rfl; omega_arith)
    h.s6 h.hX h.hC h.hRw) fun _ ⟨⟨a10, a8, a7, a2, m1⟩, k1⟩ => combRest_ok h a10 a8 a7 a2 m1 k1)

end VG.Proof.Ffdh.RISCV64.Cached
