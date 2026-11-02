module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Proof.Dsa.DomainShape
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: the pointers, the sizes and the oddness of p and q

As on PPC64LE (`Proof/Dsa/PPC64LE/Sizes.lean`):

* `ptrP_ok`, …: the octets of p, q, g and y into `s7` and `s8`;
* `sigLen_ok`, `bytesBits_ok`: the scan of a number's octets
  (`Proof/Dsa/DomainShape.lean`'s `significant`): its significant octets in
  `a1`, and `a0 = 0` exactly when the first has its top bit set;
* `pairs_ok`: `a0 = 0` exactly when the significant octets of p and q are a
  supported pair;
* `odd_ok`: `a0 = 0` exactly when the number is odd;
* `sizes_ok`, `odds_ok`: `sizes` and `odds` run `rest` exactly when the
  sizes are supported, and p and q are odd; `sizes` writes q's
  significant octets to the header's lengths.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Dsa (significant significant_fits significant_nonzero)
open VG.Proof.Bignum (slot)

/-! ## The pointers -/

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The registers the pointers write. -/
def ptrRegs : List Reg := [.s7, .s8, .t3]

/-- p's octets. -/
theorem ptrP_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrP) s fun t =>
      (t.gpr .s7 = key ∧ t.gpr .s8 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep ptrRegs s t := by
  unfold ptrP
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = key ∧ u.mem = s.mem)
    (by brun [hr.s11, BitVec.add_zero]) (by rfl) (by rfl)) fun u ⟨⟨a7, mu⟩, ku⟩ => ?_
  refine WP.mono (getP_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .s8) fun t ⟨⟨b8, mt⟩, kt⟩ =>
    ⟨⟨(kt.gpr (by decide)).trans a7, b8, by rw [mt, mu]⟩, (ku.trans kt).mono (by decide)⟩

/-- q's octets. -/
theorem ptrQ_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrQ) s fun t =>
      (t.gpr .s7 = off key L.pl ∧ t.gpr .s8 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep ptrRegs s t := by
  unfold ptrQ
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (getP_ok hs hL hr .t3) fun u ⟨⟨a3, mu⟩, ku⟩ => ?_
  refine WP.mono (WP.keep [.s7] (Q := fun v => v.gpr .s7 = off key L.pl ∧ v.mem = u.mem)
    (by brun [a3, (ku.gpr (r := .s11) (by decide)).trans hr.s11]) (by rfl) (by rfl)) fun v ⟨⟨b7, mv⟩, kv⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr (ku.trans kv).2.2) hL (hr.keepM (ku.trans kv) (by rw [mv, mu])) .s8)
    fun t ⟨⟨c8, mt⟩, kt⟩ => ⟨⟨(kt.gpr (by decide)).trans b7, c8, by rw [mt, mv, mu]⟩,
      ((ku.trans kv).trans kt).mono (by decide)⟩

/-- g's octets. -/
theorem ptrG_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrG) s fun t =>
      (t.gpr .s7 = off key (L.pl + L.ql) ∧ t.gpr .s8 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧
        Keep ptrRegs s t := by
  unfold ptrG
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (getP_ok hs hL hr .s8) fun u ⟨⟨a8, mu⟩, ku⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t3) fun v ⟨⟨b3, mv⟩, kv⟩ => ?_
  have k := ku.trans kv
  refine WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = off key (L.pl + L.ql) ∧ t.mem = v.mem)
    (by brun [b3, (kv.gpr (r := .s8) (by decide)).trans a8, (k.gpr (r := .s11) (by decide)).trans hr.s11,
      off_off]) (by rfl) (by rfl))
    fun t ⟨⟨c7, mt⟩, kt⟩ => ⟨⟨c7, by rw [kt.gpr (by decide), kv.gpr (by decide), a8], by rw [mt, mv, mu]⟩,
      (k.trans kt).mono (by decide)⟩

/-- y's octets. -/
theorem ptrY_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrY) s fun t =>
      (t.gpr .s7 = off key (2 * L.pl + L.ql) ∧ t.gpr .s8 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧
        Keep ptrRegs s t := by
  unfold ptrY
  rw [WP.block_append_iff]
  refine WP.mono (ptrG_ok hs hL hr) fun u ⟨⟨a7, a8, mu⟩, ku⟩ => ?_
  refine WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = off key (2 * L.pl + L.ql) ∧ t.mem = u.mem)
    (by brun [a7, a8, off_off]; rw [show L.pl + L.ql + L.pl = 2 * L.pl + L.ql by omega]) (by rfl) (by rfl))
    fun t ⟨⟨c7, mt⟩, kt⟩ => ⟨⟨c7, by rw [kt.gpr (by decide), a8], by rw [mt, mu]⟩, (ku.trans kt).mono (by decide)⟩

/-! ## The scan of a number's octets -/

/-- One step of `sigLen`'s scan: whether a nonzero octet was seen, and the
octets counted from the first nonzero one. -/
def scanStep (a : Bool × Nat) (b : Byte) : Bool × Nat :=
  (a.1 || b != 0, if (a.1 || b != 0) = true then a.2 + 1 else a.2)

theorem scan_foldl (bs : List Byte) (a : Bool × Nat) :
    (bs.foldl scanStep a).2 = if a.1 = true then a.2 + bs.length else a.2 + (significant bs).1 := by
  induction bs generalizing a with
  | nil => cases a.1 <;> rfl
  | cons b bs ih =>
    rw [List.foldl_cons, ih]
    rcases a with ⟨_ | _, c⟩
    · by_cases hb : b = 0#8
      · subst hb; simp [scanStep, significant]
      · simp [scanStep, significant, hb]; omega_arith
    · simp [scanStep]; omega_arith

theorem bytesAt_take_succ (m : Mem) (N : Addr) {k i : Nat} (hi : i < k) :
    (Spec.Rsa.bytesAt m N k).take (i + 1) = (Spec.Rsa.bytesAt m N k).take i ++ [m (off N i)] := by
  simp [Spec.Rsa.bytesAt, List.take_add_one, hi]

theorem bytesAt_length (m : Mem) (N : Addr) (k : Nat) : (Spec.Rsa.bytesAt m N k).length = k := by
  simp [Spec.Rsa.bytesAt]

/-- The scan of the first `i` octets. -/
def scanAcc (bs : List Byte) (i : Nat) : Bool × Nat := (bs.take i).foldl scanStep (false, 0)

theorem scanAcc_succ (m : Mem) (N : Addr) {k i : Nat} (hi : i < k) :
    scanAcc (Spec.Rsa.bytesAt m N k) (i + 1) = scanStep (scanAcc (Spec.Rsa.bytesAt m N k) i) (m (off N i)) := by
  rw [scanAcc, bytesAt_take_succ m N hi, List.foldl_append]; rfl

theorem scanAcc_all (m : Mem) (N : Addr) (k : Nat) :
    (scanAcc (Spec.Rsa.bytesAt m N k) k).2 = (significant (Spec.Rsa.bytesAt m N k)).1 := by
  rw [scanAcc, List.take_of_length_le (by rw [bytesAt_length]), scan_foldl]
  simp

theorem scanAcc_le (bs : List Byte) (i : Nat) : (scanAcc bs i).2 ≤ i := by
  rw [scanAcc, scan_foldl]
  have := significant_fits (bs.take i)
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add, List.length_take] at this ⊢
  omega_arith

theorem scanStep_or {c : Bool × Nat} {x : Nat} (b : Byte) (hx : x = 0 ↔ c.1 = false) :
    (x ||| b.toNat = 0 ↔ (scanStep c b).1 = false) ∧
      (scanStep c b).2 = c.2 + if x ||| b.toNat = 0 then 0 else 1 := by
  have hb : b.toNat = 0 ↔ b = 0 := ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => h ▸ rfl⟩
  have e : x ||| b.toNat = 0 ↔ (c.1 || b != 0) = false := by
    rw [Nat.or_eq_zero_iff, hx, hb, Bool.or_eq_false_iff, bne_eq_false_iff_eq]
  refine ⟨e, ?_⟩
  simp only [scanStep]
  by_cases h : x ||| b.toNat = 0
  · rw [e.mp h]; simp [h]
  · have hc : (c.1 || b != 0) = true := by
      cases hc : (c.1 || b != 0)
      · exact absurd (e.mpr hc) h
      · rfl
    rw [hc]; simp [h]

/-- The first significant octet. -/
theorem significant_get (bs : List Byte) (h : (significant bs).1 ≠ 0) :
    bs[bs.length - (significant bs).1]? = some (significant bs).2 := by
  induction bs with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    by_cases hb : b = 0
    · rw [significant, ite_eq_left hb] at h ⊢
      have := significant_fits bs
      rw [List.length_cons, show bs.length + 1 - (significant bs).1 = (bs.length - (significant bs).1) + 1 by
        omega_arith, List.getElem?_cons_succ]
      exact ih h
    · rw [significant, ite_eq_right hb]
      simp

theorem bytesAt_get (m : Mem) (N : Addr) {k j : Nat} (hj : j < k) :
    (Spec.Rsa.bytesAt m N k)[j]? = some (m (off N j)) := by
  simp [Spec.Rsa.bytesAt, hj]

theorem bytesAt_last (m : Mem) (N : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m N k = Spec.Rsa.bytesAt m N (k - 1) ++ [m (off N (k - 1))] := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  simp [Spec.Rsa.bytesAt, List.range_succ]

theorem or_ofNat {x y : Nat} (hx : x < 256) (hy : y < 256) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 y = BitVec.ofNat 64 (x ||| y) := by
  have : x ||| y < 2 ^ 8 := Nat.or_lt_two_pow (by omega_arith) (by omega_arith)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem neg_shr63 {y : Nat} (hy : y < 256) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if y = 0 then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> simp only [Nat.reducePow, Nat.zero_mod, Nat.add_zero] <;> omega_arith


/-- The registers `sigLen` and `bytesBits` write. -/
def sigRegs : List Reg := [.s0, .a0, .a1, .t3, .t4, .t5]

/-- `sigLen`: the significant octets of the `k` octets at `N` (`s7`, `k` in
`s8`), into `a1`. -/
theorem sigLen_ok {s : State} {N : Addr} {k : Nat} (h7 : s.gpr .s7 = N) (h8 : s.gpr .s8 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k ≤ 1024) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa sigLen s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem N k)).1 ∧ t.mem = s.mem) ∧
        Keep sigRegs s t := by
  refine WP.keep sigRegs ?_ (by decide) (by rfl)
  unfold sigLen countLoop
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t3 .s7 0, .addi .t5 .s8 0, .li .t4 0, .li .a1 0]) s fun s₁ =>
      s₁.gpr .t3 = off N 0 ∧ s₁.gpr .t5 = BitVec.ofNat 64 k ∧ s₁.gpr .t4 = BitVec.ofNat 64 0 ∧
        s₁.gpr .a1 = BitVec.ofNat 64 0 ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    brun [h7, h8, BitVec.add_zero, exec_li_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨i3, i5, i4, i1, im, ird, iwr⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off N i ∧ (∃ x, x < 256 ∧ t.gpr .t4 = BitVec.ofNat 64 x ∧
      (x = 0 ↔ (scanAcc (Spec.Rsa.bytesAt s.mem N k) i).1 = false)) ∧
      t.gpr .a1 = BitVec.ofNat 64 (scanAcc (Spec.Rsa.bytesAt s.mem N k) i).2 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.mono (wp_countdown (body := .block ([.load .b .s0 .t3 0, .logic .or .t4 .t4 .s0, .li .a0 0,
      .sub .a0 .a0 .t4, .shift .srl .d .a0 .a0 63, .add .a1 .a1 .a0, .addi .t3 .t3 1] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := k) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨t3, ⟨x, hx, t4, hx0⟩, t1, tm, trd, twr⟩ _ => ?_)
    ⟨i3, ⟨0, by decide, i4, by simp [scanAcc]⟩, by rw [i1]; rfl, im, ird, iwr⟩ i5)
    fun t ⟨_, _, t1, tm, _⟩ => ⟨by rw [t1, scanAcc_all], tm⟩
  have hb := (s.mem (off N i)).isLt
  have hy : x ||| (s.mem (off N i)).toNat < 256 := Nat.or_lt_two_pow (n := 8) hx hb
  have hs := scanStep_or (s.mem (off N i)) hx0
  have hl : exec (.load .b .s0 .t3 0) t = some (t.write .s0 (BitVec.ofNat 64 (s.mem (off N i)).toNat)) := by
    rw [exec_load_b (by decide) (by rw [t3, BitVec.add_zero, trd, twr]; exact hrd i hi), t3, BitVec.add_zero,
      read_byte64, tm]
  brun [hl, t4, t1, exec_li_lit (show 0 < 2048 by decide), exec_shift_d (show 63 < 64 by decide), gpr_write_self,
    or_ofNat hx hb, neg_shr63 hy, ← BitVec.ofNat_add]
  rw [← scanAcc_succ s.mem N hi] at hs
  refine ⟨by gsimp; rw [t3, off_add], ⟨_, hy, by gsimp, hs.1⟩, by gsimp; rw [hs.2], by gsimp; exact tm,
    by gsimp; exact trd, by gsimp; exact twr⟩

/-- `bytesBits`: the significant octets into `a1`, and `a0 = 0` exactly
when the first has its top bit set. -/
theorem bytesBits_ok {s : State} {N : Addr} {k : Nat} (h7 : s.gpr .s7 = N)
    (h8 : s.gpr .s8 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa bytesBits s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem N k)).1 ∧
        (t.gpr .a0 = 0 ↔ 128 ≤ (significant (Spec.Rsa.bytesAt s.mem N k)).2.toNat) ∧ t.mem = s.mem) ∧
        Keep sigRegs s t := by
  refine WP.keep sigRegs ?_ (by decide) (by rfl)
  unfold bytesBits
  refine WP.seq (WP.mono (sigLen_ok h7 h8 hk hk' hrd) fun t ⟨⟨t1, tm⟩, kt⟩ => ?_)
  have hc := significant_fits (Spec.Rsa.bytesAt s.mem N k)
  rw [bytesAt_length] at hc
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) t1) (fun hz => ?_) (fun hz => ?_)
  · have hz : (significant (Spec.Rsa.bytesAt s.mem N k)).1 = 0 := by simpa using hz
    have h2 := (significant_nonzero _).mp hz
    brun [t1, tm, exec_li_lit (show 1 < 2048 by decide)]
    rw [h2]
    decide
  · have hz : (significant (Spec.Rsa.bytesAt s.mem N k)).1 ≠ 0 := by simpa using hz
    have hg := significant_get _ hz
    rw [bytesAt_length, bytesAt_get _ _ (by omega_arith), Option.some.injEq] at hg
    have hr : InRegions (t.rd ++ t.wr) (off N (k - (significant (Spec.Rsa.bytesAt s.mem N k)).1)) 1 := by
      rw [kt.2.1, kt.2.2]; exact hrd _ (by omega_arith)
    unfold topBit
    brun [kt.gpr (r := .s7) (by decide), kt.gpr (r := .s8) (by decide), h7, h8, t1,
      Offset.add_ofNat_sub N (show (significant (Spec.Rsa.bytesAt s.mem N k)).1 ≤ k by omega_arith),
      hr, read_byte64, tm, hg, exec_li_lit (show 1 < 2048 by decide), exec_shift_d (show 7 < 64 by decide)]
    exact top_xor (significant (Spec.Rsa.bytesAt s.mem N k)).2.isLt

theorem ofNat_sub_eq_zero {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = 0 ↔ x = y := by
  have := Offset.ofNat_sub_ofNat_beq hx hy
  rwa [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff] at this

/-- `pairOk P Q`: `a0 := 0` if `(a, b) = (P, Q)`. -/
theorem pairOk_ok {s : State} {a b P Q : Nat} {R : Prop} (h2 : s.gpr .a2 = BitVec.ofNat 64 a)
    (h3 : s.gpr .a3 = BitVec.ofNat 64 b) (ha : a ≤ 1024) (hb : b ≤ 1024) (hP : P ≤ 2048)
    (hQ : Q ≤ 2048) (h0 : s.gpr .a0 = 0 ↔ R) :
    WP isa (pairOk P Q) s fun t =>
      ((t.gpr .a0 = 0 ↔ R ∨ (a = P ∧ b = Q)) ∧ t.gpr .a2 = BitVec.ofNat 64 a ∧
        t.gpr .a3 = BitVec.ofNat 64 b ∧ t.mem = s.mem) ∧ Keep [.a0, .t3, .t4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold pairOk
  refine WP.seq (WP.mono (WP.keep [.t3, .t4] (Q := fun t => t.gpr .t3 =
      (BitVec.ofNat 64 a - BitVec.ofNat 64 P ||| BitVec.ofNat 64 b - BitVec.ofNat 64 Q) ∧ t.mem = s.mem)
    (by brun [h2, h3, hP, hQ, exec_addi_neg_nat hP, exec_addi_neg_nat hQ]) (by rfl) (by rfl)) fun t ⟨⟨t3, tm⟩, kt⟩ => ?_)
  have e : (t.gpr .t3 == 0) = decide (a = P ∧ b = Q) := by
    rw [t3, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
      show ∀ x y : BitVec 64, (x ||| y = 0 ↔ x = 0 ∧ y = 0) from fun _ _ => BitVec.or_eq_zero_iff,
      ofNat_sub_eq_zero (by omega_arith) (by omega_arith), ofNat_sub_eq_zero (by omega_arith) (by omega_arith)]
  have t2 : t.gpr .a2 = BitVec.ofNat 64 a := (kt.gpr (by decide)).trans h2
  have t3' : t.gpr .a3 = BitVec.ofNat 64 b := (kt.gpr (by decide)).trans h3
  refine WP.ite _ (by rw [Steps.eval_zero, e]) (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    brun [t2, t3', tm, exec_li_zero]
    exact ⟨fun _ => .inr hz, fun _ => trivial⟩
  · have hz := of_decide_eq_false hz
    refine WP.block_nil ⟨?_, t2, t3', tm⟩
    rw [kt.gpr (by decide), h0]
    exact ⟨.inl, fun h => h.resolve_right hz⟩

/-- `pairs`: `a0 = 0` exactly when `(8 a, 8 b)` are supported sizes. -/
theorem pairs_ok {s : State} {a b : Nat} (h2 : s.gpr .a2 = BitVec.ofNat 64 a)
    (h3 : s.gpr .a3 = BitVec.ofNat 64 b) (ha : a ≤ 1024) (hb : b ≤ 1024) :
    WP isa pairs s fun t =>
      ((t.gpr .a0 = 0 ↔ Spec.Dsa.supportedSizes (8 * a) (8 * b)) ∧ t.mem = s.mem) ∧
        Keep [.a0, .t3, .t4] s t := by
  refine WP.keep _ ?_ (by decide) (by rfl)
  unfold pairs
  refine WP.seq (WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by brun [exec_li_lit (show 1 < 2048 by decide)]) (by decide) (by rfl)) fun t₀ ⟨⟨a0, m0⟩, k0⟩ => ?_)
  have h0 : t₀.gpr .a0 = 0 ↔ False := ⟨fun h => absurd (a0.symm.trans h) (by decide), False.elim⟩
  refine WP.seq (WP.mono (pairOk_ok (P := 128) (Q := 20) ((k0.gpr (by decide)).trans h2)
    ((k0.gpr (by decide)).trans h3) ha hb (by decide) (by decide) h0)
    fun t₁ ⟨⟨a1, b1, c1, m1⟩, _⟩ => ?_)
  refine WP.seq (WP.mono (pairOk_ok (P := 256) (Q := 20) b1 c1 ha hb (by decide) (by decide) a1)
    fun t₂ ⟨⟨a2, b2, c2, m2⟩, _⟩ => ?_)
  refine WP.seq (WP.mono (pairOk_ok (P := 256) (Q := 28) b2 c2 ha hb (by decide) (by decide) a2)
    fun t₃ ⟨⟨a3, b3, c3, m3⟩, _⟩ => ?_)
  refine WP.seq (WP.mono (pairOk_ok (P := 256) (Q := 32) b3 c3 ha hb (by decide) (by decide) a3)
    fun t₄ ⟨⟨a4, b4, c4, m4⟩, _⟩ => ?_)
  refine WP.mono (pairOk_ok (P := 384) (Q := 32) b4 c4 ha hb (by decide) (by decide) a4)
    fun t ⟨⟨a5, _, _, m5⟩, _⟩ => ⟨?_, by rw [m5, m4, m3, m2, m1, m0]⟩
  rw [a5, false_or]
  constructor
  · rintro ((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) <;> decide
  · unfold Spec.Dsa.supportedSizes
    rintro (⟨h1, h2⟩ | ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2⟩)
    · exact .inl (.inl (.inl (.inl ⟨by omega_arith, by omega_arith⟩)))
    · exact .inl (.inl (.inl (.inr ⟨by omega_arith, by omega_arith⟩)))
    · exact .inl (.inl (.inr ⟨by omega_arith, by omega_arith⟩))
    · exact .inl (.inr ⟨by omega_arith, by omega_arith⟩)
    · exact .inr ⟨by omega_arith, by omega_arith⟩

/-- `odd`: `a0 = 0` exactly when the number of the `k` octets at `N` is odd. -/
theorem odd_ok {s : State} {N : Addr} {k : Nat} (h7 : s.gpr .s7 = N) (h8 : s.gpr .s8 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k ≤ 1024) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa (.block odd) s fun t =>
      ((t.gpr .a0 = 0 ↔ Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem N k) % 2 = 1) ∧ t.mem = s.mem) ∧
        Keep [.a0, .t3] s t := by
  refine WP.keep _ ?_ (by decide) (by rfl)
  unfold odd
  have hr : InRegions (s.rd ++ s.wr) (off N (k - 1)) 1 := hrd _ (by omega_arith)
  brun [h7, h8, Offset.add_ofNat_sub N hk, hr, read_byte64]
  rw [odd_xor, bytesAt_last s.mem N hk, Proof.Dsa.decodeBE_last_mod_two]

end VG.Proof.Dsa.RISCV64
