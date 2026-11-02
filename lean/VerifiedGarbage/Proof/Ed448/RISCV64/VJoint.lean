module

-- separate module: its proofs take about 13 s, which `VMain.lean`'s edits need not re-check
public import VerifiedGarbage.Proof.Ed448.RISCV64.VDigits
public import VerifiedGarbage.Proof.Ed448.RISCV64.Comb
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Proof.Ed448.WnafWide.Group
import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
import Mathlib.Tactic.Abel

/-!
# Ed448's verification on RISCV64: the joint loop

At position `n`, from the top, `R` becomes `[2]R + [S_n]B + [k_n]a`
(`jointStep_ok`), for `S_n` and `k_n` the width-5 digits of `S` and `k`
(`digV`) and `a` what the key table's entries are odd multiples of
(`KeyOk`): `R` represents `[residual S n]B + [residual k n]a`
(`JInv.rep`), so from the neutral point at 464 it represents `[S]B + [k]a`
at 0 (`jointLoop_ok`). A digit `d ≠ 0` selects entry `|d| / 2` of its table
(`digit_decode`), negated if `d < 0`: `baseEntry d` for `B`'s, and `±[|d|]a`
for `a`'s.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Proof.X448.RISCV64.R64 (dw al8 Sep8)
open VG.Proof.Ed448 (Rep baseAff pointAdd_rep double_rep dZ)
open VG.Proof.Ed448.RISCV64.Comb (toF opsProg_eq ptOf DQ AQ dbl_ok add_ok dbl_sub add_sub dbl_vals add_vals
  addAffine_eq)
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point)

/-! ## Digits -/

/-- The byte of a digit, as `lbu` reads it. -/
abbrev dByte (d : Int) : BitVec 64 := BitVec.ofNat 64 (BitVec.ofInt 8 d).toNat

/-- The digit's byte sign-extended, as `digitIndex` does. -/
abbrev dExt (x : BitVec 64) : BitVec 64 := (x <<< 56).sshiftRight 56

/-- Its sign's mask. -/
abbrev dMask (x : BitVec 64) : BitVec 64 := (dExt x).sshiftRight 63

/-- Its entry's index. -/
abbrev dIdx (x : BitVec 64) : BitVec 64 := ((dExt x ^^^ dMask x) - dMask x) >>> 1

/-- What `digitIndex` computes, for the digit `d`. -/
def digB (d : Int) : Bool :=
  (dIdx (dByte d) == BitVec.ofNat 64 (d.natAbs / 2)) &&
    (dMask (dByte d) == if d < 0 then BitVec.allOnes 64 else 0) && ((dByte d != 0) == decide (d ≠ 0))

theorem digB_all : ∀ i : Nat, i < 31 → digB ((i : Int) - 15) = true := by decide

theorem digit_dec {d : Int} (h1 : -15 ≤ d) (h2 : d ≤ 15) :
    dIdx (dByte d) = BitVec.ofNat 64 (d.natAbs / 2) ∧
      dMask (dByte d) = (if d < 0 then BitVec.allOnes 64 else 0) ∧ (dByte d != 0) = decide (d ≠ 0) := by
  have := digB_all (d + 15).toNat (by omega)
  rw [show ((d + 15).toNat : Int) - 15 = d by omega] at this
  simp only [digB, Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem shl_ofNat {n k : Nat} (h : n * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ this) h), Nat.mod_eq_of_lt h]

section
variable {b : Addr}

/-! ## Between field operations -/

/-- `Cur` after registers of `work` but `t1` change, the memory not. -/
theorem cur_regs {s0 s s' : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe}
    (h : R64.Cur b s0 a c qs v s) {ws : List Reg} (hr : Rest ws s s') (hws : ∀ r ∈ ws, r ∈ R64.work)
    (h1 : Reg.t1 ∉ ws) (h3 : Reg.a3 ∉ ws) (hm : s'.mem = s.mem) : R64.Cur b s0 (s'.gpr .t2) c qs v s' :=
  ⟨h.ctx.of_rest hr h3, h.stp.trans (R64.Stp.of_rest hr hws hm), rfl, by rw [hr.gpr _ h1, h.t1],
    by rw [hm]; exact h.slots⟩

/-- `Cur` with the slots' own values. -/
theorem cur_fs {s0 s : State} {a c : BitVec 64} {qs qs' : List Nat} {v : Nat → Fe}
    (h : R64.Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) : R64.Cur b s0 a c qs' (FS s.mem b) s :=
  h.congr hq fun q hq' => (h.slots q (hq q hq')).symm

theorem vctx_cur {s0 s : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (hv : VCtx b s0)
    (h : R64.Cur b s0 a c qs v s) : VCtx b s :=
  hv.of_rest h.stp.rest (by decide) (by decide)

/-- The element at `b + ps` copied into the slot `o`. -/
theorem opCp {s0 s : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (hv : VCtx b s)
    (h : R64.Cur b s0 a c qs v s) {rs : Reg} {so o ps : Nat} (hrs : rs ≠ .a4) (hso : so + 48 < 2048)
    (hs : s.gpr rs + BitVec.ofNat 64 so = b + BitVec.ofNat 64 ps) (hps : ps % 8 = 0) (hps' : ps + 56 ≤ 8184)
    (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hsep : ps + 56 ≤ o ∨ o + 56 ≤ ps) :
    WP isa (.block (cp7 rs so .a3 o)) s fun t =>
      R64.Cur b s0 a c (o :: qs) (upd v o (FS s.mem b ps)) t ∧ Rest [.a4] s t := by
  have hA : ACC = 952 := rfl
  have ho8 := R64.sep8_o hq
  refine WP.mono (cp7_ok hv hrs (by decide) hso (by omega) hs (by rw [h.ctx.a3]) hps ho8 hps' (by omega)
    hsep) fun t ⟨_, hr, hf, hd⟩ => ⟨h.next (hr.mono (by decide)) (frame_FA ho (frame_o hf)) fun q hq' => ?_, hr⟩
  rcases List.mem_cons.mp hq' with rfl | hq'
  · rw [upd_self, FS, FS, cp7_V hd]
  · by_cases e : q = o
    · subst e; rw [upd_self, FS, FS, cp7_V hd]
    · rw [upd_of_ne _ _ e]
      exact slots_after (R64.sep8_sep1 hq) ho (frame_o hf) h.slots hq' e

/-! ## The digit's entry -/

/-- `loadDigit e` reads the byte of lane `e` at `n = t1`. -/
theorem loadDigit_ok {s : State} (hv : VCtx b s) {n e : Nat} (hn : n < 468) (he : e < 4)
    (h1 : s.gpr .t1 = BitVec.ofNat 64 n) :
    WP isa (.block (loadDigit e)) s fun t => Rest [.a1, .a5] s t ∧ t.mem = s.mem ∧
      t.gpr .a5 = BitVec.ofNat 64 (s.mem (b + BitVec.ofNat 64 (TB + (4 * n + e)))).toNat := by
  have hT : TB = 2104 := rfl
  have hO : OUT = 2048 := rfl
  simp only [loadDigit]
  refine wp_sll (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e2 : s2.gpr .a1 + BitVec.ofNat 64 (TB - OUT + e) = b + BitVec.ofNat 64 (TB + (4 * n + e)) := by
    rw [u2.gpr, u1.other _ (by decide), u1.gpr, hv.a0, h1, shl_ofNat (by omega), Offset.add_add, Offset.add_add]
    congr 2; omega
  refine wp_lbz (by omega) e2 (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hv.inR (by omega)) fun s3 u3 =>
    WP.block_nil ⟨(u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, u1.mem], by rw [u3.gpr, u2.mem, u1.mem]⟩

/-- `digitIndex`: the sign's mask into `a6` and the index into `a5`. -/
theorem digitIndex_ok {s : State} {d : Int} (h1 : -15 ≤ d) (h2 : d ≤ 15)
    (h5 : s.gpr .a5 = BitVec.ofNat 64 (BitVec.ofInt 8 d).toNat) :
    WP isa (.block digitIndex) s fun t => Rest [.a5, .a6] s t ∧ t.mem = s.mem ∧
      t.gpr .a5 = BitVec.ofNat 64 (d.natAbs / 2) ∧ t.gpr .a6 = (if d < 0 then BitVec.allOnes 64 else 0) := by
  obtain ⟨i1, i2, -⟩ := digit_dec h1 h2
  rw [← dByte] at h5
  simp only [digitIndex]
  refine wp_sll (by decide) fun s1 u1 => wp_sra (by decide) fun s2 u2 => wp_sra (by decide) fun s3 u3 =>
    wp_xor fun s4 u4 => wp_sub fun s5 u5 => wp_srl (by decide) fun s6 u6 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [← i1]
    simp only [reduceCtorEq, u6.at, u5.at, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h5]
  · rw [← i2]
    simp only [reduceCtorEq, u6.at, u5.at, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h5]


/-! ## What the loop keeps -/

theorem fs_hi {m m' : Mem} (hf : Frame [FA b] m m') {q : Nat} (hq : ACC + 112 ≤ q) (hq' : q + 56 ≤ 8192) :
    FS m' b q = FS m b q := by
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base b (by omega_using [hq]) (by omega_using [hq', hk])
  rw [FS, V, val32_congr e]; rfl

theorem byte_hi {m m' : Mem} (hf : Frame [FA b] m m') {d : Nat} (hd : ACC + 112 ≤ d) (hd' : d < 8192) :
    m' (b + BitVec.ofNat 64 d) = m (b + BitVec.ofNat 64 d) :=
  hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact fun h => Offset.disjoint_base b (d := d) (n := 1) (k := ACC + 112) hd (by omega_using [hd'])
      _ (Region.contains_self _ _) h

/-- The key table's entry `i`, projective. -/
def kpt (m : Mem) (b : Addr) (i : Nat) : Point :=
  ⟨FS m b (KT + 168 * i), FS m b (KT + 168 * i + 56), FS m b (KT + 168 * i + 112)⟩

/-- The key table's entries are the odd multiples of `a`. -/
def KeyOk (b : Addr) (a : VG.Proof.EdwardsLaw.EPoint dZ) (m : Mem) : Prop :=
  ∀ i < 8, Rep (kpt m b i) ((2 * i + 1) • a)

/-- What the joint loop reads: the digits of `S` and `K` and the two tables. -/
def JFix (b : Addr) (S K : Nat) (m : Mem) : Prop :=
  TbIs b m (digV S K) ∧ BaseOk b m

theorem kpt_hi {m m' : Mem} (hf : Frame [FA b] m m') {i : Nat} (hi : i < 8) : kpt m' b i = kpt m b i := by
  have hA : ACC = 952 := rfl
  have hK : KT = 3976 := rfl
  simp only [kpt]
  rw [fs_hi hf (by omega) (by omega), fs_hi hf (by omega) (by omega), fs_hi hf (by omega) (by omega)]

theorem base_fs {m : Mem} (h : BaseOk b m) {i : Nat} (hi : i < 8) :
    FS m b (BT + 112 * i) = (Impl.Ed448.PublicTable.entry i).1 ∧
      FS m b (BT + 112 * i + 56) = (Impl.Ed448.PublicTable.entry i).2 := by
  obtain ⟨e1, e2⟩ := h i hi
  exact ⟨by rw [FS, e1, Proof.X448.toFe_self], by rw [FS, e2, Proof.X448.toFe_self]⟩

theorem dig_byte {S K : Nat} {m : Mem} (h : TbIs b m (digV S K)) {n e : Nat} (hn : n < 468) (he : e = 2 ∨ e = 3) :
    (m (b + BitVec.ofNat 64 (TB + (4 * n + e)))).toNat =
      (BitVec.ofInt 8 (digitAt false (if e = 2 then S else K) n)).toNat := by
  rw [h _ (by omega), digV, BitVec.toNat_ofNat]
  rcases he with rfl | rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show (4 * n + 2) / 4 = n by omega, Nat.mod_eq_of_lt (BitVec.isLt _), ite_eq_left rfl]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      show (4 * n + 3) / 4 = n by omega, Nat.mod_eq_of_lt (BitVec.isLt _), ite_eq_right (by omega)]

theorem digit_range (k n : Nat) : -15 ≤ digitAt false k n ∧ digitAt false k n ≤ 15 := by
  have := Proof.Ed448.WnafWide.digit_bounds false (residual false k n)
  change -(16 : Int) < _ ∧ _ < 16 at this
  exact ⟨by unfold digitAt; omega, by unfold digitAt; omega⟩

/-! ## The entries' pointers -/

theorem ptrBase_ok {s : State} (hv : VCtx b s) {i : Nat} (hi : i < 8) (h5 : s.gpr .a5 = BitVec.ofNat 64 i) :
    WP isa (.block [.shift .sll .d .t0 .a5 7, .shift .sll .d .a5 .a5 4, .sub .t0 .t0 .a5, .add .t0 .t0 .a0,
        .addi .t2 .t0 2047, .addi .t2 .t2 (BT - OUT - 2047 : Nat)]) s fun t =>
      Rest [.a5, .t0, .t2] s t ∧ t.mem = s.mem ∧ t.gpr .t2 = b + BitVec.ofNat 64 (BT + 112 * i) := by
  have hB : BT = 5320 := rfl
  have hO : OUT = 2048 := rfl
  refine wp_sll (by decide) fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_sub fun s3 u3 => wp_add fun s4 u4 =>
    wp_addi (by decide) fun s5 u5 => wp_addi (by decide) fun s6 u6 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · simp only [reduceCtorEq, u6.at, u5.at, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h5, hv.a0]
    rw [shl_ofNat (by omega), shl_ofNat (by omega)]
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hB, hO]
    omega

theorem ptrKey_ok {s : State} (hv : VCtx b s) {i : Nat} (hi : i < 8) (h5 : s.gpr .a5 = BitVec.ofNat 64 i) :
    WP isa (.block [.shift .sll .d .t0 .a5 7, .shift .sll .d .a2 .a5 5, .add .t0 .t0 .a2,
        .shift .sll .d .a2 .a5 3, .add .t0 .t0 .a2, .add .t0 .t0 .a0, .addi .t2 .t0 (KT - OUT)]) s fun t =>
      Rest [.a2, .t0, .t2] s t ∧ t.mem = s.mem ∧ t.gpr .t2 = b + BitVec.ofNat 64 (KT + 168 * i) := by
  have hK : KT = 3976 := rfl
  have hO : OUT = 2048 := rfl
  refine wp_sll (by decide) fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_add fun s3 u3 =>
    wp_sll (by decide) fun s4 u4 => wp_add fun s5 u5 => wp_add fun s6 u6 =>
    wp_addi (by decide) fun s7 u7 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
        (u7.rest (by decide)))))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · simp only [reduceCtorEq, u7.at, u6.at, u5.at, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h5,
      hv.a0]
    rw [shl_ofNat (by omega), shl_ofNat (by omega), shl_ofNat (by omega)]
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hK, hO]
    omega


/-! ## The additions -/

/-- `baseEntry d` is the selected entry, negated as the code does. -/
theorem baseEntry_eq {d : Int} (hd : d ≠ 0) (x y : Fe)
    (hx : x = (Impl.Ed448.PublicTable.entry (d.natAbs / 2)).1) (hy : y = (Impl.Ed448.PublicTable.entry (d.natAbs / 2)).2) :
    Proof.Ed448.WnafWide.baseEntry d = ⟨if d < 0 then x - x - x else x, y, 1⟩ := by
  unfold Proof.Ed448.WnafWide.baseEntry Proof.Ed448.WnafWide.signedPoint
  rw [ite_eq_right hd]
  by_cases hn : d < 0
  · rw [decide_eq_true hn, ite_eq_left rfl, ite_eq_left hn]
    simp only [Proof.Ed448.negPoint, Proof.X448.basePt]
    rw [hx, hy, sub_self]
  · rw [decide_eq_false hn, ite_eq_right Bool.false_ne_true, ite_eq_right hn]
    simp only [Proof.X448.basePt]
    rw [hx, hy]

/-- After an addition: `R` and `d` in their slots, `R` representing `X a` whenever the key table holds
the odd multiples of `a`. -/
def APost (b : Addr) (sL : State) (n : Nat) (X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ)
    (t : State) : Prop :=
  (∃ t2', R64.Cur b sL t2' (BitVec.ofNat 64 n) DQ (FS t.mem b) t) ∧ FS t.mem b DK = Spec.Ed448.d ∧
    ∀ a, KeyOk b a sL.mem → Rep (ptOf (FS t.mem b)) (X a)

theorem addBase_ok {S K : Nat} {sL s : State} (hvL : VCtx b sL)
    (hfx : JFix b S K sL.mem) {n : Nat} (hn : n < 464) {t2v : BitVec 64}
    (hc : R64.Cur b sL t2v (BitVec.ofNat 64 n) DQ (FS s.mem b) s)
    {X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ}
    (hd : FS s.mem b DK = Spec.Ed448.d) (hrep : ∀ a, KeyOk b a sL.mem → Rep (ptOf (FS s.mem b)) (X a)) :
    WP isa addBase s (APost b sL n fun a => X a + digitAt false S n • baseAff) := by
  have hA : ACC = 952 := rfl
  have hT : TB = 2104 := rfl
  have hB : BT = 5320 := rfl
  have hv := vctx_cur hvL hc
  obtain ⟨hdig, hbase⟩ := hfx
  obtain ⟨g1, g2⟩ := digit_range S n
  obtain ⟨i1, i2, i3⟩ := digit_dec g1 g2
  unfold addBase baseBody
  refine WP.seq (WP.mono (loadDigit_ok hv (n := n) (e := 2) (by omega) (by decide) hc.t1)
    fun s1 ⟨r1, m1, e5⟩ => ?_)
  have hb5 : s1.gpr .a5 = dByte (digitAt false S n) := by
    rw [e5, byte_hi hc.stp.frame (by omega) (by omega), dig_byte hdig (by omega) (.inl rfl), ite_eq_left rfl]
  have C1 := cur_regs hc r1 (by decide) (by decide) (by decide) m1
  refine WP.ite _ (by rw [eval_nonzero, hb5]) (fun hnz => ?_) (fun hz => ?_)
  · have hne : digitAt false S n ≠ 0 := by rw [i3] at hnz; simpa using hnz
    have hi : (digitAt false S n).natAbs / 2 < 8 := by omega
    rw [show digitIndex ++ [.shift .sll .d .t0 .a5 7, .shift .sll .d .a5 .a5 4, .sub .t0 .t0 .a5, .add .t0 .t0 .a0,
        .addi .t2 .t0 2047, .addi .t2 .t2 (BT - OUT - 2047 : Nat)] ++ ldSlots .t2 0 [SX, SY] =
      digitIndex ++ ([.shift .sll .d .t0 .a5 7, .shift .sll .d .a5 .a5 4, .sub .t0 .t0 .a5, .add .t0 .t0 .a0,
        .addi .t2 .t0 2047, .addi .t2 .t2 (BT - OUT - 2047 : Nat)] ++ (cp7 .t2 0 .a3 SX ++ cp7 .t2 56 .a3 SY)) from rfl]
    refine WP.seq (WP.append (digitIndex_ok g1 g2 hb5) fun s2 ⟨r2, m2, a52, a62⟩ => ?_)
    have hv2 : VCtx b s2 :=
      hv.of_rest ((r1.mono (ws' := [.a1, .a5, .a6]) (by decide)).trans (r2.mono (by decide))) (by decide) (by decide)
    refine WP.append (ptrBase_ok hv2 hi a52) fun s3 ⟨r3, m3, t3⟩ => ?_
    have r23 : Rest [.a5, .a6, .t0, .t2] s1 s3 := (r2.mono (by decide)).trans (r3.mono (by decide))
    have C3 := cur_regs C1 r23 (by decide) (by decide) (by decide) (by rw [m3, m2])
    have hv3 : VCtx b s3 := vctx_cur hvL C3
    have bx := base_fs hbase hi
    have kx : FS s3.mem b (BT + 112 * ((digitAt false S n).natAbs / 2)) =
        (Impl.Ed448.PublicTable.entry ((digitAt false S n).natAbs / 2)).1 := by
      rw [fs_hi C3.stp.frame (by omega) (by omega)]; exact bx.1
    refine WP.append (opCp hv3 C3 (rs := .t2) (so := 0) (o := SX)
      (ps := BT + 112 * ((digitAt false S n).natAbs / 2)) (by decide) (by decide)
      (by rw [BitVec.add_zero, t3]) (by omega) (by omega) (by decide) (by decide) (by simp only [SX]; omega))
      fun s4 ⟨C4, q4⟩ => ?_
    have hv4 : VCtx b s4 := vctx_cur hvL C4
    have ky : FS s4.mem b (BT + 112 * ((digitAt false S n).natAbs / 2) + 56) =
        (Impl.Ed448.PublicTable.entry ((digitAt false S n).natAbs / 2)).2 := by
      rw [fs_hi C4.stp.frame (by omega) (by omega)]; exact bx.2
    refine WP.mono (opCp hv4 C4 (rs := .t2) (so := 56) (o := SY)
      (ps := BT + 112 * ((digitAt false S n).natAbs / 2) + 56) (by decide) (by decide)
      (by rw [C4.t2, t3, Offset.add_add]) (by omega) (by omega) (by decide) (by decide) (by simp only [SY]; omega))
      fun s5 ⟨C5, q5⟩ => ?_
    -- The negation.
    have a65 : s5.gpr .a6 = if digitAt false S n < 0 then BitVec.allOnes 64 else 0 := by
      rw [q5.gpr _ (by decide), q4.gpr _ (by decide), r3.gpr _ (by decide), a62]
    rw [kx] at C5
    rw [ky] at C5
    generalize hx : (Impl.Ed448.PublicTable.entry ((digitAt false S n).natAbs / 2)).1 = x at C5
    generalize hy : (Impl.Ed448.PublicTable.entry ((digitAt false S n).natAbs / 2)).2 = y at C5
    let w : Nat → Fe := upd (upd (FS s.mem b) SX (if digitAt false S n < 0 then x - x - x else x)) SY y
    have neg : WP isa (.ite (.nonzero .a6) (.block (Impl.X448.RISCV64.R64.sub U0 SX SX ++
        Impl.X448.RISCV64.R64.sub SX U0 SX)) (.block [])) s5
        (R64.Cur b sL (s3.gpr .t2) (BitVec.ofNat 64 n) AQ w) := by
      by_cases hneg : digitAt false S n < 0
      · refine WP.ite true (by rw [eval_nonzero, a65, ite_eq_left hneg]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
        refine WP.append (R64.opSub (o := U0) (x := SX) (y := SX) (by decide) (by decide) (by decide) (by decide) C5)
          fun s6 C6 => WP.mono (R64.opSub (o := SX) (x := U0) (y := SX) (by decide) (by decide) (by decide)
            (by decide) C6) fun s7 C7 => C7.congr (by decide) fun q hq => ?_
        simp only [AQ, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := decide) only [w, upd_self, upd_of_ne, ite_eq_left hneg]
      · refine WP.ite false (by rw [eval_nonzero, a65, ite_eq_right hneg]; rfl) (fun h => absurd h (by decide))
          (fun _ => WP.block_nil (C5.congr (by decide) fun q hq => ?_))
        simp only [AQ, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := decide) only [w, upd_self, upd_of_ne, ite_eq_right hneg]
    refine WP.seq (WP.mono neg fun s7 C7 => ?_)
    rw [opsProg_eq]
    have hwd : w DK = Spec.Ed448.d := by simp (disch := decide) only [w, upd_of_ne]; exact hd
    refine R64.ops_ok _ AQ w s7 add_ok C7 fun s8 C8 => WP.block_nil ⟨⟨_, cur_fs C8 add_sub⟩, ?_, ?_⟩
    · rw [C8.slots DK (add_sub DK (by decide)), (add_vals w hwd).2, hwd]
    · have p8 : ptOf (FS s8.mem b) = ptOf (runOps (Impl.Ed448.RISCV64.addOps.map toF) w) := by
        simp only [ptOf]
        rw [C8.slots RX (add_sub RX (by decide)), C8.slots RY (add_sub RY (by decide)),
          C8.slots RZ (add_sub RZ (by decide))]
      have pw : ptOf w = ptOf (FS s.mem b) := by simp (disch := decide) only [ptOf, w, upd_of_ne]
      have sx : w SX = if digitAt false S n < 0 then x - x - x else x := by
        simp (disch := decide) only [w, upd_self, upd_of_ne]
      have sy : w SY = y := by simp (disch := decide) only [w, upd_self]
      intro a hk
      rw [p8, (add_vals w hwd).1, pw, sx, sy, addAffine_eq,
        ← baseEntry_eq hne x y hx.symm hy.symm]
      exact pointAdd_rep (hrep a hk) (Proof.Ed448.WnafWide.baseEntry_rep (by omega)
        (Proof.Ed448.WnafWide.digit_zero_or_odd false _))
  · have hz' : digitAt false S n = 0 := by rw [i3] at hz; simpa using hz
    refine WP.block_nil ⟨⟨_, by rw [m1]; exact C1⟩, by rw [m1]; exact hd, fun a hk => ?_⟩
    beta_reduce
    rw [m1, hz', zero_smul, add_zero]
    exact hrep a hk


/-- The selected key entry, negated as the code does. -/
theorem keyEntry_eq {d : Int} (p : Point) :
    Proof.Ed448.WnafWide.signedPoint (decide (d < 0)) p = ⟨if d < 0 then p.X - p.X - p.X else p.X, p.Y, p.Z⟩ := by
  unfold Proof.Ed448.WnafWide.signedPoint
  by_cases hn : d < 0
  · rw [decide_eq_true hn, ite_eq_left rfl, ite_eq_left hn]
    simp only [Proof.Ed448.negPoint]
    rw [sub_self]
  · rw [decide_eq_false hn, ite_eq_right Bool.false_ne_true, ite_eq_right hn]

theorem key_rep {a : VG.Proof.EdwardsLaw.EPoint dZ} {m : Mem} (hk : KeyOk b a m) {d : Int} (hd : d ≠ 0)
    (h1 : -15 ≤ d) (h2 : d ≤ 15) (ho : d = 0 ∨ d.natAbs % 2 = 1) :
    Rep (Proof.Ed448.WnafWide.signedPoint (decide (d < 0)) (kpt m b (d.natAbs / 2))) (d • a) := by
  have he : 2 * (d.natAbs / 2) + 1 = d.natAbs := by omega
  have h := hk (d.natAbs / 2) (by omega)
  rw [he] at h
  have hs := Proof.Ed448.WnafWide.signedPoint_rep h (decide (d < 0))
  rwa [Proof.Ed448.WnafWide.signed_abs] at hs

theorem addKey_ok {S K : Nat} {sL s : State} (hvL : VCtx b sL)
    (hfx : JFix b S K sL.mem) {n : Nat} (hn : n < 464) {t2v : BitVec 64}
    (hc : R64.Cur b sL t2v (BitVec.ofNat 64 n) DQ (FS s.mem b) s)
    {X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ}
    (hd : FS s.mem b DK = Spec.Ed448.d) (hrep : ∀ a, KeyOk b a sL.mem → Rep (ptOf (FS s.mem b)) (X a)) :
    WP isa addKey s (APost b sL n fun a => X a + digitAt false K n • a) := by
  have hA : ACC = 952 := rfl
  have hT : TB = 2104 := rfl
  have hK : KT = 3976 := rfl
  have hv := vctx_cur hvL hc
  obtain ⟨hdig, -⟩ := hfx
  obtain ⟨g1, g2⟩ := digit_range K n
  obtain ⟨i1, i2, i3⟩ := digit_dec g1 g2
  unfold addKey keyBody
  refine WP.seq (WP.mono (loadDigit_ok hv (n := n) (e := 3) (by omega) (by decide) hc.t1)
    fun s1 ⟨r1, m1, e5⟩ => ?_)
  have hb5 : s1.gpr .a5 = dByte (digitAt false K n) := by
    rw [e5, byte_hi hc.stp.frame (by omega) (by omega), dig_byte hdig (by omega) (.inr rfl),
      ite_eq_right (by decide)]
  have C1 := cur_regs hc r1 (by decide) (by decide) (by decide) m1
  refine WP.ite _ (by rw [eval_nonzero, hb5]) (fun hnz => ?_) (fun hz => ?_)
  · have hne : digitAt false K n ≠ 0 := by rw [i3] at hnz; simpa using hnz
    have hi : (digitAt false K n).natAbs / 2 < 8 := by omega
    rw [show digitIndex ++ [.shift .sll .d .t0 .a5 7, .shift .sll .d .a2 .a5 5, .add .t0 .t0 .a2,
        .shift .sll .d .a2 .a5 3, .add .t0 .t0 .a2, .add .t0 .t0 .a0, .addi .t2 .t0 (KT - OUT)] ++
        ldSlots .t2 0 [PX, PY, Impl.Ed448.RISCV64.PZ] =
      digitIndex ++ ([.shift .sll .d .t0 .a5 7, .shift .sll .d .a2 .a5 5, .add .t0 .t0 .a2,
        .shift .sll .d .a2 .a5 3, .add .t0 .t0 .a2, .add .t0 .t0 .a0, .addi .t2 .t0 (KT - OUT)] ++
        (cp7 .t2 0 .a3 PX ++ (cp7 .t2 56 .a3 PY ++ cp7 .t2 112 .a3 Impl.Ed448.RISCV64.PZ))) from rfl]
    refine WP.seq (WP.append (digitIndex_ok g1 g2 hb5) fun s2 ⟨r2, m2, a52, a62⟩ => ?_)
    have hv2 : VCtx b s2 :=
      hv.of_rest ((r1.mono (ws' := [.a1, .a5, .a6]) (by decide)).trans (r2.mono (by decide))) (by decide) (by decide)
    refine WP.append (ptrKey_ok hv2 hi a52) fun s3 ⟨r3, m3, t3⟩ => ?_
    have r23 : Rest [.a2, .a5, .a6, .t0, .t2] s1 s3 := (r2.mono (by decide)).trans (r3.mono (by decide))
    have C3 := cur_regs C1 r23 (by decide) (by decide) (by decide) (by rw [m3, m2])
    generalize hi' : (digitAt false K n).natAbs / 2 = i at t3 hi
    have kp : ∀ {t : State} {a' c' : BitVec 64} {qs : List Nat} {v : Nat → Fe}, R64.Cur b sL a' c' qs v t →
        kpt t.mem b i = kpt sL.mem b i := fun h => kpt_hi h.stp.frame hi
    refine WP.append (opCp (vctx_cur hvL C3) C3 (rs := .t2) (so := 0) (o := PX) (ps := KT + 168 * i)
      (by decide) (by decide) (by rw [BitVec.add_zero, t3]) (by omega) (by omega) (by decide) (by decide)
      (by simp only [PX]; omega)) fun s4 ⟨C4, q4⟩ => ?_
    refine WP.append (opCp (vctx_cur hvL C4) C4 (rs := .t2) (so := 56) (o := PY) (ps := KT + 168 * i + 56)
      (by decide) (by decide) (by rw [C4.t2, t3, Offset.add_add]) (by omega) (by omega) (by decide) (by decide)
      (by simp only [PY]; omega)) fun s5 ⟨C5, q5⟩ => ?_
    refine WP.mono (opCp (vctx_cur hvL C5) C5 (rs := .t2) (so := 112) (o := Impl.Ed448.RISCV64.PZ) (ps := KT + 168 * i + 112)
      (by decide) (by decide) (by rw [C5.t2, t3, Offset.add_add]) (by omega) (by omega) (by decide)
      (by decide) (by simp only [Impl.Ed448.RISCV64.PZ]; omega)) fun s6 ⟨C6, q6⟩ => ?_
    have kx : FS s3.mem b (KT + 168 * i) = (kpt sL.mem b i).X := by rw [← kp C3]; rfl
    have ky : FS s4.mem b (KT + 168 * i + 56) = (kpt sL.mem b i).Y := by rw [← kp C4]; rfl
    have kz : FS s5.mem b (KT + 168 * i + 112) = (kpt sL.mem b i).Z := by rw [← kp C5]; rfl
    rw [kx, ky, kz] at C6
    -- The negation.
    have a66 : s6.gpr .a6 = if digitAt false K n < 0 then BitVec.allOnes 64 else 0 := by
      rw [q6.gpr _ (by decide), q5.gpr _ (by decide), q4.gpr _ (by decide), r3.gpr _ (by decide), a62]
    let r : Point := ptOf (FS s.mem b)
    let p : Point := Proof.Ed448.WnafWide.signedPoint (decide (digitAt false K n < 0)) (kpt sL.mem b i)
    have neg : WP isa (.ite (.nonzero .a6) (.block (Impl.X448.RISCV64.R64.sub TA PX PX ++
        Impl.X448.RISCV64.R64.sub PX TA PX)) (.block [])) s6
        (R64.Cur b sL (s3.gpr .t2) (BitVec.ofNat 64 n) SQ (ptV r p)) := by
      have pe := keyEntry_eq (d := digitAt false K n) (kpt sL.mem b i)
      have hd' : FS s.mem b 336 = Spec.Ed448.d := hd
      by_cases hneg : digitAt false K n < 0
      · refine WP.ite true (by rw [eval_nonzero, a66, ite_eq_left hneg]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
        refine WP.append (R64.opSub (o := TA) (x := PX) (y := PX) (by decide) (by decide) (by decide) (by decide) C6)
          fun s7 C7 => WP.mono (R64.opSub (o := PX) (x := TA) (y := PX) (by decide) (by decide) (by decide)
            (by decide) C7) fun s8 C8 => C8.congr (by decide) fun q hq => ?_
        simp only [SQ, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := decide) only [ptV, p, pe, ite_eq_left hneg, upd_self, upd_of_ne, r, ptOf, RX, RY, RZ, PX,
            PY, Impl.Ed448.RISCV64.PZ, DK, TA, Impl.X448.RISCV64.X2, Impl.X448.RISCV64.Z2, Nat.reduceEqDiff, ↓reduceIte, hd']
      · refine WP.ite false (by rw [eval_nonzero, a66, ite_eq_right hneg]; rfl) (fun h => absurd h (by decide))
          (fun _ => WP.block_nil (C6.congr (by decide) fun q hq => ?_))
        simp only [SQ, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := decide) only [ptV, p, pe, ite_eq_right hneg, upd_self, upd_of_ne, r, ptOf, RX, RY, RZ, PX,
            PY, Impl.Ed448.RISCV64.PZ, DK, Impl.X448.RISCV64.X2, Impl.X448.RISCV64.Z2, Nat.reduceEqDiff, ↓reduceIte, hd']
    refine WP.seq (WP.mono neg fun s7 C7 => ?_)
    obtain ⟨o1, o2, o3, o4⟩ := last_ok
    rw [addition_eq]
    refine WP.seq (R64.ops_ok Proof.Ed448.RISCV64.addOps SQ _ s7 addOps_ok C7 fun s8 C8 =>
      WP.mono (R64.op_ok (.mul TZ TF TG) o1 o2 o3 o4 C8) fun s9 C9 => ?_)
    -- `T` into `R`.
    obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := addV_vals r p
    have C9' : R64.Cur b sL (s3.gpr .t2) (BitVec.ofNat 64 n) FQ (addV r p) s9 := C9
    rw [show copySlot RX TX ++ copySlot RY TY ++ copySlot RZ TZ =
      cp7 .a3 TX .a3 RX ++ (cp7 .a3 TY .a3 RY ++ cp7 .a3 TZ .a3 RZ) from rfl]
    have a3 : ∀ {t : State} {a' c' : BitVec 64} {qs : List Nat} {v : Nat → Fe}, R64.Cur b sL a' c' qs v t →
        ∀ o, t.gpr .a3 + BitVec.ofNat 64 o = b + BitVec.ofNat 64 o := fun h o => by rw [h.ctx.a3]
    refine WP.append (opCp (vctx_cur hvL C9') C9' (rs := .a3) (so := TX) (o := RX) (ps := TX) (by decide) (by decide)
      (a3 C9' _) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u1 ⟨D1, _⟩ => ?_
    refine WP.append (opCp (vctx_cur hvL D1) D1 (rs := .a3) (so := TY) (o := RY) (ps := TY) (by decide) (by decide)
      (a3 D1 _) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u2 ⟨D2, _⟩ => ?_
    refine WP.mono (opCp (vctx_cur hvL D2) D2 (rs := .a3) (so := TZ) (o := RZ) (ps := TZ) (by decide) (by decide)
      (a3 D2 _) (by decide) (by decide) (by decide) (by decide) (by decide)) fun u3 ⟨D3, _⟩ => ?_
    have f1 : FS s9.mem b TX = (Spec.Ed448.pointAdd r p).X := by rw [C9'.slots TX (by decide), v5]
    have f2 : FS u1.mem b TY = (Spec.Ed448.pointAdd r p).Y := by rw [D1.slots TY (by decide)]; simp (disch := decide) only [upd_of_ne, v6]
    have f3 : FS u2.mem b TZ = (Spec.Ed448.pointAdd r p).Z := by rw [D2.slots TZ (by decide)]; simp (disch := decide) only [upd_of_ne, v7]
    refine ⟨⟨_, cur_fs D3 (by decide)⟩, ?_, ?_⟩
    · rw [D3.slots DK (by decide)]; simp (disch := decide) only [upd_of_ne, v4]
    · have e : ptOf (FS u3.mem b) = Spec.Ed448.pointAdd r p := by
        simp only [ptOf]
        rw [D3.slots RX (by decide), D3.slots RY (by decide), D3.slots RZ (by decide)]
        simp (disch := decide) only [upd_self, upd_of_ne, f1, f2, f3]
      intro a hkey
      rw [e]
      have hk := key_rep hkey hne g1 g2 (Proof.Ed448.WnafWide.digit_zero_or_odd false _)
      rw [hi'] at hk
      exact pointAdd_rep (hrep a hkey) hk
  · have hz' : digitAt false K n = 0 := by rw [i3] at hz; simpa using hz
    refine WP.block_nil ⟨⟨_, by rw [m1]; exact C1⟩, by rw [m1]; exact hd, fun a hk => ?_⟩
    beta_reduce
    rw [m1, hz', zero_smul, add_zero]
    exact hrep a hk


/-! ## The loop -/

/-- Before the position `n - 1` (with `n` left): `R` represents `[residual S n]B + [residual K n]a`. -/
def WInv (b : Addr) (S K : Nat) (sL : State) (n : Nat) : State → Prop :=
  APost b sL n fun a => (residual false S n : Int) • baseAff + (residual false K n : Int) • a

theorem round_eq (S K n : Nat) (a : VG.Proof.EdwardsLaw.EPoint dZ) :
    ((residual false S (n + 1) : Int) • baseAff + (residual false K (n + 1) : Int) • a) +
        ((residual false S (n + 1) : Int) • baseAff + (residual false K (n + 1) : Int) • a) +
        digitAt false S n • baseAff + digitAt false K n • a =
      (residual false S n : Int) • baseAff + (residual false K n : Int) • a := by
  rw [Proof.Ed448.WnafWide.residual_step false S n, Proof.Ed448.WnafWide.residual_step false K n, add_zsmul,
    add_zsmul, mul_smul, mul_smul, two_zsmul, two_zsmul]
  abel

/-- The counter decremented. -/
theorem decStep_ok {S K : Nat} {sL : State} {n : Nat} (hn : n < 464) {s : State} (h : WInv b S K sL (n + 1) s) :
    WP isa (.block [.addi .t1 .t1 (-1)]) s fun t =>
      (∃ t2', R64.Cur b sL t2' (BitVec.ofNat 64 n) DQ (FS t.mem b) t) ∧ FS t.mem b DK = Spec.Ed448.d ∧
      (∀ a, KeyOk b a sL.mem → Rep (ptOf (FS t.mem b))
        ((residual false S (n + 1) : Int) • baseAff + (residual false K (n + 1) : Int) • a)) := by
  obtain ⟨⟨t2', hc⟩, hd, hrep⟩ := h
  refine wp_subi (by decide) fun s1 u1 => WP.block_nil ⟨⟨t2',
    ⟨hc.ctx.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide),
      hc.stp.trans (R64.Stp.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide) u1.mem),
      by rw [u1.other _ (by decide), hc.t2],
      by rw [u1.gpr, hc.t1, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel],
      by rw [u1.mem]; exact hc.slots⟩⟩, by rw [u1.mem]; exact hd, fun a hk => by rw [u1.mem]; exact hrep a hk⟩

/-- The doubling. -/
theorem dblStep_ok {sL : State} {n : Nat} {s : State} {t2' : BitVec 64}
    (hc : R64.Cur b sL t2' (BitVec.ofNat 64 n) DQ (FS s.mem b) s) (hd : FS s.mem b DK = Spec.Ed448.d)
    {X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ}
    (hrep : ∀ a, KeyOk b a sL.mem → Rep (ptOf (FS s.mem b)) (X a)) :
    WP isa (opsProg dblOps) s (APost b sL n fun a => X a + X a) := by
  rw [opsProg_eq]
  refine R64.ops_ok _ DQ _ s dbl_ok hc fun s2 C2 => WP.block_nil ⟨⟨_, cur_fs C2 dbl_sub⟩, ?_, fun a hk => ?_⟩
  · rw [C2.slots DK (dbl_sub DK (by decide)), (dbl_vals _).2, hd]
  · have e : ptOf (FS s2.mem b) = Proof.Ed448.double (ptOf (FS s.mem b)) := by
      have e' : ptOf (FS s2.mem b) = ptOf (runOps (dblOps.map toF) (FS s.mem b)) := by
        simp only [ptOf]
        rw [C2.slots RX (dbl_sub RX (by decide)), C2.slots RY (dbl_sub RY (by decide)),
          C2.slots RZ (dbl_sub RZ (by decide))]
      rw [e', (dbl_vals _).1]
    rw [e]; exact double_rep (hrep a hk)

theorem jointStep_ok {S K : Nat} {sL : State} (hvL : VCtx b sL)
    (hfx : JFix b S K sL.mem) {n : Nat} (hn : n < 464) {s : State} (h : WInv b S K sL (n + 1) s) :
    WP isa jointStep s fun t => WInv b S K sL n t ∧ (t.gpr .t1 != 0) = decide (n ≠ 0) := by
  unfold jointStep
  refine WP.seq (WP.mono (decStep_ok hn h) fun s1 ⟨⟨t2', C1⟩, d1, r1⟩ =>
    WP.seq (WP.mono (dblStep_ok C1 d1 r1) fun s2 ⟨⟨_, C2⟩, d2, r2⟩ =>
      WP.seq (WP.mono (addBase_ok hvL hfx hn C2 d2 r2) fun s3 ⟨⟨_, C3⟩, d3, r3⟩ =>
        WP.mono (addKey_ok hvL hfx hn C3 d3 r3) fun s4 ⟨⟨t4, C4⟩, d4, r4⟩ => ?_)))
  refine ⟨⟨⟨t4, C4⟩, d4, fun a hk => ?_⟩, by rw [C4.t1, ofNat_ne_zero (by omega)]⟩
  beta_reduce
  rw [← round_eq S K n a]
  exact r4 a hk

theorem jointLoop_ok {S K : Nat} {sL : State} (hvL : VCtx b sL)
    (hfx : JFix b S K sL.mem) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 464 → WInv b S K sL n s →
      WP isa (.loop jointStep (.nonzero .t1)) s (WInv b S K sL 0) := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := WInv b S K sL 0)
    (fun m s => 1 ≤ m ∧ m ≤ 464 ∧ WInv b S K sL m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hl⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (jointStep_ok hvL hfx (by omega) hl) fun s' ⟨hl', hz⟩ => ?_
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    exact .inl ⟨by rw [eval_nonzero, hz]; simp, hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [show t ≠ 0 by omega], t, by omega, by omega, by omega, hl'⟩


/-! ## The key table -/

/-- An element apart from a frame's regions stays. -/
theorem fsD {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {q : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 q, 56⟩ r) : FS m' b q = FS m b q := by
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => (hd r hr).sub_left (Offset.sub b (d := q + 4 * k) (n := 4) (e := q) (k := 56)
      (by omega) (by omega))
  rw [FS, V, val32_congr e]; rfl

/-- The point at the offsets `ox`, `oy`, `oz`. -/
def Pt (m : Mem) (b : Addr) (ox oy oz : Nat) (p : Point) : Prop :=
  FS m b ox = p.X ∧ FS m b oy = p.Y ∧ FS m b oz = p.Z

/-- Three regions of 56 bytes. -/
abbrev R3 (b : Addr) (x y z : Nat) : List Region :=
  [⟨b + BitVec.ofNat 64 x, 56⟩, ⟨b + BitVec.ofNat 64 y, 56⟩, ⟨b + BitVec.ofNat 64 z, 56⟩]

theorem pt_keep {m m' : Mem} {x y z ox oy oz : Nat} (hf : Frame (R3 b x y z) m m') {p : Point}
    (h : Pt m b ox oy oz p) (hb : ox + 56 ≤ 8192 ∧ oy + 56 ≤ 8192 ∧ oz + 56 ≤ 8192 ∧ x + 56 ≤ 8192 ∧ y + 56 ≤ 8192 ∧
      z + 56 ≤ 8192)
    (hd : ∀ o ∈ [ox, oy, oz], ∀ w ∈ [x, y, z], o + 56 ≤ w ∨ w + 56 ≤ o) : Pt m' b ox oy oz p := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have k : ∀ o ∈ [ox, oy, oz], o + 56 ≤ 8192 → FS m' b o = FS m b o := fun o ho hob =>
    fsD hf fun r hr => by
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hw := hd o ho
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (hw x (by simp)) (by omega) (by omega)
      · exact Offset.disjoint _ (hw y (by simp)) (by omega) (by omega)
      · exact Offset.disjoint _ (hw z (by simp)) (by omega) (by omega)
  exact ⟨by rw [k ox (by simp) b1]; exact h.1, by rw [k oy (by simp) b2]; exact h.2.1,
    by rw [k oz (by simp) b3]; exact h.2.2⟩

/-- Three copies, of the point at `(x, y, z)` (from `rs`) to `(X, Y, Z)` (from `rd`). -/
theorem copy3_ok {s : State} (hv : VCtx b s) {rs rd : Reg} (hrs : rs ≠ .a4) (hrd : rd ≠ .a4)
    {sx sy sz dx dy dz x y z X Y Z : Nat} (hso : sx + 48 < 2048 ∧ sy + 48 < 2048 ∧ sz + 48 < 2048)
    (hdo : dx + 48 < 2048 ∧ dy + 48 < 2048 ∧ dz + 48 < 2048)
    (hs : ∀ o p, (o, p) ∈ [(sx, x), (sy, y), (sz, z)] → s.gpr rs + BitVec.ofNat 64 o = b + BitVec.ofNat 64 p)
    (hd : ∀ o p, (o, p) ∈ [(dx, X), (dy, Y), (dz, Z)] → s.gpr rd + BitVec.ofNat 64 o = b + BitVec.ofNat 64 p)
    (h8 : ∀ o ∈ [x, y, z, X, Y, Z], o % 8 = 0 ∧ o + 56 ≤ 8184)
    (hsep : ∀ o ∈ [x, y, z], ∀ w ∈ [X, Y, Z], o + 56 ≤ w ∨ w + 56 ≤ o)
    (hXY : X + 56 ≤ Y ∨ Y + 56 ≤ X) (hXZ : X + 56 ≤ Z ∨ Z + 56 ≤ X) (hYZ : Y + 56 ≤ Z ∨ Z + 56 ≤ Y)
    {p : Point} (hp : Pt s.mem b x y z p) :
    WP isa (.block (cp7 rs sx rd dx ++ (cp7 rs sy rd dy ++ cp7 rs sz rd dz))) s fun t =>
      VCtx b t ∧ Rest [.a4] s t ∧ Frame (R3 b X Y Z) s.mem t.mem ∧ Pt t.mem b X Y Z p := by
  have g : ∀ o ∈ [x, y, z, X, Y, Z], o % 8 = 0 := fun o ho => (h8 o ho).1
  have l : ∀ o ∈ [x, y, z, X, Y, Z], o + 56 ≤ 8184 := fun o ho => (h8 o ho).2
  have fx := l x (by simp); have fy := l y (by simp); have fz := l z (by simp)
  have fX := l X (by simp); have fY := l Y (by simp); have fZ := l Z (by simp)
  refine WP.append (cp7_ok hv hrs hrd hso.1 hdo.1 (hs _ _ (by simp)) (hd _ _ (by simp)) (g x (by simp))
    (g X (by simp)) fx fX (hsep x (by simp) X (by simp))) fun s1 ⟨v1, r1, f1, d1⟩ => ?_
  have e1 : ∀ {r : Reg}, r ≠ .a4 → s1.gpr r = s.gpr r := fun h => r1.gpr _ (by simpa using h)
  refine WP.append (cp7_ok v1 hrs hrd hso.2.1 hdo.2.1 (by rw [e1 hrs]; exact hs _ _ (by simp))
    (by rw [e1 hrd]; exact hd _ _ (by simp)) (g y (by simp)) (g Y (by simp)) fy fY (hsep y (by simp) Y (by simp)))
    fun s2 ⟨v2, r2, f2, d2⟩ => ?_
  have e2 : ∀ {r : Reg}, r ≠ .a4 → s2.gpr r = s.gpr r := fun h => (r2.gpr _ (by simpa using h)).trans (e1 h)
  refine WP.mono (cp7_ok v2 hrs hrd hso.2.2 hdo.2.2 (by rw [e2 hrs]; exact hs _ _ (by simp))
    (by rw [e2 hrd]; exact hd _ _ (by simp)) (g z (by simp)) (g Z (by simp)) fz fZ (hsep z (by simp) Z (by simp)))
    fun s3 ⟨v3, r3, f3, d3⟩ => ⟨v3, r1.trans (r2.trans r3), ?_, ?_⟩
  · have s1' : Frame (R3 b X Y Z) s.mem s1.mem := f1.mono fun r hr => by simp [List.mem_singleton.mp hr]
    have s2' : Frame (R3 b X Y Z) s1.mem s2.mem := f2.mono fun r hr => by simp [List.mem_singleton.mp hr]
    have s3' : Frame (R3 b X Y Z) s2.mem s3.mem := f3.mono fun r hr => by simp [List.mem_singleton.mp hr]
    exact s1'.trans (s2'.trans s3')
  · have dj : ∀ {o w : Nat}, o + 56 ≤ w ∨ w + 56 ≤ o → o + 56 ≤ 8192 → w + 56 ≤ 8192 →
        ∀ r ∈ [(⟨b + BitVec.ofNat 64 w, 56⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 o, 56⟩ r :=
      fun h ho hw r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ h (by omega) (by omega)
    have y1 : FS s1.mem b y = FS s.mem b y :=
      fsD f1 (dj (hsep y (by simp) X (by simp)) (by omega) (by omega))
    have z1 : FS s1.mem b z = FS s.mem b z :=
      fsD f1 (dj (hsep z (by simp) X (by simp)) (by omega) (by omega))
    have z2 : FS s2.mem b z = FS s1.mem b z :=
      fsD f2 (dj (hsep z (by simp) Y (by simp)) (by omega) (by omega))
    have X2 : FS s2.mem b X = FS s1.mem b X := fsD f2 (dj hXY (by omega) (by omega))
    have X3 : FS s3.mem b X = FS s2.mem b X := fsD f3 (dj hXZ (by omega) (by omega))
    have Y3 : FS s3.mem b Y = FS s2.mem b Y := fsD f3 (dj hYZ (by omega) (by omega))
    refine ⟨?_, ?_, ?_⟩
    · rw [X3, X2, FS, cp7_V d1]; exact hp.1
    · rw [Y3, FS, cp7_V d2, ← FS, y1]; exact hp.2.1
    · rw [FS, cp7_V d3, ← FS, z2, z1]; exact hp.2.2


/-- The entries: `-A` (`p`), then each the last plus `d = [2](-A)`. -/
def kE (p d : Point) : Nat → Point
  | 0 => p
  | e + 1 => Spec.Ed448.pointAdd (kE p d e) d

theorem kE_rep {p : Point} {a : VG.Proof.EdwardsLaw.EPoint dZ} (h : Rep p a) :
    ∀ e, Rep (kE p (Proof.Ed448.double p) e) ((2 * e + 1) • a)
  | 0 => by simpa only [kE, Nat.mul_zero, Nat.zero_add, one_nsmul] using h
  | e + 1 => by
    have hh := pointAdd_rep (kE_rep h e) (double_rep h)
    rw [← two_nsmul, ← add_nsmul] at hh
    simpa only [kE, show 2 * e + 1 + 2 = 2 * (e + 1) + 1 by omega] using hh

theorem addV_P (r p : Point) : addV r p PX = p.X ∧ addV r p PY = p.Y ∧ addV r p Impl.Ed448.RISCV64.PZ = p.Z := by
  simp only [addV, Proof.Ed448.RISCV64.addOps, runOps, FOp.out, upd, ptV, RX, RY, RZ, PX, PY,
    Impl.Ed448.RISCV64.PZ, DK, TX, TY, TZ, TA, TC, TD, TF, TG, TH, Impl.X448.RISCV64.X2, Impl.X448.RISCV64.Z2,
    Impl.X448.RISCV64.R, Nat.reduceEqDiff, ↓reduceIte, and_self]

/-- The key table's region. -/
abbrev KR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 KT, 1344⟩

/-- After `j + 1` entries, from `sK`. -/
def KInv (b : Addr) (sK : State) (p d : Point) (j : Nat) (s : State) : Prop :=
  VCtx b s ∧ Rest R64.work sK s ∧ Frame [FA b, KR b] sK.mem s.mem ∧
    s.gpr .t2 = b + BitVec.ofNat 64 (KT + 168 * j) ∧ s.gpr .t1 = BitVec.ofNat 64 (7 - j) ∧
    Pt s.mem b RX RY RZ (kE p d j) ∧ Pt s.mem b PX PY Impl.Ed448.RISCV64.PZ d ∧ FS s.mem b DK = Spec.Ed448.d ∧
    ∀ e ≤ j, kpt s.mem b e = kE p d e

theorem frame_R3_FA {m m' : Mem} {x y z : Nat} (hf : Frame (R3 b x y z) m m') (hx : x + 56 ≤ 1064)
    (hy : y + 56 ≤ 1064) (hz : z + 56 ≤ 1064) : Frame [FA b, KR b] m m' :=
  hf.sub fun r hr => ⟨FA b, by simp, by
    have hA : ACC = 952 := rfl
    simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Offset.sub_base _ (by omega)⟩

theorem frame_R3_KR {m m' : Mem} {e : Nat} (he : e < 8)
    (hf : Frame (R3 b (KT + 168 * e) (KT + 168 * e + 56) (KT + 168 * e + 112)) m m') : Frame [FA b, KR b] m m' :=
  hf.sub fun r hr => ⟨KR b, by simp, by
    have hK : KT = 3976 := rfl
    have := he
    simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)⟩

theorem frame_FA_K {m m' : Mem} (hf : Frame [FA b] m m') : Frame [FA b, KR b] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem kpt_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {e : Nat}
    (hd : ∀ o ∈ [KT + 168 * e, KT + 168 * e + 56, KT + 168 * e + 112], ∀ r ∈ rs,
      Region.Disjoint ⟨b + BitVec.ofNat 64 o, 56⟩ r) : kpt m' b e = kpt m b e := by
  simp only [kpt]
  rw [fsD hf (hd _ (by simp)), fsD hf (hd _ (by simp)), fsD hf (hd _ (by simp))]

theorem keyStep_ok {sK : State} {p d : Point} {j : Nat} (hj : j < 7) {s : State}
    (h : KInv b sK p d j s) :
    WP isa keyStep s fun t => KInv b sK p d (j + 1) t ∧ (t.gpr .t1 != 0) = decide (7 - (j + 1) ≠ 0) := by
  have hA : ACC = 952 := rfl
  have hK : KT = 3976 := rfl
  have hTX : TX = 392 := rfl
  have hTY : TY = 448 := rfl
  have hTZ : TZ = 504 := rfl
  obtain ⟨hv, hr, hf, ht2, ht1, ⟨rx, ry, rz⟩, ⟨px, py, pz⟩, hdk, htab⟩ := h
  let r := kE p d j
  have C0 : R64.Cur b s (s.gpr .t2) (BitVec.ofNat 64 (7 - j)) SQ (ptV r d) s :=
    ⟨hv.ctx, R64.Stp.refl _ _, rfl, ht1, fun q hq => by
      simp only [SQ, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [ptV, RX, RY, RZ, PX, PY, Impl.Ed448.RISCV64.PZ, DK, Impl.X448.RISCV64.X2, Impl.X448.RISCV64.Z2,
          Nat.reduceEqDiff, ↓reduceIte]
      exacts [pz, py, px, rx, ry, rz, hdk]⟩
  obtain ⟨o1, o2, o3, o4⟩ := last_ok
  unfold keyStep
  rw [addition_eq]
  refine WP.seq (R64.ops_ok Proof.Ed448.RISCV64.addOps SQ _ s addOps_ok C0 fun s1 C1 =>
    WP.mono (R64.op_ok (.mul TZ TF TG) o1 o2 o3 o4 C1) fun s2 C2 => ?_)
  have C2' : R64.Cur b s (s.gpr .t2) (BitVec.ofNat 64 (7 - j)) FQ (addV r d) s2 := C2
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := addV_vals r d
  obtain ⟨w1, w2, w3⟩ := addV_P r d
  have hv2 : VCtx b s2 := vctx_cur hv C2'
  rw [show [Instr.addi .t2 .t2 168] ++ stSlots .t2 0 [TX, TY, TZ] ++ copySlot RX TX ++ copySlot RY TY ++
      copySlot RZ TZ ++ [.addi .t1 .t1 (-1)] =
    .addi .t2 .t2 168 :: ((cp7 .a3 TX .t2 0 ++ (cp7 .a3 TY .t2 56 ++ cp7 .a3 TZ .t2 112)) ++
      ((cp7 .a3 TX .a3 RX ++ (cp7 .a3 TY .a3 RY ++ cp7 .a3 TZ .a3 RZ)) ++ [.addi .t1 .t1 (-1)])) from rfl]
  refine wp_addi (by decide) fun s3 u3 => ?_
  have hv3 : VCtx b s3 := hv2.of_rest (u3.rest (ws := [.t2]) (by decide)) (by decide) (by decide)
  have e3 : s3.gpr .t2 = b + BitVec.ofNat 64 (KT + 168 * (j + 1)) := by
    rw [u3.gpr, C2'.t2, ht2, Offset.add_add, show KT + 168 * j + 168 = KT + 168 * (j + 1) by omega]
  have hk : kE p d (j + 1) = Spec.Ed448.pointAdd r d := by simp only [kE, r]
  have hT : Pt s3.mem b TX TY TZ (kE p d (j + 1)) := by
    rw [u3.mem, hk]
    exact ⟨by rw [C2'.slots TX (by decide), v5], by rw [C2'.slots TY (by decide), v6],
      by rw [C2'.slots TZ (by decide), v7]⟩
  have a3 : ∀ o, s3.gpr .a3 + BitVec.ofNat 64 o = b + BitVec.ofNat 64 o := fun o => by rw [hv3.ctx.a3]
  refine WP.append (copy3_ok hv3 (rs := .a3) (rd := .t2) (by decide) (by decide) (by decide) (by decide)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
                      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact a3 _)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
                      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [e3, Offset.add_add] <;> congr 2)
    (X := KT + 168 * (j + 1)) (Y := KT + 168 * (j + 1) + 56) (Z := KT + 168 * (j + 1) + 112)
    (fun o ho => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
                    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun o ho w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    (by omega) (by omega) (by omega) hT) fun s4 ⟨hv4, r4, f4, k4⟩ => ?_
  have dj3 : ∀ {o x y z : Nat}, (∀ w ∈ [x, y, z], o + 56 ≤ w ∨ w + 56 ≤ o) → o + 56 ≤ 8192 →
      x + 56 ≤ 8192 → y + 56 ≤ 8192 → z + 56 ≤ 8192 →
      ∀ r ∈ R3 b x y z, Region.Disjoint ⟨b + BitVec.ofNat 64 o, 56⟩ r := fun h ho hx hy hz r hr => by
    simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (h _ (by simp)) (by omega) (by omega)
    · exact Offset.disjoint _ (h _ (by simp)) (by omega) (by omega)
    · exact Offset.disjoint _ (h _ (by simp)) (by omega) (by omega)
  have hT4 : Pt s4.mem b TX TY TZ (kE p d (j + 1)) := pt_keep f4 hT (by omega)
    (fun o ho w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  refine WP.append (copy3_ok hv4 (rs := .a3) (rd := .a3) (X := RX) (Y := RY) (Z := RZ) (by decide) (by decide)
    (by decide) (by decide)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
                      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv4.ctx.a3])
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
                      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv4.ctx.a3])
    (fun o ho => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
                    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun o ho w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    (by omega) (by omega) (by omega) hT4) fun s5 ⟨hv5, r5, f5, k5⟩ => ?_
  refine wp_subi (by decide) fun s6 u6 => WP.block_nil ?_
  have g5 : ∀ {q : Reg}, q ≠ .a4 → s5.gpr q = s3.gpr q := fun h =>
    (r5.gpr _ (by simpa using h)).trans (r4.gpr _ (by simpa using h))
  have t5 : s5.gpr .t1 = BitVec.ofNat 64 (7 - j) := by
    rw [g5 (by decide), u3.other _ (by decide), C2'.t1]
  have hPs : ∀ (m : Mem) (q : Nat), m = s2.mem → q = PX ∨ q = PY ∨ q = Impl.Ed448.RISCV64.PZ ∨ q = DK →
      FS m b q = FS s2.mem b q := fun m q hm _ => by rw [hm]
  -- The slots `P` and `d` stay through the stores and copies.
  have keep : ∀ q, (q = PX ∨ q = PY ∨ q = Impl.Ed448.RISCV64.PZ ∨ q = DK) → FS s6.mem b q = FS s2.mem b q := by
    intro q hq
    have hPX : PX = 168 := rfl
    have hPY : PY = 224 := rfl
    have hPZ : Impl.Ed448.RISCV64.PZ = 280 := rfl
    have hDK : DK = 336 := rfl
    have hq' : q = 168 ∨ q = 224 ∨ q = 280 ∨ q = 336 := by omega
    rw [u6.mem, fsD f5 (dj3 (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega) (by omega)),
      fsD f4 (dj3 (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega) (by omega)), u3.mem]
  have t6 : s6.gpr .t1 = BitVec.ofNat 64 (7 - (j + 1)) := by
    rw [u6.gpr, t5, ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  refine ⟨⟨hv5.of_rest (u6.rest (ws := [.t1]) (by decide)) (by decide) (by decide),
    hr.trans (C2'.stp.rest.trans ((u3.rest (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans
      (u6.rest (by decide)))))),
    hf.trans ((frame_FA_K C2'.stp.frame).trans (by
      rw [u6.mem, ← u3.mem]; exact (frame_R3_KR (e := j + 1) (by omega) f4).trans (frame_R3_FA f5 (by omega)
        (by omega) (by omega)))),
    by rw [u6.other _ (by decide), g5 (by decide), e3],
    t6,
    by rw [u6.mem]; exact k5,
    ⟨by rw [keep PX (by simp), C2'.slots PX (by decide), w1],
      by rw [keep PY (by simp), C2'.slots PY (by decide), w2],
      by rw [keep _ (by simp), C2'.slots Impl.Ed448.RISCV64.PZ (by decide), w3]⟩,
    by rw [keep DK (by simp), C2'.slots DK (by decide), v4], fun e he => ?_⟩,
    by rw [t6, ofNat_ne_zero (by omega)]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le he) with he' | rfl
  · -- An earlier entry stays.
    have he8 : e < 8 := by omega
    have dE : ∀ o ∈ [KT + 168 * e, KT + 168 * e + 56, KT + 168 * e + 112], ∀ w ∈ [KT + 168 * (j + 1),
        KT + 168 * (j + 1) + 56, KT + 168 * (j + 1) + 112], o + 56 ≤ w ∨ w + 56 ≤ o := fun o ho w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega
    rw [show s6.mem = s5.mem from u6.mem,
      kpt_keep f5 fun o ho r hr => dj3 (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; rcases ho with rfl | rfl | rfl <;> omega)
        (by omega) (by omega) (by omega) r hr,
      kpt_keep f4 fun o ho r hr => dj3 (dE o ho) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; rcases ho with rfl | rfl | rfl <;> omega)
        (by omega) (by omega) (by omega) r hr,
      u3.mem, kpt_hi C2'.stp.frame he8]
    exact htab e (by omega)
  · -- The new one.
    obtain ⟨n1, n2, n3⟩ := pt_keep f5 k4 (by omega) (fun o ho w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    simp only [kpt]
    rw [u6.mem, n1, n2, n3]



theorem pt_ptOf {m : Mem} {p : Point} (h : Pt m b RX RY RZ p) : ptOf (FS m b) = p := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ptOf, h1, h2, h3]

theorem keyHead_ok {s : State} (hv : VCtx b s) {p : Point} (hp : Pt s.mem b NAX NAY ONE p)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa keyHead s (KInv b s p (Proof.Ed448.double p) 0) := by
  have hA : ACC = 952 := rfl
  have hK : KT = 3976 := rfl
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  have hPX : PX = 168 := rfl
  have hPY : PY = 224 := rfl
  have hPZ : Impl.Ed448.RISCV64.PZ = 280 := rfl
  have hDK : DK = 336 := rfl
  have hNX : NAX = 1176 := rfl
  have hNY : NAY = 1232 := rfl
  have hON : ONE = 1400 := rfl
  have hO : OUT = 2048 := rfl
  have dj3 : ∀ {o x y z : Nat}, (∀ w ∈ [x, y, z], o + 56 ≤ w ∨ w + 56 ≤ o) → o + 56 ≤ 8192 →
      x + 56 ≤ 8192 → y + 56 ≤ 8192 → z + 56 ≤ 8192 →
      ∀ r ∈ R3 b x y z, Region.Disjoint ⟨b + BitVec.ofNat 64 o, 56⟩ r := fun h ho hx hy hz r hr => by
    simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (h _ (by simp)) (by omega) (by omega)
    · exact Offset.disjoint _ (h _ (by simp)) (by omega) (by omega)
    · exact Offset.disjoint _ (h _ (by simp)) (by omega) (by omega)
  unfold keyHead
  rw [show copySlot RX NAX ++ copySlot RY NAY ++ copySlot RZ ONE ++ [Instr.addi .t2 .a0 (KT - OUT)] ++
      stSlots .t2 0 [RX, RY, RZ] =
    (cp7 .a3 NAX .a3 RX ++ (cp7 .a3 NAY .a3 RY ++ cp7 .a3 ONE .a3 RZ)) ++
      (.addi .t2 .a0 (KT - OUT) :: (cp7 .a3 RX .t2 0 ++ (cp7 .a3 RY .t2 56 ++ cp7 .a3 RZ .t2 112))) from rfl]
  refine WP.seq (WP.append (copy3_ok hv (rs := .a3) (rd := .a3) (X := RX) (Y := RY) (Z := RZ) (by decide)
    (by decide) (by decide) (by decide)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv.ctx.a3])
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv.ctx.a3])
    (fun o ho => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun o ho w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    (by omega) (by omega) (by omega) hp) fun s1 ⟨hv1, r1, f1, k1⟩ => ?_)
  refine wp_addi (imm := KT - OUT) (by decide) fun s2 u2 => ?_
  have hv2 : VCtx b s2 := hv1.of_rest (u2.rest (ws := [.t2]) (by decide)) (by decide) (by decide)
  have e2 : s2.gpr .t2 = b + BitVec.ofNat 64 KT := by
    rw [u2.gpr, r1.gpr _ (by decide), hv.a0, Offset.add_add, hK, hO]
  have k2 : Pt s2.mem b RX RY RZ p := by rw [u2.mem]; exact k1
  refine WP.mono (copy3_ok hv2 (rs := .a3) (rd := .t2) (X := KT) (Y := KT + 56) (Z := KT + 112) (by decide)
    (by decide) (by decide) (by decide)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv2.ctx.a3])
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [e2, Offset.add_add, Nat.add_zero])
    (fun o ho => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun o ho w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    (by omega) (by omega) (by omega) k2) fun s3 ⟨hv3, r3, f3, k3⟩ => ?_
  -- The doubling.
  have k3r : Pt s3.mem b RX RY RZ p := pt_keep f3 k2 (by omega) (fun o ho w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
  have d3 : FS s3.mem b DK = Spec.Ed448.d := by
    rw [fsD f3 (dj3 (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega) (by omega)),
      u2.mem, fsD f1 (dj3 (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega) (by omega)), hd]
  have C3 : R64.Cur b s3 (s3.gpr .t2) (s3.gpr .t1) DQ (FS s3.mem b) s3 :=
    ⟨hv3.ctx, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [opsProg_eq]
  refine WP.seq (R64.ops_ok _ DQ _ s3 dbl_ok C3 fun s4 C4 => WP.block_nil ?_)
  have hv4 : VCtx b s4 := vctx_cur hv3 C4
  have p4 : Pt s4.mem b RX RY RZ (Proof.Ed448.double p) := by
    have e := (dbl_vals (FS s3.mem b)).1
    rw [pt_ptOf k3r] at e
    refine ⟨?_, ?_, ?_⟩
    · rw [C4.slots RX (dbl_sub RX (by decide)), ← e]; rfl
    · rw [C4.slots RY (dbl_sub RY (by decide)), ← e]; rfl
    · rw [C4.slots RZ (dbl_sub RZ (by decide)), ← e]; rfl
  have d4 : FS s4.mem b DK = Spec.Ed448.d := by
    rw [C4.slots DK (dbl_sub DK (by decide)), (dbl_vals _).2, d3]
  have e4 : s4.gpr .t2 = b + BitVec.ofNat 64 KT := by rw [C4.t2, r3.gpr _ (by decide), e2]
  have k4 : Pt s4.mem b KT (KT + 56) (KT + 112) p := by
    refine ⟨?_, ?_, ?_⟩
    · rw [fs_hi C4.stp.frame (by omega) (by omega)]; exact k3.1
    · rw [fs_hi C4.stp.frame (by omega) (by omega)]; exact k3.2.1
    · rw [fs_hi C4.stp.frame (by omega) (by omega)]; exact k3.2.2
  rw [show copySlot PX RX ++ copySlot PY RY ++ copySlot Impl.Ed448.RISCV64.PZ RZ ++ ldSlots .t2 0 [RX, RY, RZ] ++
      [Instr.li .t1 7] =
    (cp7 .a3 RX .a3 PX ++ (cp7 .a3 RY .a3 PY ++ cp7 .a3 RZ .a3 Impl.Ed448.RISCV64.PZ)) ++
      ((cp7 .t2 0 .a3 RX ++ (cp7 .t2 56 .a3 RY ++ cp7 .t2 112 .a3 RZ)) ++ [.li .t1 7]) from rfl]
  refine WP.append (copy3_ok hv4 (rs := .a3) (rd := .a3) (X := PX) (Y := PY) (Z := Impl.Ed448.RISCV64.PZ)
    (by decide) (by decide) (by decide) (by decide)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv4.ctx.a3])
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv4.ctx.a3])
    (fun o ho => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun o ho w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    (by omega) (by omega) (by omega) p4) fun s5 ⟨hv5, r5, f5, k5⟩ => ?_
  have k5' : Pt s5.mem b KT (KT + 56) (KT + 112) p := pt_keep f5 k4 (by omega) (fun o ho w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
  refine WP.append (copy3_ok hv5 (rs := .t2) (rd := .a3) (X := RX) (Y := RY) (Z := RZ)
    (by decide) (by decide) (by decide) (by decide)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [r5.gpr _ (by decide), e4, Offset.add_add] <;> rfl)
    (fun o q hm => by simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hv5.ctx.a3])
    (fun o ho => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun o ho w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    (by omega) (by omega) (by omega) k5') fun s6 ⟨hv6, r6, f6, k6⟩ => ?_
  refine wp_li (by decide) fun s7 u7 => WP.block_nil ?_
  have dkeep : ∀ {m m' : Mem} {x y z : Nat}, Frame (R3 b x y z) m m' → (∀ w ∈ [x, y, z], DK + 56 ≤ w ∨ w + 56 ≤ DK) →
      x + 56 ≤ 8192 → y + 56 ≤ 8192 → z + 56 ≤ 8192 → FS m' b DK = FS m b DK := fun hf h hx hy hz =>
    fsD hf (dj3 h (by omega) hx hy hz)
  refine ⟨hv6.of_rest (u7.rest (ws := [.t1]) (by decide)) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans ((r3.mono (by decide)).trans
      (C4.stp.rest.trans ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans (u7.rest (by decide)))))))
  · rw [u7.mem]
    refine (frame_R3_FA f1 (by omega) (by omega) (by omega)).trans ?_
    rw [← u2.mem]
    refine (frame_R3_KR (e := 0) (by decide) (by simpa using f3)).trans ((frame_FA_K C4.stp.frame).trans
      ((frame_R3_FA f5 (by omega) (by omega) (by omega)).trans (frame_R3_FA f6 (by omega) (by omega) (by omega))))
  · rw [u7.other _ (by decide), r6.gpr _ (by decide), r5.gpr _ (by decide), e4]; rfl
  · rw [u7.gpr]
  · rw [u7.mem]; exact k6
  · rw [u7.mem]
    exact pt_keep f6 k5 (by omega) (fun o ho w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
  · rw [u7.mem, dkeep f6 (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega),
      dkeep f5 (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega), d4]
  · intro e he
    obtain rfl : e = 0 := by omega
    obtain ⟨n1, n2, n3⟩ := pt_keep f6 k5' (by omega) (fun o ho w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hw; rcases ho with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> omega)
    simp only [kpt, kE, Nat.mul_zero, Nat.add_zero]
    rw [u7.mem, n1, n2, n3]

theorem keyTable_ok {s : State} (hv : VCtx b s) {p : Point} (hp : Pt s.mem b NAX NAY ONE p)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa keyTable s (KInv b s p (Proof.Ed448.double p) 7) := by
  unfold keyTable
  refine WP.seq (WP.mono (keyHead_ok hv hp hd) fun s1 h1 => ?_)
  refine WP.loop (M := isa) (Q := KInv b s p (Proof.Ed448.double p) 7)
    (fun m t => ∃ j, m = 7 - j ∧ j < 7 ∧ KInv b s p (Proof.Ed448.double p) j t) ?_ 7 s1 ⟨0, rfl, by decide, h1⟩
  rintro m t ⟨j, rfl, hj, ht⟩
  refine WP.mono (keyStep_ok hj ht) fun t' ⟨ht', hz⟩ => ?_
  by_cases h7 : j + 1 = 7
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h7], by rw [h7] at ht'; exact ht'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega, 7 - (j + 1), by omega, j + 1, rfl, by omega, ht'⟩

theorem keyOk_of {sK t : State} {p : Point} {a : VG.Proof.EdwardsLaw.EPoint dZ} (hp : Rep p a)
    (h : KInv b sK p (Proof.Ed448.double p) 7 t) : KeyOk b a t.mem := fun i hi => by
  rw [h.2.2.2.2.2.2.2.2 i (by omega)]
  exact kE_rep hp i


/-! ## The loop's start and end -/

theorem jfix_FA {S K : Nat} {m m' : Mem} (hf : Frame [FA b] m m') (h : JFix b S K m) : JFix b S K m' := by
  have hA : ACC = 952 := rfl
  have hT : TB = 2104 := rfl
  have hB : BT = 5320 := rfl
  refine ⟨fun h' hh => by rw [byte_hi hf (by omega) (by omega)]; exact h.1 h' hh, fun i hi => ?_⟩
  have k : ∀ o, ACC + 112 ≤ o → o + 56 ≤ 8192 → V m' b o = V m b o := fun o h1 h2 => by
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base b (by omega) (by omega))
  rw [k _ (by omega) (by omega), k _ (by omega) (by omega)]
  exact h.2 i hi

theorem keyOk_FA {a : VG.Proof.EdwardsLaw.EPoint dZ} {m m' : Mem} (hf : Frame [FA b] m m') (h : KeyOk b a m) :
    KeyOk b a m' := fun i hi => by rw [kpt_hi hf hi]; exact h i hi

theorem residual_464 {k : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) : residual false k 464 = 0 :=
  Proof.Ed448.WnafWide.residual_end false hk

/-- `R` the neutral point, and the counter. -/
theorem jointInit_ok {s : State} (hv : VCtx b s) :
    WP isa (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ ([.li .t1 464] : List Instr))) s fun t =>
      VCtx b t ∧ Rest [.a4, .t1] s t ∧ Frame (R3 b RX RY RZ) s.mem t.mem ∧
      ptOf (FS t.mem b) = Spec.Ed448.identity ∧ t.gpr .t1 = BitVec.ofNat 64 464 := by
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  simp only [List.append_assoc]
  refine WP.append (constField_ok hv.ctx (o := RX) (by decide) (by decide) (v := 0) (by decide))
    fun s1 ⟨r1, f1, v1⟩ => ?_
  have hv1 : VCtx b s1 := hv.of_rest r1 (by decide) (by decide)
  refine WP.append (constField_ok hv1.ctx (o := RY) (by decide) (by decide) (v := 1) (by decide))
    fun s2 ⟨r2, f2, v2⟩ => ?_
  have hv2 : VCtx b s2 := hv1.of_rest r2 (by decide) (by decide)
  refine WP.append (constField_ok hv2.ctx (o := RZ) (by decide) (by decide) (v := 1) (by decide))
    fun s3 ⟨r3, f3, v3⟩ => ?_
  have hv3 : VCtx b s3 := hv2.of_rest r3 (by decide) (by decide)
  refine wp_li (by decide) fun t u => WP.block_nil ⟨hv3.of_rest (u.rest (ws := [.t1]) (by decide)) (by decide)
    (by decide), (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      (u.rest (by decide)))), ?_, ?_, u.gpr⟩
  · rw [u.mem]
    exact (f1.mono (by simp)).trans ((f2.mono (by simp)).trans (f3.mono (by simp)))
  · simp only [ptOf, Spec.Ed448.identity]
    rw [u.mem, FS, FS, FS, slot_keep f3 (by omega) (by omega) (by omega), slot_keep f2 (by omega) (by omega) (by omega),
      v1, slot_keep f3 (by omega) (by omega) (by omega), v2, v3, Proof.X448.toFe_one]
    rfl

/-- The joint loop from `s`: `R` represents `[S]B + [K]a`. -/
theorem joint_ok {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    {s : State} (hv : VCtx b s)
    (hfx : JFix b S K s.mem) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa jointLoop s fun t => ∃ sL, VCtx b sL ∧ Frame [FA b] s.mem sL.mem ∧ Rest [.a4, .t1] s sL ∧
      WInv b S K sL 0 t := by
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  have hDK : DK = 336 := rfl
  unfold jointLoop
  refine WP.seq (WP.mono (jointInit_ok hv) fun sL ⟨hvL, rL, fL, pL, tL⟩ => ?_)
  have fFA : Frame [FA b] s.mem sL.mem := fL.sub fun r hr => ⟨FA b, by simp, by
    have hA : ACC = 952 := rfl
    simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Offset.sub_base _ (by omega)⟩
  have dL : FS sL.mem b DK = Spec.Ed448.d := by
    rw [fsD fL fun r hr => by
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega), hd]
  refine WP.mono (jointLoop_ok hvL (jfix_FA fFA hfx) 464 sL (by decide) (le_refl _)
    ⟨⟨_, ⟨hvL.ctx, R64.Stp.refl _ _, rfl, tL, fun _ _ => rfl⟩⟩, dL, fun a _ => ?_⟩) fun t ht => ⟨sL, hvL, fFA, rL, ht⟩
  beta_reduce
  rw [pL, residual_464 hS, residual_464 hK]
  simpa only [Nat.cast_zero, zero_smul, add_zero] using Proof.Ed448.identity_rep

/-- `R = [4](R + (x, y))`, in the slots `vFinish` reads. -/
theorem addNegR_ok {sL s : State} (hvL : VCtx b sL) {t2v c : BitVec 64}
    (hc : R64.Cur b sL t2v c DQ (FS s.mem b) s) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa addNegR s fun t => VCtx b t ∧ R64.Stp b sL t ∧
      SlotsOk t.mem b RQ (ptV (Proof.Ed448.double (Proof.Ed448.double (Spec.Ed448.pointAdd (ptOf (FS s.mem b))
        ⟨FS s.mem b NRX, FS s.mem b NRY, 1⟩)))
        (Proof.Ed448.double (Proof.Ed448.double (Spec.Ed448.pointAdd (ptOf (FS s.mem b))
          ⟨FS s.mem b NRX, FS s.mem b NRY, 1⟩)))) := by
  have hA : ACC = 952 := rfl
  have hNX : NRX = 1288 := rfl
  have hNY : NRY = 1344 := rfl
  have hv := vctx_cur hvL hc
  unfold addNegR
  rw [show copySlot SX NRX ++ copySlot SY NRY = cp7 .a3 NRX .a3 SX ++ cp7 .a3 NRY .a3 SY from rfl]
  refine WP.seq (WP.append (opCp hv hc (rs := .a3) (so := NRX) (o := SX) (ps := NRX) (by decide) (by decide)
    (by rw [hc.ctx.a3]) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s1 ⟨C1, _⟩ =>
    WP.mono (opCp (vctx_cur hvL C1) C1 (rs := .a3) (so := NRY) (o := SY) (ps := NRY) (by decide) (by decide)
      (by rw [C1.ctx.a3]) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s2 ⟨C2, _⟩ => ?_)
  have ky : FS s1.mem b NRY = FS s.mem b NRY := by
    rw [fs_hi C1.stp.frame (by omega) (by omega), fs_hi hc.stp.frame (by omega) (by omega)]
  let w : Nat → Fe := upd (upd (FS s.mem b) SX (FS s.mem b NRX)) SY (FS s.mem b NRY)
  have C2w : R64.Cur b sL t2v c AQ w s2 := by
    refine C2.congr (by decide) fun q hq => ?_
    simp only [AQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (disch := decide) only [w, upd_self, upd_of_ne, ky]
  have hwd : w DK = Spec.Ed448.d := by simp (disch := decide) only [w, upd_of_ne]; exact hd
  rw [opsProg_eq]
  refine WP.seq (R64.ops_ok _ AQ w s2 add_ok C2w fun s3 C3 => WP.block_nil ?_)
  have C3' := cur_fs C3 add_sub
  have d3 : FS s3.mem b DK = Spec.Ed448.d := by rw [C3.slots DK (add_sub DK (by decide)), (add_vals w hwd).2, hwd]
  have p3 : ptOf (FS s3.mem b) = Spec.Ed448.pointAdd (ptOf (FS s.mem b)) ⟨FS s.mem b NRX, FS s.mem b NRY, 1⟩ := by
    have e : ptOf (FS s3.mem b) = ptOf (runOps (Impl.Ed448.RISCV64.addOps.map toF) w) := by
      simp only [ptOf]
      rw [C3.slots RX (add_sub RX (by decide)), C3.slots RY (add_sub RY (by decide)),
        C3.slots RZ (add_sub RZ (by decide))]
    have pw : ptOf w = ptOf (FS s.mem b) := by simp (disch := decide) only [ptOf, w, upd_of_ne]
    rw [e, (add_vals w hwd).1, pw, addAffine_eq]
    simp (disch := decide) only [w, upd_self, upd_of_ne]
  refine WP.seq (R64.ops_ok _ DQ _ s3 dbl_ok C3' fun s4 C4 => WP.block_nil ?_)
  have C4' := cur_fs C4 dbl_sub
  have d4 : FS s4.mem b DK = Spec.Ed448.d := by rw [C4.slots DK (dbl_sub DK (by decide)), (dbl_vals _).2, d3]
  have p4 : ptOf (FS s4.mem b) = Proof.Ed448.double (ptOf (FS s3.mem b)) := by
    have e : ptOf (FS s4.mem b) = ptOf (runOps (dblOps.map toF) (FS s3.mem b)) := by
      simp only [ptOf]
      rw [C4.slots RX (dbl_sub RX (by decide)), C4.slots RY (dbl_sub RY (by decide)),
        C4.slots RZ (dbl_sub RZ (by decide))]
    rw [e, (dbl_vals _).1]
  refine R64.ops_ok _ DQ _ s4 dbl_ok C4' fun s5 C5 => WP.block_nil ⟨vctx_cur hvL C5, C5.stp, fun q hq => ?_⟩
  have p5 : ptOf (FS s5.mem b) = Proof.Ed448.double (ptOf (FS s4.mem b)) := by
    have e : ptOf (FS s5.mem b) = ptOf (runOps (dblOps.map toF) (FS s4.mem b)) := by
      simp only [ptOf]
      rw [C5.slots RX (dbl_sub RX (by decide)), C5.slots RY (dbl_sub RY (by decide)),
        C5.slots RZ (dbl_sub RZ (by decide))]
    rw [e, (dbl_vals _).1]
  have d5 : FS s5.mem b DK = Spec.Ed448.d := by rw [C5.slots DK (dbl_sub DK (by decide)), (dbl_vals _).2, d4]
  rw [← p3, ← p4, ← p5]
  simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [ptV, ptOf, RX, RY, RZ, PX, PY, Impl.Ed448.RISCV64.PZ, DK, Impl.X448.RISCV64.X2, Impl.X448.RISCV64.Z2,
      Nat.reduceEqDiff, ↓reduceIte]
  exact d5

end

end VG.Proof.Ed448.RISCV64
