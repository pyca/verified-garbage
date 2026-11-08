module
-- separate module: its proofs take about 10 s, which `VMain.lean`'s edits need not re-check

public import VerifiedGarbage.Proof.Ed448.PPC64LE.VDigits
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Comb
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseStep
public import VerifiedGarbage.Proof.Ed448.WnafWide.Group
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseInit
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseSel
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
import Mathlib.Tactic.Abel

/-!
# Ed448's verification on PPC64LE: the joint loop

RISC-V's proof (`Proof/Ed448/RISCV64/VJoint.lean`), with the point
operations called (`Comb.call_ops`). At position `n`, from the top, `R`
becomes `[2]R + [S_n]B + [k_n]a` (`jointStep_ok`), for `S_n` and `k_n` the
width-5 digits of `S` and `k` (`digV`) and `a` what the key table's entries
are odd multiples of (`KeyOk`): `R` represents
`[residual S n]B + [residual k n]a` (`WInv`), so from the neutral point at
464 it represents `[S]B + [k]a` at 0 (`joint_ok`). A digit `d ≠ 0` selects
entry `|d| / 2` of its table (`digit_dec`), negated if `d < 0`: `baseEntry d`
for `B`'s, and `±[|d|]a` for `a`'s. Between operations the loop has written
only the registers of `work`, the position in `r14`, and the field area
(`JS`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Proof.Ed448 (Rep baseAff pointAdd_rep double_rep dZ)
open VG.Proof.Ed448.PPC64LE.Comb (toF opsProg_eq ptOf DQ AQ dbl_ok add_ok dbl_sub add_sub dbl_vals add_vals
  addAffine_eq call_ops dbl_lr add_lr)
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.PPC64LE (ACC)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point)

/-! ## Digits -/

/-- The byte of a digit, as `lbz` reads it. -/
abbrev dByte (d : Int) : BitVec 64 := BitVec.ofNat 64 (BitVec.ofInt 8 d).toNat

/-- Its sign's mask, as `digitIndex` computes it. -/
abbrev dMask (x : BitVec 64) : BitVec 64 := 0 - (x >>> 7)

/-- Its entry's index. -/
abbrev dIdx (x : BitVec 64) : BitVec 64 := (((x ^^^ dMask x) - dMask x) &&& BitVec.ofNat 64 255) >>> 1

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

/-! ## The loop's state -/

/-- `s` is `sL` but for the registers of `work`, the position `n` in `r14` and
the field area. -/
structure JS (b : Addr) (sL : State) (n : Nat) (s : State) : Prop where
  ctx : VCtx b s
  rest : Rest (.r14 :: work) sL s
  frame : Frame [FA b] sL.mem s.mem
  r14 : s.gpr .r14 = BitVec.ofNat 64 n

theorem JS.next {sL s s' : State} {n : Nat} (h : JS b sL n s) {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ work) (hf : Frame [FA b] s.mem s'.mem) : JS b sL n s' :=
  ⟨h.ctx.of_rest hr (fun e => absurd (hws _ e) (by decide)) (fun e => absurd (hws _ e) (by decide)),
    h.rest.trans (hr.mono fun r hr' => List.mem_cons_of_mem _ (hws r hr')), h.frame.trans hf,
    by rw [hr.gpr _ (fun e => absurd (hws _ e) (by decide)), h.r14]⟩

theorem JS.stp {sL s s' : State} {n : Nat} (h : JS b sL n s) (hs : Stp b s s') : JS b sL n s' :=
  h.next hs.rest (fun _ h => h) hs.frame

/-! ## The digit's entry -/

/-- `loadDigit e` reads the byte of lane `e` at `n = r14`. -/
theorem loadDigit_ok {s : State} (hv : VCtx b s) {n e : Nat} (hn : n < 468) (he : e < 4)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 n) :
    WP isa (.block (loadDigit e)) s fun t => Rest [.r9, .r10] s t ∧ t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 64 (s.mem (b + BitVec.ofNat 64 (TB + (4 * n + e)))).toNat := by
  have hT : TB = 1064 := rfl
  simp only [loadDigit]
  refine wp_lsl (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e2 : s2.gpr .r9 + BitVec.ofNat 64 (TB + e) = b + BitVec.ofNat 64 (TB + (4 * n + e)) := by
    rw [u2.gpr, u1.other _ (by decide), u1.gpr, hv.ctx.r6, h14, shl_ofNat (by omega), Offset.add_add]
    congr 2; omega
  refine wp_lbz (by decide) (by omega) e2 (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hv.inR (by omega))
    fun s3 u3 => WP.block_nil ⟨(u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, u1.mem], by rw [u3.gpr, u2.mem, u1.mem]⟩

/-- `digitIndex`: the sign's mask into `r12` and the index into `r10`. -/
theorem digitIndex_ok {s : State} {d : Int} (h1 : -15 ≤ d) (h2 : d ≤ 15)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (BitVec.ofInt 8 d).toNat) :
    WP isa (.block digitIndex) s fun t => Rest [.r8, .r10, .r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 64 (d.natAbs / 2) ∧ t.gpr .r12 = (if d < 0 then BitVec.allOnes 64 else 0) := by
  obtain ⟨i1, i2, -⟩ := digit_dec h1 h2
  rw [← dByte] at h10
  simp only [digitIndex]
  refine wp_lsr (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_sub fun s3 u3 =>
    wp_xor fun s4 u4 => wp_sub fun s5 u5 => wp_li (by decide) fun s6 u6 => wp_and fun s7 u7 =>
    wp_lsr (by decide) fun s8 u8 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide))))))))
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [← i1]
    simp only [reduceCtorEq, u8.at, u7.at, u6.at, u5.at, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h10]
    rfl
  · rw [← i2]
    simp only [reduceCtorEq, u8.at, u7.at, u6.at, u5.at, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h10]
    rfl

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

/-- What the joint loop reads: the digits of `S` and `K` and the base table. -/
def JFix (b : Addr) (S K : Nat) (m : Mem) : Prop :=
  TbIs b m (digV S K) ∧ BaseOk b m

theorem kpt_hi {m m' : Mem} (hf : Frame [FA b] m m') {i : Nat} (hi : i < 8) : kpt m' b i = kpt m b i := by
  have hA : ACC = 952 := rfl
  have hK : KT = 4160 := rfl
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

theorem ptrBase_ok {s : State} (hv : VCtx b s) {i : Nat} (hi : i < 8) (h10 : s.gpr .r10 = BitVec.ofNat 64 i) :
    WP isa (.block [.lsl .r9 .r10 7, .lsl .r8 .r10 4, .sub .r9 .r9 .r8, .add .r9 .r9 .r6]) s fun t =>
      Rest [.r8, .r9] s t ∧ t.mem = s.mem ∧ t.gpr .r9 = b + BitVec.ofNat 64 (112 * i) := by
  refine wp_lsl (by decide) fun s1 u1 => wp_lsl (by decide) fun s2 u2 => wp_sub fun s3 u3 => wp_add fun s4 u4 =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide))))
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · simp only [reduceCtorEq, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h10, hv.ctx.r6]
    rw [shl_ofNat (by omega), shl_ofNat (by omega)]
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

theorem ptrKey_ok {s : State} (hv : VCtx b s) {i : Nat} (hi : i < 8) (h10 : s.gpr .r10 = BitVec.ofNat 64 i) :
    WP isa (.block [.lsl .r9 .r10 7, .lsl .r8 .r10 5, .add .r9 .r9 .r8, .lsl .r8 .r10 3,
        .add .r9 .r9 .r8, .add .r9 .r9 .r6]) s fun t =>
      Rest [.r8, .r9] s t ∧ t.mem = s.mem ∧ t.gpr .r9 = b + BitVec.ofNat 64 (168 * i) := by
  refine wp_lsl (by decide) fun s1 u1 => wp_lsl (by decide) fun s2 u2 => wp_add fun s3 u3 =>
    wp_lsl (by decide) fun s4 u4 => wp_add fun s5 u5 => wp_add fun s6 u6 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · simp only [reduceCtorEq, u6.at, u5.at, u4.at, u3.at, u2.at, u1.at, ↓reduceIte, h10, hv.ctx.r6]
    rw [shl_ofNat (by omega), shl_ofNat (by omega), shl_ofNat (by omega)]
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

end

/-! ## RFC 8032's addition, a function -/

theorem runOps_append : ∀ (l₁ l₂ : List FOp) (v : Nat → Fe), runOps (l₁ ++ l₂) v = runOps l₂ (runOps l₁ v)
  | [], _, _ => rfl
  | _ :: l₁, l₂, _ => runOps_append l₁ l₂ _

theorem projOps_eq : projOps.map toF = addOps ++ ([.mul TZ TF TG] : List FOp) := rfl

theorem proj_ok : opsOk (projOps.map toF) SQ = true := by decide

theorem proj_sub : ∀ q ∈ [TX, TY, TZ, RX, RY, RZ, DK], q ∈ outsQ (projOps.map toF) SQ := by decide

theorem proj_sub' : ∀ q ∈ [PX, PY, Impl.Ed448.PPC64LE.PZ], q ∈ outsQ (projOps.map toF) SQ := by decide

theorem addV_P (r p : Point) : addV r p PX = p.X ∧ addV r p PY = p.Y ∧ addV r p Impl.Ed448.PPC64LE.PZ = p.Z := by
  simp only [addV, addOps, runOps, FOp.out, upd, ptV, RX, RY, RZ, PX, PY,
    Impl.Ed448.PPC64LE.PZ, DK, TX, TY, TZ, TA, TC, TD, TF, TG, TH, Impl.X448.PPC64LE.X2, Impl.X448.PPC64LE.Z2,
    Impl.X448.PPC64LE.R, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem proj_lr : (instrs (opsCode (projOps.map toF) (.block []) : Prog isa)).all
    (fun i => !i.writesLr) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem proj_run (r p : Point) : runOps (projOps.map toF) (ptV r p) = addV r p := by
  rw [projOps_eq, runOps_append]; rfl

section
variable {b : Addr}

/-! ## Operations on the loop's state -/

/-- An element apart from a frame's regions stays. -/
theorem fsD {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {q : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 q, 56⟩ r) : FS m' b q = FS m b q := by
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => (hd r hr).sub_left (Offset.sub b (d := q + 4 * k) (n := 4) (e := q) (k := 56)
      (by omega) (by omega))
  rw [FS, V, val32_congr e]; rfl

/-- The element at `b + ps` copied into the slot `o`. -/
theorem opCp {sL s : State} {n : Nat} (h : JS b sL n s) {rs : Reg} {so o ps : Nat} (hrs : rs ≠ .r7)
    (hrs0 : rs ≠ .r0) (hso : so + 48 < 2 ^ 15) (hso4 : so % 4 = 0)
    (hs : s.gpr rs + BitVec.ofNat 64 so = b + BitVec.ofNat 64 ps) (hps' : ps + 56 ≤ 8192)
    (ho : o + 56 ≤ ACC) (ho4 : o % 4 = 0) (hsep : ps + 56 ≤ o ∨ o + 56 ≤ ps) :
    WP isa (.block (cp7 rs so .r6 o)) s fun t => JS b sL n t ∧ Rest [.r7] s t ∧
      FS t.mem b o = FS s.mem b ps ∧
      ∀ q, (q + 56 ≤ o ∨ o + 56 ≤ q) → q + 56 ≤ 8192 → FS t.mem b q = FS s.mem b q := by
  have hA : ACC = 952 := rfl
  refine WP.mono (cp7_ok h.ctx hrs (by decide) hrs0 (by decide) hso hso4 (by omega) ho4 hs
    (by rw [h.ctx.ctx.r6]) hps' (by omega) hsep) fun t ⟨_, hr, hf, hd⟩ =>
    ⟨h.next hr (by decide) (hf.sub fun r hr' => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr']; exact Offset.sub_base _ (by omega)⟩), hr,
      by rw [FS, FS, cp7_V hd], fun q hq hq' => fsD hf fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ hq (by omega) (by omega)⟩

/-- The slot `x` negated, as `(x - x) - x` through `tmp`, if the mask in `r12` is all ones. -/
theorem negSlot_ok {sL s : State} {n : Nat} (h : JS b sL n s) {tmp x : Nat} {qs : List Nat}
    (hq1 : Sep1 tmp (x :: qs) = true) (hq2 : Sep1 x (tmp :: x :: qs) = true) (ht : tmp + 56 ≤ ACC)
    (hx : x + 56 ≤ ACC) (hqs : ∀ q ∈ qs, q ≠ tmp ∧ q ≠ x) (htx : tmp ≠ x) (neg : Bool)
    (h12 : s.gpr .r12 = if neg then BitVec.allOnes 64 else 0) :
    WP isa (.ite (.nonzero .d .r12) (.block (Impl.X448.PPC64LE.sub tmp x x ++ Impl.X448.PPC64LE.sub x tmp x))
      (.block [])) s fun t => JS b sL n t ∧
      FS t.mem b x = (if neg then FS s.mem b x - FS s.mem b x - FS s.mem b x else FS s.mem b x) ∧
      ∀ q ∈ qs, FS t.mem b q = FS s.mem b q := by
  cases neg
  · refine WP.ite false (by rw [eval_nonzero, h12]; rfl) (fun h => absurd h (by decide))
      (fun _ => WP.block_nil ⟨h, by simp, fun _ _ => rfl⟩)
  · refine WP.ite true (by rw [eval_nonzero, h12]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.append (subS (o := tmp) (x := x) (y := x) hq1 ht (List.mem_cons_self ..) (List.mem_cons_self ..)
      h.ctx.ctx (v := FS s.mem b) fun _ _ => rfl) fun s6 ⟨r6, f6, S6⟩ => ?_
    have h6 : JS b sL n s6 := h.next r6 (by decide) f6
    refine WP.mono (subS (o := x) (x := tmp) (y := x) hq2 hx (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) h6.ctx.ctx S6) fun s7 ⟨r7, f7, S7⟩ =>
      ⟨h6.next r7 (by decide) f7, ?_, fun q hq => ?_⟩
    · rw [S7 x (List.mem_cons_self ..), upd_self, upd_self, upd_of_ne _ _ (Ne.symm htx)]
      simp only [ite_true]
    · obtain ⟨n1, n2⟩ := hqs q hq
      rw [S7 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))),
        upd_of_ne _ _ n2, upd_of_ne _ _ n1]

/-- The doubling, called. -/
theorem callDbl_ok {sL s : State} {n : Nat} (h : JS b sL n s) :
    WP isa callDbl s fun t => JS b sL n t ∧ ptOf (FS t.mem b) = Proof.Ed448.double (ptOf (FS s.mem b)) ∧
      FS t.mem b DK = FS s.mem b DK := by
  unfold callDbl
  rw [opsProg_eq]
  refine call_ops (v := FS s.mem b) dbl_ok dbl_lr h.ctx.ctx (fun _ _ => rfl) fun t st S =>
    ⟨h.stp st, ?_, ?_⟩
  · simp only [ptOf]
    rw [S RX (dbl_sub RX (by decide)), S RY (dbl_sub RY (by decide)), S RZ (dbl_sub RZ (by decide))]
    exact (dbl_vals _).1
  · rw [S DK (dbl_sub DK (by decide)), (dbl_vals _).2]

/-- The affine addition, called. -/
theorem callAdd_ok {sL s : State} {n : Nat} (h : JS b sL n s) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa callAdd s fun t => JS b sL n t ∧
      ptOf (FS t.mem b) = Spec.Ed448.pointAdd (ptOf (FS s.mem b)) ⟨FS s.mem b SX, FS s.mem b SY, 1⟩ ∧
      FS t.mem b DK = FS s.mem b DK := by
  unfold callAdd
  rw [opsProg_eq]
  refine call_ops (v := FS s.mem b) add_ok add_lr h.ctx.ctx (fun _ _ => rfl) fun t st S =>
    ⟨h.stp st, ?_, ?_⟩
  · simp only [ptOf]
    rw [S RX (add_sub RX (by decide)), S RY (add_sub RY (by decide)), S RZ (add_sub RZ (by decide)),
      ← addAffine_eq]
    exact (add_vals _ hd).1
  · rw [S DK (add_sub DK (by decide)), (add_vals _ hd).2]

/-- RFC 8032's addition `T = R + P`, called. -/
theorem callProj_ok {sL s : State} {n : Nat} (h : JS b sL n s) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa callProj s fun t => JS b sL n t ∧
      FS t.mem b TX = (Spec.Ed448.pointAdd (ptOf (FS s.mem b)) ⟨FS s.mem b PX, FS s.mem b PY, FS s.mem b Impl.Ed448.PPC64LE.PZ⟩).X ∧
      FS t.mem b TY = (Spec.Ed448.pointAdd (ptOf (FS s.mem b)) ⟨FS s.mem b PX, FS s.mem b PY, FS s.mem b Impl.Ed448.PPC64LE.PZ⟩).Y ∧
      FS t.mem b TZ = (Spec.Ed448.pointAdd (ptOf (FS s.mem b)) ⟨FS s.mem b PX, FS s.mem b PY, FS s.mem b Impl.Ed448.PPC64LE.PZ⟩).Z ∧
      FS t.mem b DK = Spec.Ed448.d ∧ FS t.mem b PX = FS s.mem b PX ∧ FS t.mem b PY = FS s.mem b PY ∧
      FS t.mem b Impl.Ed448.PPC64LE.PZ = FS s.mem b Impl.Ed448.PPC64LE.PZ := by
  unfold callProj
  rw [opsProg_eq]
  have hS : SlotsOk s.mem b SQ (ptV (ptOf (FS s.mem b)) ⟨FS s.mem b PX, FS s.mem b PY, FS s.mem b Impl.Ed448.PPC64LE.PZ⟩) := by
    intro q hq
    simp only [SQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    iterate 6 (· simp only [ptV, ptOf, RX, RY, RZ, PX, PY, Impl.Ed448.PPC64LE.PZ, Impl.X448.PPC64LE.X2, Impl.X448.PPC64LE.Z2,
      Nat.reduceEqDiff, ↓reduceIte])
    · simp only [ptV, RX, RY, RZ, PX, PY, Impl.Ed448.PPC64LE.PZ, DK, Impl.X448.PPC64LE.X2, Impl.X448.PPC64LE.Z2, Nat.reduceEqDiff,
        ↓reduceIte]
      exact hd
  refine call_ops proj_ok proj_lr h.ctx.ctx hS fun t st S => ⟨h.stp st, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [proj_run] at S
  · rw [S TX (proj_sub TX (by decide))]; exact (addV_vals _ _).2.2.2.2.1
  · rw [S TY (proj_sub TY (by decide))]; exact (addV_vals _ _).2.2.2.2.2.1
  · rw [S TZ (proj_sub TZ (by decide))]; exact (addV_vals _ _).2.2.2.2.2.2
  · rw [S DK (proj_sub DK (by decide))]; exact (addV_vals _ _).2.2.2.1
  · rw [S PX (proj_sub' PX (by decide))]; exact (addV_P _ _).1
  · rw [S PY (proj_sub' PY (by decide))]; exact (addV_P _ _).2.1
  · rw [S Impl.Ed448.PPC64LE.PZ (proj_sub' Impl.Ed448.PPC64LE.PZ (by decide))]; exact (addV_P _ _).2.2

end

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

/-- The selected key entry, negated as the code does. -/
theorem keyEntry_eq {d : Int} (p : Point) :
    Proof.Ed448.WnafWide.signedPoint (decide (d < 0)) p = ⟨if d < 0 then p.X - p.X - p.X else p.X, p.Y, p.Z⟩ := by
  unfold Proof.Ed448.WnafWide.signedPoint
  by_cases hn : d < 0
  · rw [decide_eq_true hn, ite_eq_left rfl, ite_eq_left hn]
    simp only [Proof.Ed448.negPoint]
    rw [sub_self]
  · rw [decide_eq_false hn, ite_eq_right Bool.false_ne_true, ite_eq_right hn]

section
variable {b : Addr}

theorem key_rep {a : VG.Proof.EdwardsLaw.EPoint dZ} {m : Mem} (hk : KeyOk b a m) {d : Int} (hd : d ≠ 0)
    (h1 : -15 ≤ d) (h2 : d ≤ 15) (ho : d = 0 ∨ d.natAbs % 2 = 1) :
    Rep (Proof.Ed448.WnafWide.signedPoint (decide (d < 0)) (kpt m b (d.natAbs / 2))) (d • a) := by
  have he : 2 * (d.natAbs / 2) + 1 = d.natAbs := by omega
  have h := hk (d.natAbs / 2) (by omega)
  rw [he] at h
  have hs := Proof.Ed448.WnafWide.signedPoint_rep h (decide (d < 0))
  rwa [Proof.Ed448.WnafWide.signed_abs] at hs

/-- After an addition: `R` and `d` in their slots, `R` representing `X a` whenever the key table holds
the odd multiples of `a`. -/
def APost (b : Addr) (sL : State) (n : Nat) (X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ)
    (t : State) : Prop :=
  JS b sL n t ∧ FS t.mem b DK = Spec.Ed448.d ∧ ∀ a, KeyOk b a sL.mem → Rep (ptOf (FS t.mem b)) (X a)

theorem pt_keep {m m' : Mem} (h : ∀ q ∈ [RX, RY, RZ], FS m' b q = FS m b q) : ptOf (FS m' b) = ptOf (FS m b) := by
  simp only [ptOf]
  rw [h RX (by simp), h RY (by simp), h RZ (by simp)]

theorem addBase_ok {S K : Nat} {sL s : State} (hfx : JFix b S K sL.mem) {n : Nat} (hn : n < 464)
    (hc : JS b sL n s) {X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ}
    (hd : FS s.mem b DK = Spec.Ed448.d) (hrep : ∀ a, KeyOk b a sL.mem → Rep (ptOf (FS s.mem b)) (X a)) :
    WP isa addBase s (APost b sL n fun a => X a + digitAt false S n • baseAff) := by
  have hA : ACC = 952 := rfl
  have hT : TB = 1064 := rfl
  have hB : BT = 5504 := rfl
  have hX : RX = 56 := rfl
  have hY : RY = 0 := rfl
  have hZ : RZ = 112 := rfl
  have hD : DK = 336 := rfl
  have hSX : SX = 168 := rfl
  have hSY : SY = 224 := rfl
  obtain ⟨hdig, hbase⟩ := hfx
  obtain ⟨g1, g2⟩ := digit_range S n
  obtain ⟨i1, i2, i3⟩ := digit_dec g1 g2
  unfold addBase baseBody
  refine WP.seq (WP.mono (loadDigit_ok hc.ctx (n := n) (e := 2) (by omega) (by decide) hc.r14)
    fun s1 ⟨r1, m1, e10⟩ => ?_)
  have hb10 : s1.gpr .r10 = dByte (digitAt false S n) := by
    rw [e10, byte_hi hc.frame (by omega) (by omega), dig_byte hdig (by omega) (.inl rfl), ite_eq_left rfl]
  have C1 : JS b sL n s1 := hc.next r1 (by decide) (by rw [m1]; exact Frame.refl _ _)
  refine WP.ite _ (by rw [eval_nonzero, hb10]) (fun hnz => ?_) (fun hz => ?_)
  · have hne : digitAt false S n ≠ 0 := by rw [i3] at hnz; simpa using hnz
    have hi : (digitAt false S n).natAbs / 2 < 8 := by omega
    rw [show digitIndex ++ [.lsl .r9 .r10 7, .lsl .r8 .r10 4, .sub .r9 .r9 .r8, .add .r9 .r9 .r6] ++
        ldSlots .r9 BT [SX, SY] =
      digitIndex ++ ([.lsl .r9 .r10 7, .lsl .r8 .r10 4, .sub .r9 .r9 .r8, .add .r9 .r9 .r6] ++
        (cp7 .r9 BT .r6 SX ++ cp7 .r9 (BT + 56) .r6 SY)) from rfl]
    refine WP.seq (WP.append (digitIndex_ok g1 g2 hb10) fun s2 ⟨r2, m2, a2, m12⟩ => ?_)
    have C2 : JS b sL n s2 := C1.next r2 (by decide) (by rw [m2]; exact Frame.refl _ _)
    refine WP.append (ptrBase_ok C2.ctx hi a2) fun s3 ⟨r3, m3, t3⟩ => ?_
    have C3 : JS b sL n s3 := C2.next r3 (by decide) (by rw [m3]; exact Frame.refl _ _)
    generalize hi' : (digitAt false S n).natAbs / 2 = i at t3 hi
    have bx := base_fs hbase hi
    refine WP.append (opCp C3 (rs := .r9) (so := BT) (o := SX) (ps := BT + 112 * i) (by decide) (by decide)
      (by omega) (by omega) (by rw [t3, Offset.add_add, Nat.add_comm]) (by omega) (by decide) (by decide)
      (by omega)) fun s4 ⟨C4, q4, x4, k4⟩ => ?_
    refine WP.mono (opCp C4 (rs := .r9) (so := BT + 56) (o := SY) (ps := BT + 112 * i + 56) (by decide) (by decide)
      (by omega) (by omega) (by rw [q4.gpr _ (by decide), t3, Offset.add_add]; congr 2; omega) (by omega)
      (by decide) (by decide) (by omega)) fun s5 ⟨C5, q5, y5, k5⟩ => ?_
    have m12' : s5.gpr .r12 = if digitAt false S n < 0 then BitVec.allOnes 64 else 0 := by
      rw [q5.gpr _ (by decide), q4.gpr _ (by decide), r3.gpr _ (by decide), m12]
    have hx5 : FS s5.mem b SX = (Impl.Ed448.PublicTable.entry i).1 := by
      rw [k5 SX (by omega) (by omega), x4, fs_hi C3.frame (by omega) (by omega)]; exact bx.1
    have hy5 : FS s5.mem b SY = (Impl.Ed448.PublicTable.entry i).2 := by
      rw [y5, k4 _ (by omega) (by omega), fs_hi C3.frame (by omega) (by omega)]; exact bx.2
    have kR5 : ∀ q ∈ [RX, RY, RZ, DK], FS s5.mem b q = FS s.mem b q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), m3, m2, m1]
    -- The negation.
    refine WP.seq (WP.mono (negSlot_ok C5 (tmp := U0) (x := SX) (qs := [RX, RY, RZ, DK, SY]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (decide (digitAt false S n < 0))
      (by rw [m12']; by_cases h : digitAt false S n < 0 <;> simp [h])) fun s6 ⟨C6, x6, k6⟩ => ?_)
    have d6 : FS s6.mem b DK = Spec.Ed448.d := by rw [k6 DK (by simp), kR5 DK (by simp), hd]
    refine WP.mono (callAdd_ok C6 d6) fun s7 ⟨C7, p7, d7⟩ => ⟨C7, by rw [d7, d6], fun a hk => ?_⟩
    have p6 : ptOf (FS s6.mem b) = ptOf (FS s.mem b) :=
      pt_keep fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> rw [k6 _ (by simp), kR5 _ (by simp)]
    rw [p7, p6, x6, k6 SY (by simp), hy5, hx5]
    have e := baseEntry_eq hne (Impl.Ed448.PublicTable.entry i).1 (Impl.Ed448.PublicTable.entry i).2
      (by rw [hi']) (by rw [hi'])
    rw [show (if decide (digitAt false S n < 0) = true then (Impl.Ed448.PublicTable.entry i).1 -
        (Impl.Ed448.PublicTable.entry i).1 - (Impl.Ed448.PublicTable.entry i).1
        else (Impl.Ed448.PublicTable.entry i).1) =
        (if digitAt false S n < 0 then (Impl.Ed448.PublicTable.entry i).1 -
          (Impl.Ed448.PublicTable.entry i).1 - (Impl.Ed448.PublicTable.entry i).1
        else (Impl.Ed448.PublicTable.entry i).1) by simp only [decide_eq_true_eq], ← e]
    exact pointAdd_rep (hrep a hk) (Proof.Ed448.WnafWide.baseEntry_rep (by omega)
      (Proof.Ed448.WnafWide.digit_zero_or_odd false _))
  · have hz' : digitAt false S n = 0 := by rw [i3] at hz; simpa using hz
    refine WP.block_nil ⟨C1, by rw [m1]; exact hd, fun a hk => ?_⟩
    beta_reduce
    rw [m1, hz', zero_smul, add_zero]
    exact hrep a hk

end

section
variable {b : Addr}

theorem addKey_ok {S K : Nat} {sL s : State} (hfx : JFix b S K sL.mem) {n : Nat} (hn : n < 464)
    (hc : JS b sL n s) {X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ}
    (hd : FS s.mem b DK = Spec.Ed448.d) (hrep : ∀ a, KeyOk b a sL.mem → Rep (ptOf (FS s.mem b)) (X a)) :
    WP isa addKey s (APost b sL n fun a => X a + digitAt false K n • a) := by
  have hA : ACC = 952 := rfl
  have hT : TB = 1064 := rfl
  have hK : KT = 4160 := rfl
  have hPX : PX = 168 := rfl
  have hPY : PY = 224 := rfl
  have hPZ : Impl.Ed448.PPC64LE.PZ = 280 := rfl
  obtain ⟨hdig, -⟩ := hfx
  obtain ⟨g1, g2⟩ := digit_range K n
  obtain ⟨i1, i2, i3⟩ := digit_dec g1 g2
  unfold addKey keyBody
  refine WP.seq (WP.mono (loadDigit_ok hc.ctx (n := n) (e := 3) (by omega) (by decide) hc.r14)
    fun s1 ⟨r1, m1, e10⟩ => ?_)
  have hb10 : s1.gpr .r10 = dByte (digitAt false K n) := by
    rw [e10, byte_hi hc.frame (by omega) (by omega), dig_byte hdig (by omega) (.inr rfl),
      ite_eq_right (by decide)]
  have C1 : JS b sL n s1 := hc.next r1 (by decide) (by rw [m1]; exact Frame.refl _ _)
  refine WP.ite _ (by rw [eval_nonzero, hb10]) (fun hnz => ?_) (fun hz => ?_)
  · have hne : digitAt false K n ≠ 0 := by rw [i3] at hnz; simpa using hnz
    have hi : (digitAt false K n).natAbs / 2 < 8 := by omega
    rw [show digitIndex ++ [.lsl .r9 .r10 7, .lsl .r8 .r10 5, .add .r9 .r9 .r8, .lsl .r8 .r10 3,
        .add .r9 .r9 .r8, .add .r9 .r9 .r6] ++ ldSlots .r9 KT [PX, PY, Impl.Ed448.PPC64LE.PZ] =
      digitIndex ++ ([.lsl .r9 .r10 7, .lsl .r8 .r10 5, .add .r9 .r9 .r8, .lsl .r8 .r10 3,
        .add .r9 .r9 .r8, .add .r9 .r9 .r6] ++
        (cp7 .r9 KT .r6 PX ++ (cp7 .r9 (KT + 56) .r6 PY ++ cp7 .r9 (KT + 112) .r6 Impl.Ed448.PPC64LE.PZ))) from rfl]
    refine WP.seq (WP.append (digitIndex_ok g1 g2 hb10) fun s2 ⟨r2, m2, a2, m12⟩ => ?_)
    have C2 : JS b sL n s2 := C1.next r2 (by decide) (by rw [m2]; exact Frame.refl _ _)
    refine WP.append (ptrKey_ok C2.ctx hi a2) fun s3 ⟨r3, m3, t3⟩ => ?_
    have C3 : JS b sL n s3 := C2.next r3 (by decide) (by rw [m3]; exact Frame.refl _ _)
    generalize hi' : (digitAt false K n).natAbs / 2 = i at t3 hi
    refine WP.append (opCp C3 (rs := .r9) (so := KT) (o := PX) (ps := KT + 168 * i) (by decide) (by decide)
      (by omega) (by omega) (by rw [t3, Offset.add_add, Nat.add_comm]) (by omega) (by decide) (by decide)
      (by simp only [PX]; omega)) fun s4 ⟨C4, q4, x4, k4⟩ => ?_
    refine WP.append (opCp C4 (rs := .r9) (so := KT + 56) (o := PY) (ps := KT + 168 * i + 56) (by decide)
      (by decide) (by omega) (by omega) (by rw [q4.gpr _ (by decide), t3, Offset.add_add]; congr 2; omega)
      (by omega) (by decide) (by decide) (by simp only [PY]; omega)) fun s5 ⟨C5, q5, y5, k5⟩ => ?_
    refine WP.mono (opCp C5 (rs := .r9) (so := KT + 112) (o := Impl.Ed448.PPC64LE.PZ) (ps := KT + 168 * i + 112)
      (by decide) (by decide) (by omega) (by omega)
      (by rw [q5.gpr _ (by decide), q4.gpr _ (by decide), t3, Offset.add_add]; congr 2; omega)
      (by omega) (by decide) (by decide) (by simp only [Impl.Ed448.PPC64LE.PZ]; omega))
      fun s6 ⟨C6, q6, z6, k6⟩ => ?_
    have m12' : s6.gpr .r12 = if digitAt false K n < 0 then BitVec.allOnes 64 else 0 := by
      rw [q6.gpr _ (by decide), q5.gpr _ (by decide), q4.gpr _ (by decide), r3.gpr _ (by decide), m12]
    have kp := kpt_hi C3.frame hi
    have hx6 : FS s6.mem b PX = (kpt sL.mem b i).X := by
      rw [k6 PX (by decide) (by decide), k5 PX (by decide) (by decide), x4, ← kp]; rfl
    have hy6 : FS s6.mem b PY = (kpt sL.mem b i).Y := by
      rw [k6 PY (by decide) (by decide), y5, k4 _ (by omega) (by omega), ← kp]; rfl
    have hz6 : FS s6.mem b Impl.Ed448.PPC64LE.PZ = (kpt sL.mem b i).Z := by
      rw [z6, k5 _ (by omega) (by omega), k4 _ (by omega) (by omega), ← kp]; rfl
    have kR6 : ∀ q ∈ [RX, RY, RZ, DK], FS s6.mem b q = FS s.mem b q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        rw [k6 _ (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), m3, m2, m1]
    -- The negation.
    refine WP.seq (WP.mono (negSlot_ok C6 (tmp := TA) (x := PX) (qs := [RX, RY, RZ, DK, PY, Impl.Ed448.PPC64LE.PZ])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (decide (digitAt false K n < 0))
      (by rw [m12']; by_cases h : digitAt false K n < 0 <;> simp [h])) fun s7 ⟨C7, x7, k7⟩ => ?_)
    have d7 : FS s7.mem b DK = Spec.Ed448.d := by rw [k7 DK (by simp), kR6 DK (by simp), hd]
    refine WP.seq (WP.mono (callProj_ok C7 d7) fun s8 ⟨C8, tx8, ty8, tz8, d8, _, _, _⟩ => ?_)
    -- `T` into `R`.
    rw [show copySlot RX TX ++ copySlot RY TY ++ copySlot RZ TZ =
      cp7 .r6 TX .r6 RX ++ (cp7 .r6 TY .r6 RY ++ cp7 .r6 TZ .r6 RZ) from rfl]
    refine WP.append (opCp C8 (rs := .r6) (so := TX) (o := RX) (ps := TX) (by decide) (by decide) (by decide)
      (by decide) (by rw [C8.ctx.ctx.r6]) (by decide) (by decide) (by decide) (by decide)) fun u1 ⟨D1, _, e1, f1⟩ => ?_
    refine WP.append (opCp D1 (rs := .r6) (so := TY) (o := RY) (ps := TY) (by decide) (by decide) (by decide)
      (by decide) (by rw [D1.ctx.ctx.r6]) (by decide) (by decide) (by decide) (by decide)) fun u2 ⟨D2, _, e2, f2⟩ => ?_
    refine WP.mono (opCp D2 (rs := .r6) (so := TZ) (o := RZ) (ps := TZ) (by decide) (by decide) (by decide)
      (by decide) (by rw [D2.ctx.ctx.r6]) (by decide) (by decide) (by decide) (by decide)) fun u3 ⟨D3, _, e3, f3⟩ =>
      ⟨D3, ?_, fun a hkey => ?_⟩
    · rw [f3 _ (by decide) (by decide), f2 _ (by decide) (by decide), f1 _ (by decide) (by decide), d8]
    · let r : Point := ptOf (FS s.mem b)
      let p : Point := Proof.Ed448.WnafWide.signedPoint (decide (digitAt false K n < 0)) (kpt sL.mem b i)
      have e : ptOf (FS u3.mem b) = Spec.Ed448.pointAdd r p := by
        have p7 : ptOf (FS s7.mem b) = r := pt_keep fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl <;> rw [k7 _ (by simp), kR6 _ (by simp)]
        have pp : (⟨FS s7.mem b PX, FS s7.mem b PY, FS s7.mem b Impl.Ed448.PPC64LE.PZ⟩ : Point) = p := by
          rw [x7, k7 PY (by simp), k7 Impl.Ed448.PPC64LE.PZ (by simp), hx6, hy6, hz6]
          simp only [p, keyEntry_eq, decide_eq_true_eq]
        simp only [ptOf]
        rw [f3 RX (by decide) (by decide), f2 RX (by decide) (by decide), e1, f3 RY (by decide) (by decide), e2, e3,
          f2 TZ (by decide) (by decide), f1 TZ (by decide) (by decide), f1 TY (by decide) (by decide), tx8, ty8, tz8,
          p7, pp]
      rw [e]
      have hk := key_rep hkey hne g1 g2 (Proof.Ed448.WnafWide.digit_zero_or_odd false _)
      rw [hi'] at hk
      exact pointAdd_rep (hrep a hkey) hk
  · have hz' : digitAt false K n = 0 := by rw [i3] at hz; simpa using hz
    refine WP.block_nil ⟨C1, by rw [m1]; exact hd, fun a hk => ?_⟩
    beta_reduce
    rw [m1, hz', zero_smul, add_zero]
    exact hrep a hk

end

/-! ## The loop -/

section
variable {b : Addr}

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

/-- The position decremented. -/
theorem decStep_ok {S K : Nat} {sL : State} {n : Nat} (hn : n < 464) {s : State} (h : WInv b S K sL (n + 1) s) :
    WP isa (.block [.subi .r14 .r14 1]) s (APost b sL n fun a =>
      (residual false S (n + 1) : Int) • baseAff + (residual false K (n + 1) : Int) • a) := by
  obtain ⟨hc, hd, hrep⟩ := h
  refine wp_subi (by decide) (by decide) fun s1 u1 => WP.block_nil ⟨⟨hc.ctx.of_rest (u1.rest (ws := [.r14])
    (by decide)) (by decide) (by decide), hc.rest.trans (u1.rest (by decide)), by rw [u1.mem]; exact hc.frame,
    by rw [u1.gpr, hc.r14, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]⟩,
    by rw [u1.mem]; exact hd, fun a hk => by rw [u1.mem]; exact hrep a hk⟩

/-- The doubling. -/
theorem dblStep_ok {sL : State} {n : Nat} {s : State}
    {X : VG.Proof.EdwardsLaw.EPoint dZ → VG.Proof.EdwardsLaw.EPoint dZ} (h : APost b sL n X s) :
    WP isa callDbl s (APost b sL n fun a => X a + X a) :=
  WP.mono (callDbl_ok h.1) fun t ⟨ht, pt, dt⟩ => ⟨ht, by rw [dt]; exact h.2.1, fun a hk => by
    rw [pt]; exact double_rep (h.2.2 a hk)⟩

theorem jointStep_ok {S K : Nat} {sL : State} (hfx : JFix b S K sL.mem) {n : Nat} (hn : n < 464) {s : State}
    (h : WInv b S K sL (n + 1) s) :
    WP isa jointStep s fun t => WInv b S K sL n t ∧ (t.gpr .r14 != 0) = decide (n ≠ 0) := by
  unfold jointStep
  refine WP.seq (WP.mono (decStep_ok hn h) fun s1 h1 =>
    WP.seq (WP.mono (dblStep_ok h1) fun s2 ⟨C2, d2, r2⟩ =>
      WP.seq (WP.mono (addBase_ok hfx hn C2 d2 r2) fun s3 ⟨C3, d3, r3⟩ =>
        WP.mono (addKey_ok hfx hn C3 d3 r3) fun s4 ⟨C4, d4, r4⟩ => ?_)))
  refine ⟨⟨C4, d4, fun a hk => ?_⟩, by rw [C4.r14, ofNat_ne_zero (by omega)]⟩
  beta_reduce
  rw [← round_eq S K n a]
  exact r4 a hk

theorem jointLoop_ok {S K : Nat} {sL : State} (hfx : JFix b S K sL.mem) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 464 → WInv b S K sL n s →
      WP isa (.loop jointStep (.nonzero .d .r14)) s (WInv b S K sL 0) := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := WInv b S K sL 0)
    (fun m s => 1 ≤ m ∧ m ≤ 464 ∧ WInv b S K sL m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hl⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (jointStep_ok hfx (by omega) hl) fun s' ⟨hl', hz⟩ => ?_
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    exact .inl ⟨by rw [eval_nonzero, hz]; simp, hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [show t ≠ 0 by omega], t, by omega, by omega, by omega, hl'⟩

end

/-! ## The key table -/

section
variable {b : Addr}

theorem JS.refl {s : State} (hv : VCtx b s) : JS b s (s.gpr .r14).toNat s :=
  ⟨hv, Rest.refl _ _, Frame.refl _ _, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

/-- The point at the offsets `ox`, `oy`, `oz`. -/
def Pt (m : Mem) (b : Addr) (ox oy oz : Nat) (p : Point) : Prop :=
  FS m b ox = p.X ∧ FS m b oy = p.Y ∧ FS m b oz = p.Z

/-- Three regions of 56 bytes. -/
abbrev R3 (b : Addr) (x y z : Nat) : List Region :=
  [⟨b + BitVec.ofNat 64 x, 56⟩, ⟨b + BitVec.ofNat 64 y, 56⟩, ⟨b + BitVec.ofNat 64 z, 56⟩]

theorem pt_keep3 {m m' : Mem} {x y z ox oy oz : Nat} (hf : Frame (R3 b x y z) m m') {p : Point}
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
theorem copy3_ok {s : State} (hv : VCtx b s) {rs rd : Reg} (hrs : rs ≠ .r7) (hrd : rd ≠ .r7)
    (hrs0 : rs ≠ .r0) (hrd0 : rd ≠ .r0)
    {sx sy sz dx dy dz x y z X Y Z : Nat}
    (hso : ∀ o ∈ [sx, sy, sz, dx, dy, dz], o + 48 < 2 ^ 15 ∧ o % 4 = 0)
    (hs : ∀ o p, (o, p) ∈ [(sx, x), (sy, y), (sz, z)] → s.gpr rs + BitVec.ofNat 64 o = b + BitVec.ofNat 64 p)
    (hd : ∀ o p, (o, p) ∈ [(dx, X), (dy, Y), (dz, Z)] → s.gpr rd + BitVec.ofNat 64 o = b + BitVec.ofNat 64 p)
    (h8 : ∀ o ∈ [x, y, z, X, Y, Z], o + 56 ≤ 8192)
    (hsep : ∀ o ∈ [x, y, z], ∀ w ∈ [X, Y, Z], o + 56 ≤ w ∨ w + 56 ≤ o)
    (hXY : X + 56 ≤ Y ∨ Y + 56 ≤ X) (hXZ : X + 56 ≤ Z ∨ Z + 56 ≤ X) (hYZ : Y + 56 ≤ Z ∨ Z + 56 ≤ Y)
    {p : Point} (hp : Pt s.mem b x y z p) :
    WP isa (.block (cp7 rs sx rd dx ++ (cp7 rs sy rd dy ++ cp7 rs sz rd dz))) s fun t =>
      VCtx b t ∧ Rest [.r7] s t ∧ Frame (R3 b X Y Z) s.mem t.mem ∧ Pt t.mem b X Y Z p := by
  have fx := h8 x (by simp); have fy := h8 y (by simp); have fz := h8 z (by simp)
  have fX := h8 X (by simp); have fY := h8 Y (by simp); have fZ := h8 Z (by simp)
  obtain ⟨o1, o1'⟩ := hso sx (by simp); obtain ⟨o2, o2'⟩ := hso sy (by simp)
  obtain ⟨o3, o3'⟩ := hso sz (by simp); obtain ⟨o4, o4'⟩ := hso dx (by simp)
  obtain ⟨o5, o5'⟩ := hso dy (by simp); obtain ⟨o6, o6'⟩ := hso dz (by simp)
  refine WP.append (cp7_ok hv hrs hrd hrs0 hrd0 o1 o1' o4 o4' (hs _ _ (by simp)) (hd _ _ (by simp))
    fx fX (hsep x (by simp) X (by simp))) fun s1 ⟨v1, r1, f1, d1⟩ => ?_
  have e1 : ∀ {r : Reg}, r ≠ .r7 → s1.gpr r = s.gpr r := fun h => r1.gpr _ (by simpa using h)
  refine WP.append (cp7_ok v1 hrs hrd hrs0 hrd0 o2 o2' o5 o5' (by rw [e1 hrs]; exact hs _ _ (by simp))
    (by rw [e1 hrd]; exact hd _ _ (by simp)) fy fY (hsep y (by simp) Y (by simp)))
    fun s2 ⟨v2, r2, f2, d2⟩ => ?_
  have e2 : ∀ {r : Reg}, r ≠ .r7 → s2.gpr r = s.gpr r := fun h => (r2.gpr _ (by simpa using h)).trans (e1 h)
  refine WP.mono (cp7_ok v2 hrs hrd hrs0 hrd0 o3 o3' o6 o6' (by rw [e2 hrs]; exact hs _ _ (by simp))
    (by rw [e2 hrd]; exact hd _ _ (by simp)) fz fZ (hsep z (by simp) Z (by simp)))
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

/-- The key table's region. -/
abbrev KR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 KT, 1344⟩

/-- After `j + 1` entries, from `sK`. -/
def KInv (b : Addr) (sK : State) (p d : Point) (j : Nat) (s : State) : Prop :=
  VCtx b s ∧ Rest (.r14 :: work) sK s ∧ Frame [FA b, KR b] sK.mem s.mem ∧
    s.gpr .r14 = BitVec.ofNat 64 (7 - j) ∧
    Pt s.mem b RX RY RZ (kE p d j) ∧ Pt s.mem b PX PY Impl.Ed448.PPC64LE.PZ d ∧ FS s.mem b DK = Spec.Ed448.d ∧
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
    have hK : KT = 4160 := rfl
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

theorem pt_ptOf {m : Mem} {p : Point} (h : Pt m b RX RY RZ p) : ptOf (FS m b) = p := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ptOf]; rw [h1, h2, h3]

theorem pt_of_ptOf {m : Mem} {p : Point} (h : ptOf (FS m b) = p) : Pt m b RX RY RZ p := by
  subst h; exact ⟨rfl, rfl, rfl⟩

end

section
variable {b : Addr}

theorem idp {s : State} (h6 : s.gpr .r6 = b) {x y z : Nat} :
    ∀ o p, (o, p) ∈ [(x, x), (y, y), (z, z)] → s.gpr .r6 + BitVec.ofNat 64 o = b + BitVec.ofNat 64 p := by
  intro o p h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [h6]

theorem offp {s : State} {r : Reg} {c : Nat} (hr : s.gpr r = b + BitVec.ofNat 64 c) {x y z : Nat} :
    ∀ o p, (o, p) ∈ [(x, x + c), (y, y + c), (z, z + c)] → s.gpr r + BitVec.ofNat 64 o = b + BitVec.ofNat 64 p := by
  intro o p h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hr, Offset.add_add, Nat.add_comm]

theorem kpt_pt {m : Mem} {e : Nat} {p : Point}
    (h : Pt m b (KT + 168 * e) (KT + 168 * e + 56) (KT + 168 * e + 112) p) : kpt m b e = p := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [kpt]; rw [h1, h2, h3]

theorem fs_R3 {m m' : Mem} {x y z : Nat} (hf : Frame (R3 b x y z) m m') {q : Nat}
    (hd : (q + 56 ≤ 8192 ∧ x + 56 ≤ 8192 ∧ y + 56 ≤ 8192 ∧ z + 56 ≤ 8192) ∧
      ∀ w ∈ [x, y, z], q + 56 ≤ w ∨ w + 56 ≤ q) : FS m' b q = FS m b q := by
  obtain ⟨⟨hq, hx, hy, hz⟩, hw⟩ := hd
  exact fsD hf fun r hr => by
    simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (hw x (by simp)) (by omega) (by omega)
    · exact Offset.disjoint _ (hw y (by simp)) (by omega) (by omega)
    · exact Offset.disjoint _ (hw z (by simp)) (by omega) (by omega)

theorem kpt_R3 {m m' : Mem} {x y z : Nat} (hf : Frame (R3 b x y z) m m') {e : Nat}
    (hd : ∀ q ∈ [KT + 168 * e, KT + 168 * e + 56, KT + 168 * e + 112],
      (q + 56 ≤ 8192 ∧ x + 56 ≤ 8192 ∧ y + 56 ≤ 8192 ∧ z + 56 ≤ 8192) ∧
      ∀ w ∈ [x, y, z], q + 56 ≤ w ∨ w + 56 ≤ q) : kpt m' b e = kpt m b e := by
  simp only [kpt]
  rw [fs_R3 hf (hd _ (by simp)), fs_R3 hf (hd _ (by simp)), fs_R3 hf (hd _ (by simp))]

theorem keyHead_ok {s : State} (hv : VCtx b s) {p : Point} (hp : Pt s.mem b NAX NAY ONE p)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa keyHead s (KInv b s p (Proof.Ed448.double p) 0) := by
  have hK : KT = 4160 := rfl
  have hA : ACC = 952 := rfl
  unfold keyHead
  rw [show copySlot RX NAX ++ copySlot RY NAY ++ copySlot RZ ONE ++ stSlots .r6 KT [RX, RY, RZ] =
      (cp7 .r6 NAX .r6 RX ++ (cp7 .r6 NAY .r6 RY ++ cp7 .r6 ONE .r6 RZ)) ++
        (cp7 .r6 RX .r6 KT ++ (cp7 .r6 RY .r6 (KT + 56) ++ cp7 .r6 RZ .r6 (KT + 112))) from rfl]
  refine WP.seq (WP.append (copy3_ok hv (rs := .r6) (rd := .r6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (idp hv.ctx.r6) (idp hv.ctx.r6) (by decide) (by decide) (by decide) (by decide) (by decide) hp)
    fun s1 ⟨v1, r1, f1, p1⟩ => ?_)
  refine WP.mono (copy3_ok v1 (rs := .r6) (rd := .r6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (idp v1.ctx.r6) (idp v1.ctx.r6) (by decide) (by decide) (by decide) (by decide) (by decide) p1)
    fun s2 ⟨v2, r2, f2, p2⟩ => ?_
  have pR2 : Pt s2.mem b RX RY RZ p := pt_keep3 f2 p1 (by decide) (by decide)
  have hk2 : kpt s2.mem b 0 = p := kpt_pt (by simpa only [Nat.mul_zero, Nat.add_zero] using p2)
  have k12 : ∀ q ∈ [DK], FS s2.mem b q = FS s.mem b q := fun q hq => by
    rw [List.mem_singleton.mp hq]
    rw [fs_R3 f2 (by decide),
      fs_R3 f1 (by decide)]
  -- The doubling.
  refine WP.seq (WP.mono (callDbl_ok (JS.refl v2)) fun s3 ⟨C3, p3, d3⟩ => ?_)
  rw [show copySlot PX RX ++ copySlot PY RY ++ copySlot Impl.Ed448.PPC64LE.PZ RZ ++ ldSlots .r6 KT [RX, RY, RZ] ++
      [.li .r14 7] =
      (cp7 .r6 RX .r6 PX ++ (cp7 .r6 RY .r6 PY ++ cp7 .r6 RZ .r6 Impl.Ed448.PPC64LE.PZ)) ++
        ((cp7 .r6 KT .r6 RX ++ (cp7 .r6 (KT + 56) .r6 RY ++ cp7 .r6 (KT + 112) .r6 RZ)) ++ [.li .r14 7]) from rfl]
  have pR3 : Pt s3.mem b RX RY RZ (Proof.Ed448.double p) := pt_of_ptOf (by rw [p3, pt_ptOf pR2])
  refine WP.append (copy3_ok C3.ctx (rs := .r6) (rd := .r6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (idp C3.ctx.ctx.r6) (idp C3.ctx.ctx.r6) (by decide) (by decide) (by decide) (by decide) (by decide) pR3)
    fun s4 ⟨v4, r4, f4, p4⟩ => ?_
  have pK3 : Pt s3.mem b KT (KT + 56) (KT + 112) p := by
    obtain ⟨e1, e2, e3⟩ := p2
    exact ⟨by rw [fs_hi C3.frame (by omega) (by omega)]; exact e1, by rw [fs_hi C3.frame (by omega) (by omega)]; exact e2,
      by rw [fs_hi C3.frame (by omega) (by omega)]; exact e3⟩
  have pK4 : Pt s4.mem b KT (KT + 56) (KT + 112) p := pt_keep3 f4 pK3 (by decide) (by decide)
  refine WP.append (copy3_ok v4 (rs := .r6) (rd := .r6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (idp v4.ctx.r6) (idp v4.ctx.r6) (by decide) (by decide) (by decide) (by decide) (by decide) pK4)
    fun s5 ⟨v5, r5, f5, p5⟩ => ?_
  refine wp_li (by decide) fun s6 u6 => WP.block_nil ?_
  have pP5 : Pt s5.mem b PX PY Impl.Ed448.PPC64LE.PZ (Proof.Ed448.double p) := pt_keep3 f5 p4 (by decide) (by decide)
  have d5 : FS s5.mem b DK = Spec.Ed448.d := by
    rw [fs_R3 f5 (by decide),
      fs_R3 f4 (by decide),
      d3, k12 DK (by simp), hd]
  have hk5 : kpt s5.mem b 0 = p := by
    rw [kpt_R3 f5 (by decide),
      kpt_R3 f4 (by decide),
      kpt_hi C3.frame (by decide), hk2]
  refine ⟨v5.of_rest (u6.rest (ws := [.r14]) (by decide)) (by decide) (by decide), ?_, ?_, by rw [u6.gpr], ?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans (C3.rest.trans ((r4.mono (by decide)).trans
      ((r5.mono (by decide)).trans (u6.rest (by decide))))))
  · rw [u6.mem]
    exact (frame_R3_FA f1 (by decide) (by decide) (by decide)).trans ((frame_R3_KR (e := 0) (by decide)
      (by simpa only [Nat.mul_zero, Nat.add_zero] using f2)).trans ((frame_FA_K C3.frame).trans
      ((frame_R3_FA f4 (by decide) (by decide) (by decide)).trans (frame_R3_FA f5 (by decide) (by decide) (by decide)))))
  · rw [u6.mem]; exact p5
  · rw [u6.mem]; exact pP5
  · rw [u6.mem]; exact d5
  · intro e he
    rw [Nat.le_zero.mp he, u6.mem, hk5]; rfl

end

section
variable {b : Addr}

theorem pt_mk {m : Mem} {x y z : Nat} {p : Point} (h : Pt m b x y z p) :
    (⟨FS m b x, FS m b y, FS m b z⟩ : Point) = p := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h2, h3]

/-- An entry of the key table written: what lies below it is kept. -/
theorem fs_KE {m m' : Mem} {i : Nat} (hi : i < 8)
    (hf : Frame (R3 b (KT + 168 * i) (KT + 168 * i + 56) (KT + 168 * i + 112)) m m') {q : Nat}
    (hq : q + 56 ≤ KT) : FS m' b q = FS m b q := by
  have hK : KT = 4160 := rfl
  exact fsD hf fun r hr => by
    simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem pt_KE {m m' : Mem} {i : Nat} (hi : i < 8)
    (hf : Frame (R3 b (KT + 168 * i) (KT + 168 * i + 56) (KT + 168 * i + 112)) m m') {x y z : Nat} {p : Point}
    (h : Pt m b x y z p) (hx : x + 56 ≤ KT ∧ y + 56 ≤ KT ∧ z + 56 ≤ KT) : Pt m' b x y z p := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [fs_KE hi hf hx.1]; exact h1, by rw [fs_KE hi hf hx.2.1]; exact h2, by rw [fs_KE hi hf hx.2.2]; exact h3⟩

theorem kpt_KE {m m' : Mem} {i : Nat} (hi : i < 8)
    (hf : Frame (R3 b (KT + 168 * i) (KT + 168 * i + 56) (KT + 168 * i + 112)) m m') {e : Nat} (he : e < i) :
    kpt m' b e = kpt m b e := by
  have hK : KT = 4160 := rfl
  simp only [kpt]
  have k : ∀ q, KT + 168 * e ≤ q → q ≤ KT + 168 * e + 112 → FS m' b q = FS m b q := fun q h1 h2 =>
    fsD hf fun r hr => by
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
  rw [k _ (by omega) (by omega), k _ (by omega) (by omega), k _ (by omega) (by omega)]

/-- A copy below the key table keeps its entries. -/
theorem kpt_lo {m m' : Mem} {x y z : Nat} (hf : Frame (R3 b x y z) m m') (hx : x + 56 ≤ KT ∧ y + 56 ≤ KT ∧ z + 56 ≤ KT)
    {e : Nat} (he : e < 8) : kpt m' b e = kpt m b e := by
  have hK : KT = 4160 := rfl
  obtain ⟨hx, hy, hz⟩ := hx
  simp only [kpt]
  have k : ∀ q, KT ≤ q → q ≤ KT + 168 * 7 + 112 → FS m' b q = FS m b q := fun q h1 h2 =>
    fsD hf fun r hr => by
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
  rw [k _ (by omega) (by omega), k _ (by omega) (by omega), k _ (by omega) (by omega)]

theorem keyPtr_ok {s : State} (hv : VCtx b s) {j : Nat} (hj : j < 7) (h14 : s.gpr .r14 = BitVec.ofNat 64 (7 - j)) :
    WP isa (.block keyPtr) s fun t =>
      Rest [.r4, .r5, .r12] s t ∧ t.mem = s.mem ∧ t.gpr .r12 = b + BitVec.ofNat 64 (168 * (j + 1)) := by
  simp only [keyPtr]
  refine wp_li (by decide) fun s0 u0 => wp_sub fun s1 u1 => wp_lsl (by decide) fun s2 u2 =>
    wp_lsl (by decide) fun s3 u3 => wp_add fun s4 u4 => wp_lsl (by decide) fun s5 u5 => wp_add fun s6 u6 =>
    wp_add fun s7 u7 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u0.rest (by decide)).trans ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans
      ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans
      ((u6.rest (by decide)).trans (u7.rest (by decide))))))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u0.mem]
  · have e4 : s1.gpr .r4 = BitVec.ofNat 64 (j + 1) := by
      simp only [reduceCtorEq, u1.at, u0.at, ↓reduceIte, h14]
      rw [Offset.ofNat_sub_ofNat (by omega), show 8 - (7 - j) = j + 1 by omega]
    simp only [reduceCtorEq, u7.at, u6.at, u5.at, u4.at, u3.at, u2.at, ↓reduceIte,
      (u1.rest (ws := [.r4]) (by decide)).gpr .r6 (by decide), (u0.rest (ws := [.r4]) (by decide)).gpr .r6 (by decide),
      hv.ctx.r6]
    rw [e4, shl_ofNat (by omega), shl_ofNat (by omega), shl_ofNat (by omega)]
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

end

section
variable {b : Addr}

theorem offK {s : State} {r : Reg} {c : Nat} (hr : s.gpr r = b + BitVec.ofNat 64 c) :
    ∀ o p, (o, p) ∈ [(KT, KT + c), (KT + 56, KT + c + 56), (KT + 112, KT + c + 112)] →
      s.gpr r + BitVec.ofNat 64 o = b + BitVec.ofNat 64 p := by
  intro o p h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hr, Offset.add_add_eq _ (Nat.add_comm c KT)]
  · rw [hr, Offset.add_add_eq _ (show c + (KT + 56) = KT + c + 56 by omega)]
  · rw [hr, Offset.add_add_eq _ (show c + (KT + 112) = KT + c + 112 by omega)]

theorem keyStep_ok {sK s : State} {p d : Point} {j : Nat} (hj : j < 7) (h : KInv b sK p d j s) :
    WP isa keyStep s fun t => KInv b sK p d (j + 1) t ∧ (t.gpr .r14 != 0) = decide (7 - (j + 1) ≠ 0) := by
  have hK : KT = 4160 := rfl
  obtain ⟨hv, hr, hf, h14, pR, pP, hd, hk⟩ := h
  unfold keyStep
  refine WP.seq (WP.mono (callProj_ok (JS.refl hv) hd) fun s1 ⟨C1, tx, ty, tz, d1, px, py, pz⟩ => ?_)
  rw [pt_ptOf pR, pt_mk pP] at tx ty tz
  have pT1 : Pt s1.mem b TX TY TZ (Spec.Ed448.pointAdd (kE p d j) d) := ⟨tx, ty, tz⟩
  have pP1 : Pt s1.mem b PX PY Impl.Ed448.PPC64LE.PZ d := ⟨px.trans pP.1, py.trans pP.2.1, pz.trans pP.2.2⟩
  have e14 : s1.gpr .r14 = BitVec.ofNat 64 (7 - j) := by
    rw [C1.r14, BitVec.ofNat_toNat, BitVec.setWidth_eq, h14]
  rw [show keyPtr ++ stSlots .r12 KT [TX, TY, TZ] ++ copySlot RX TX ++ copySlot RY TY ++ copySlot RZ TZ ++
      [.subi .r14 .r14 1] =
      keyPtr ++ ((cp7 .r6 TX .r12 KT ++ (cp7 .r6 TY .r12 (KT + 56) ++ cp7 .r6 TZ .r12 (KT + 112))) ++
        ((cp7 .r6 TX .r6 RX ++ (cp7 .r6 TY .r6 RY ++ cp7 .r6 TZ .r6 RZ)) ++ [.subi .r14 .r14 1])) from rfl]
  refine WP.append (keyPtr_ok C1.ctx hj e14) fun s2 ⟨r2, m2, p2⟩ => ?_
  have v2 : VCtx b s2 := C1.ctx.of_rest r2 (by decide) (by decide)
  have pT2 : Pt s2.mem b TX TY TZ (Spec.Ed448.pointAdd (kE p d j) d) := by rw [m2]; exact pT1
  refine WP.append (copy3_ok v2 (rs := .r6) (rd := .r12) (by decide) (by decide) (by decide) (by decide)
    (by decide) (idp v2.ctx.r6) (offK p2)
    (by intro o ho; simp only [List.mem_cons, List.not_mem_nil, or_false, TX, TY, TZ] at ho; omega)
    (by intro o ho w hw; simp only [List.mem_cons, List.not_mem_nil, or_false, TX, TY, TZ] at ho hw; omega)
    (by omega) (by omega) (by omega) pT2) fun s3 ⟨v3, r3, f3, p3⟩ => ?_
  have pT3 : Pt s3.mem b TX TY TZ (Spec.Ed448.pointAdd (kE p d j) d) :=
    pt_KE (i := j + 1) (by omega) (by simpa only [Nat.add_assoc, Nat.add_comm 56, Nat.add_comm 112] using f3) pT2
      (by simp only [TX, TY, TZ]; omega)
  refine WP.append (copy3_ok v3 (rs := .r6) (rd := .r6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (idp v3.ctx.r6) (idp v3.ctx.r6) (by decide) (by decide) (by decide) (by decide) (by decide) pT3)
    fun s4 ⟨v4, r4, f4, p4⟩ => ?_
  refine wp_subi (by decide) (by decide) fun s5 u5 => WP.block_nil ?_
  have f3' : Frame (R3 b (KT + 168 * (j + 1)) (KT + 168 * (j + 1) + 56) (KT + 168 * (j + 1) + 112)) s2.mem s3.mem := by
    simpa only [Nat.add_assoc, Nat.add_comm 56, Nat.add_comm 112] using f3
  have e4 : s4.gpr .r14 = BitVec.ofNat 64 (7 - j) := by
    rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide), e14]
  have e5 : s5.gpr .r14 = BitVec.ofNat 64 (7 - (j + 1)) := by
    rw [u5.gpr, e4, ofNat_sub_one (by omega) (by omega), show 7 - j - 1 = 7 - (j + 1) by omega]
  refine ⟨⟨v4.of_rest (u5.rest (ws := [.r14]) (by decide)) (by decide) (by decide), ?_, ?_, e5, ?_, ?_, ?_, ?_⟩,
    by rw [e5, ofNat_ne_zero (by omega)]⟩
  · exact hr.trans (C1.rest.trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans (u5.rest (by decide))))))
  · have g2 : Frame [FA b, KR b] s1.mem s3.mem := by rw [← m2]; exact frame_R3_KR (by omega) f3'
    rw [u5.mem]
    exact hf.trans ((frame_FA_K C1.frame).trans (g2.trans (frame_R3_FA f4 (by decide) (by decide) (by decide))))
  · rw [u5.mem]; exact p4
  · rw [u5.mem]
    exact pt_keep3 f4 (pt_KE (i := j + 1) (by omega) f3' (by rw [m2]; exact pP1) (by decide)) (by decide) (by decide)
  · rw [u5.mem, fs_R3 f4 (by decide), fs_KE (i := j + 1) (by omega) f3' (by decide), m2, d1]
  · intro e he
    rw [u5.mem, kpt_lo f4 (by decide) (by omega)]
    rcases Nat.lt_or_ge e (j + 1) with hl | hl
    · rw [kpt_KE (by omega) f3' hl, m2, kpt_hi C1.frame (by omega), hk e (by omega)]
    · obtain rfl : e = j + 1 := by omega
      exact (kpt_pt (p := Spec.Ed448.pointAdd (kE p d j) d)
        (by simpa only [Nat.add_assoc, Nat.add_comm 56, Nat.add_comm 112] using p3) :)

theorem keyTable_ok {s : State} (hv : VCtx b s) {p : Point} (hp : Pt s.mem b NAX NAY ONE p)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa keyTable s (KInv b s p (Proof.Ed448.double p) 7) := by
  unfold keyTable
  refine WP.seq (WP.mono (keyHead_ok hv hp hd) fun s0 h0 => ?_)
  refine WP.loop (M := isa) (Q := KInv b s p (Proof.Ed448.double p) 7)
    (fun n t => 1 ≤ n ∧ n ≤ 7 ∧ KInv b s p (Proof.Ed448.double p) (7 - n) t) ?_ 7 s0 ⟨by omega, by omega, by rw [Nat.sub_self]; exact h0⟩
  rintro n t ⟨hn1, hn2, hl⟩
  refine WP.mono (keyStep_ok (by omega) hl) fun t' ⟨hl', hz⟩ => ?_
  by_cases e : n = 1
  · subst e
    exact .inl ⟨by rw [eval_nonzero, hz]; simp, hl'⟩
  · refine .inr ⟨by rw [eval_nonzero, hz]; simp; omega, n - 1, by omega, by omega, by omega, ?_⟩
    rwa [show 7 - (n - 1) = 7 - n + 1 by omega]

end

section
variable {b : Addr}

theorem keyOk_of {sK t : State} {p : Point} {a : VG.Proof.EdwardsLaw.EPoint dZ} (hp : Rep p a)
    (h : KInv b sK p (Proof.Ed448.double p) 7 t) : KeyOk b a t.mem := fun i hi => by
  rw [h.2.2.2.2.2.2.2 i (by omega)]
  exact kE_rep hp i

/-! ## The loop's start and end -/

theorem jfix_FA {S K : Nat} {m m' : Mem} (hf : Frame [FA b] m m') (h : JFix b S K m) : JFix b S K m' := by
  have hA : ACC = 952 := rfl
  have hT : TB = 1064 := rfl
  have hB : BT = 5504 := rfl
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
    WP isa (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ ([.li .r14 464] : List Instr))) s
      fun t => VCtx b t ∧ Rest [.r7, .r14] s t ∧ Frame (R3 b RX RY RZ) s.mem t.mem ∧
        ptOf (FS t.mem b) = Spec.Ed448.identity ∧ t.gpr .r14 = BitVec.ofNat 64 464 := by
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  simp only [List.append_assoc]
  refine WP.append (constField_ok hv.ctx (o := RX) (by decide) (v := 0) (by decide))
    fun s1 ⟨r1, f1, v1⟩ => ?_
  have hv1 : VCtx b s1 := hv.of_rest r1 (by decide) (by decide)
  refine WP.append (constField_ok hv1.ctx (o := RY) (by decide) (v := 1) (by decide))
    fun s2 ⟨r2, f2, v2⟩ => ?_
  have hv2 : VCtx b s2 := hv1.of_rest r2 (by decide) (by decide)
  refine WP.append (constField_ok hv2.ctx (o := RZ) (by decide) (v := 1) (by decide))
    fun s3 ⟨r3, f3, v3⟩ => ?_
  have hv3 : VCtx b s3 := hv2.of_rest r3 (by decide) (by decide)
  refine wp_li (by decide) fun t u => WP.block_nil ⟨hv3.of_rest (u.rest (ws := [.r14]) (by decide)) (by decide)
    (by decide), (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      (u.rest (by decide)))), ?_, ?_, u.gpr⟩
  · rw [u.mem]
    exact (f1.mono (by simp)).trans ((f2.mono (by simp)).trans (f3.mono (by simp)))
  · simp only [ptOf, Spec.Ed448.identity]
    rw [u.mem, FS, FS, FS, slot_keep f3 (by omega) (by omega) (by omega), slot_keep f2 (by omega) (by omega) (by omega),
      v1, slot_keep f3 (by omega) (by omega) (by omega), v2, v3, Proof.X448.toFe_one]
    rfl

/-- The joint loop from `s`: `R` represents `[S]B + [K]a`, for every `a` the key table holds. -/
theorem joint_ok {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    {s : State} (hv : VCtx b s) (hfx : JFix b S K s.mem) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa jointLoop s fun t => ∃ sL, VCtx b sL ∧ Frame [FA b] s.mem sL.mem ∧ Rest [.r7, .r14] s sL ∧
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
  have dL : FS sL.mem b DK = Spec.Ed448.d := by rw [fs_R3 fL (by decide), hd]
  refine WP.mono (jointLoop_ok (jfix_FA fFA hfx) 464 sL (by decide) (le_refl _)
    ⟨⟨hvL, Rest.refl _ _, Frame.refl _ _, tL⟩, dL, fun a _ => ?_⟩) fun t ht => ⟨sL, hvL, fFA, rL, ht⟩
  beta_reduce
  rw [pL, residual_464 hS, residual_464 hK]
  simpa only [Nat.cast_zero, zero_smul, add_zero] using Proof.Ed448.identity_rep

/-- `R = [4](R + (x, y))`, in the slots `vFinish` reads. -/
theorem addNegR_ok {sL s : State} {n : Nat} (h : JS b sL n s) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa addNegR s fun t => JS b sL n t ∧
      SlotsOk t.mem b RQ (ptV (Proof.Ed448.double (Proof.Ed448.double (Spec.Ed448.pointAdd (ptOf (FS s.mem b))
        ⟨FS s.mem b NRX, FS s.mem b NRY, 1⟩)))
        (Proof.Ed448.double (Proof.Ed448.double (Spec.Ed448.pointAdd (ptOf (FS s.mem b))
          ⟨FS s.mem b NRX, FS s.mem b NRY, 1⟩)))) := by
  have hNX : NRX = 3120 := rfl
  have hNY : NRY = 3176 := rfl
  unfold addNegR
  rw [show copySlot SX NRX ++ copySlot SY NRY = cp7 .r6 NRX .r6 SX ++ cp7 .r6 NRY .r6 SY from rfl]
  refine WP.seq (WP.append (opCp h (rs := .r6) (so := NRX) (o := SX) (ps := NRX) (by decide) (by decide)
    (by decide) (by decide) (by rw [h.ctx.ctx.r6]) (by decide) (by decide) (by decide) (by decide))
    fun s1 ⟨C1, _, x1, k1⟩ =>
    WP.mono (opCp C1 (rs := .r6) (so := NRY) (o := SY) (ps := NRY) (by decide) (by decide)
      (by decide) (by decide) (by rw [C1.ctx.ctx.r6]) (by decide) (by decide) (by decide) (by decide))
      fun s2 ⟨C2, _, y2, k2⟩ => ?_)
  have k12 : ∀ q, (q + 56 ≤ SX ∨ SX + 56 ≤ q) → (q + 56 ≤ SY ∨ SY + 56 ≤ q) → q + 56 ≤ 8192 →
      FS s2.mem b q = FS s.mem b q := fun q a1 a2 a3 => by rw [k2 q a2 a3, k1 q a1 a3]
  have p2 : ptOf (FS s2.mem b) = ptOf (FS s.mem b) := by
    simp only [ptOf]
    rw [k12 RX (by decide) (by decide) (by decide), k12 RY (by decide) (by decide) (by decide),
      k12 RZ (by decide) (by decide) (by decide)]
  have sx2 : FS s2.mem b SX = FS s.mem b NRX := by rw [k2 SX (by decide) (by decide), x1]
  have sy2 : FS s2.mem b SY = FS s.mem b NRY := by rw [y2, k1 NRY (by decide) (by decide)]
  have d2 : FS s2.mem b DK = Spec.Ed448.d := by rw [k12 DK (by decide) (by decide) (by decide), hd]
  refine WP.seq (WP.mono (callAdd_ok C2 d2) fun s3 ⟨C3, p3, d3⟩ => ?_)
  rw [p2, sx2, sy2] at p3
  refine WP.seq (WP.mono (callDbl_ok C3) fun s4 ⟨C4, p4, d4⟩ => ?_)
  refine WP.mono (callDbl_ok C4) fun s5 ⟨C5, p5, d5⟩ => ⟨C5, fun q hq => ?_⟩
  rw [p4, p3] at p5
  rw [d4, d3, d2] at d5
  rw [← p5]
  simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [ptV, ptOf, RX, RY, RZ, PX, PY, Impl.Ed448.PPC64LE.PZ, DK, Impl.X448.PPC64LE.X2, Impl.X448.PPC64LE.Z2,
      Nat.reduceEqDiff, ↓reduceIte]
  exact d5

end

end VG.Proof.Ed448.PPC64LE
