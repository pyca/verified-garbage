module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VLadder
import VerifiedGarbage.Proof.Ed448.RISCV64.VSel
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

/-!
# Ed448's verification on RISCV64: one iteration of the loop

The selection (`vhead_ok`) puts `selP h a r Q` into `P` for the iteration
`h`, from `B`, `a` and `r` above the field area (`PtsOk`); the addition is
base-point multiplication's; the swap (`vswap_ok`) keeps the sum under the
mask `TAB[h]`. The loop (`vloop_ok`) runs the 1832 iterations: `Q` becomes
`vladder4 (4S) (4K) 4 a r 458`.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC BITS X2 Z2 R)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point pointAdd basePoint)

/-- `B`, `a = (ax, ay, 1)`, `r = (rx, ry, 1)` and `1` above the field area. -/
structure PtsOk (b : Addr) (m : Mem) (a r : Point) : Prop where
  bx : FS m b BX = basePoint.X
  by_ : FS m b BY = basePoint.Y
  ax : FS m b NAX = a.X
  ay : FS m b NAY = a.Y
  rx : FS m b NRX = r.X
  ry : FS m b NRY = r.Y
  one : FS m b ONE = 1
  az : a.Z = 1
  rz : r.Z = 1

theorem basePoint_Z : basePoint.Z = 1 := rfl

theorem pick_same {α : Type} (sw : Nat) (x : α) : pick sw x x = x := by
  unfold pick VG.Proof.X25519.sel; split <;> rfl

section
variable {b : Addr} {sL : State} {a r : Point}

theorem PtsOk.frame {m m' : Mem} {a r : Point} (h : PtsOk b m a r) (hf : Frame [FA b] m m') : PtsOk b m' a r :=
  ⟨by rw [fs_above hf (by decide) (by decide)]; exact h.bx, by rw [fs_above hf (by decide) (by decide)]; exact h.by_,
    by rw [fs_above hf (by decide) (by decide)]; exact h.ax, by rw [fs_above hf (by decide) (by decide)]; exact h.ay,
    by rw [fs_above hf (by decide) (by decide)]; exact h.rx, by rw [fs_above hf (by decide) (by decide)]; exact h.ry,
    by rw [fs_above hf (by decide) (by decide)]; exact h.one, h.az, h.rz⟩

theorem bit1_shift (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x <<< 62) >>> 63 = BitVec.ofNat 64 (x / 2 % 2) := by
  apply BitVec.eq_of_toNat_eq
  have := bit_shift (BitVec.ofNat 64 x) (j := 1) (by decide)
  rw [toNat_imm hx, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.pow_one] at this
  rw [this, toNat_imm (by omega_arith)]

theorem vhead_ok (hP : PtsOk b sL.mem a r) {c : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ 1832) {q : Point}
    {a0 : BitVec 64} {s : State} (h : R64.Cur b sL a0 (BitVec.ofNat 64 c) RQ (ptV q q) s) :
    WP isa (.block (([.addi .t1 .t1 (-1)] : List Instr) ++ vSelect)) s
      (R64.Cur b sL a0 (BitVec.ofNat 64 (c - 1)) SQ (ptV q (selP (c - 1) a r q))) := by
  have hc := h.ctx
  have hA := X448.RISCV64.ACC_eq
  have hb0 : (c - 1) % 2 ≤ 1 := by omega_arith
  have hb1 : (c - 1) / 2 % 2 ≤ 1 := by omega_arith
  have hPs := hP.frame h.stp.frame
  simp only [vSelect, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_subi (by decide) fun s1 u1 => ?_
  have e12 : s1.gpr .t1 = BitVec.ofNat 64 (c - 1) := by
    rw [u1.gpr, h.t1, ofNat_sub_one hc1 (by omega_arith)]
  refine wp_sll (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  refine wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  have e11 : s5.gpr .t0 = 0 - BitVec.ofNat 64 ((c - 1) % 2) := by
    rw [u5.gpr, u4.gpr, u4.other _ (by decide), u3.gpr, u2.gpr, e12, par_shift _ (by omega_arith)]; rfl
  have hr5 : Rest [.a1, .t0, .t1] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  have hS5 : SlotsOk s5.mem b RQ (ptV q q) := by rw [hm5]; exact h.slots
  have hP5 : PtsOk b s5.mem a r := by rw [hm5]; exact hPs
  -- The selections by bit 0.
  refine WP.append (selG (o := PX) (q := NRX) (r := NAX) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc5 hb0 e11 hS5 hP5.rx hP5.ax) fun s6 ⟨hr6, hf6, hS6⟩ => ?_
  have hP6 := hP5.frame hf6
  have hc6 : Ctx b s6 := hc5.of_rest hr6 (by decide)
  refine WP.append (selG (o := PY) (q := NRY) (r := NAY) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc6 hb0 (by rw [hr6.gpr _ (by decide), e11]) hS6 hP6.ry hP6.ay)
    fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hP7 := hP6.frame hf7
  have hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  have e11' : ∀ {t : State}, Rest [.a2, .a4] s5 t → t.gpr .t0 = 0 - BitVec.ofNat 64 ((c - 1) % 2) :=
    fun hr => by rw [hr.gpr _ (by decide), e11]
  refine WP.append (selG (o := TX) (q := BX) (r := RX) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc7 hb0 (e11' (hr6.trans hr7)) hS7 hP7.bx (hS7 RX (by decide)))
    fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  have hP8 := hP7.frame hf8
  have hc8 : Ctx b s8 := hc7.of_rest hr8 (by decide)
  refine WP.append (selG (o := TY) (q := BY) (r := RY) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc8 hb0 (e11' (hr6.trans (hr7.trans hr8))) hS8 hP8.by_ (hS8 RY (by decide)))
    fun s9 ⟨hr9, hf9, hS9⟩ => ?_
  have hP9 := hP8.frame hf9
  have hc9 : Ctx b s9 := hc8.of_rest hr9 (by decide)
  refine WP.append (selG (o := TZ) (q := ONE) (r := RZ) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc9 hb0 (e11' (hr6.trans (hr7.trans (hr8.trans hr9)))) hS9 hP9.one (hS9 RZ (by decide)))
    fun s10 ⟨hr10, hf10, hS10⟩ => ?_
  have hP10 := hP9.frame hf10
  have hc10 : Ctx b s10 := hc9.of_rest hr10 (by decide)
  have hr10' : Rest [.a2, .a4] s5 s10 := hr6.trans (hr7.trans (hr8.trans (hr9.trans hr10)))
  -- The selections by bit 1.
  refine wp_sll (by decide) fun s11 u11 => wp_srl (by decide) fun s12 u12 => ?_
  refine wp_li (by decide) fun s13 u13 => wp_sub fun s14 u14 => ?_
  have e11b : s14.gpr .t0 = 0 - BitVec.ofNat 64 ((c - 1) / 2 % 2) := by
    rw [u14.gpr, u13.gpr, u13.other _ (by decide), u12.gpr, u11.gpr, hr10'.gpr _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e12,
      bit1_shift _ (by omega_arith)]; rfl
  have hr14 : Rest [.a1, .t0] s10 s14 := (u11.rest (by decide)).trans ((u12.rest (by decide)).trans
    ((u13.rest (by decide)).trans (u14.rest (by decide))))
  have hm14 : s14.mem = s10.mem := by rw [u14.mem, u13.mem, u12.mem, u11.mem]
  have hc14 : Ctx b s14 := hc10.of_rest hr14 (by decide)
  have hS14 := hS10
  rw [← hm14] at hS14
  have hP14 : PtsOk b s14.mem a r := by rw [hm14]; exact hP10
  refine WP.append (selG (o := PX) (q := PX) (r := TX) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc14 hb1 e11b hS14 (hS14 PX (by decide)) (hS14 TX (by decide)))
    fun s15 ⟨hr15, hf15, hS15⟩ => ?_
  have hc15 : Ctx b s15 := hc14.of_rest hr15 (by decide)
  refine WP.append (selG (o := PY) (q := PY) (r := TY) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc15 hb1 (by rw [hr15.gpr _ (by decide), e11b]) hS15 (hS15 PY (by decide))
    (hS15 TY (by decide))) fun s16 ⟨hr16, hf16, hS16⟩ => ?_
  have hc16 : Ctx b s16 := hc15.of_rest hr16 (by decide)
  have hP16 := (hP14.frame hf15).frame hf16
  refine WP.mono (selG (o := PZ) (q := ONE) (r := TZ) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc16 hb1 (by rw [hr16.gpr _ (by decide), hr15.gpr _ (by decide), e11b]) hS16 hP16.one
    (hS16 TZ (by decide))) fun t ⟨hrt, hft, hSt⟩ => ?_
  have hrw : Rest R64.work s t := by
    refine (hr5.mono (by decide)).trans ((hr10'.mono (by decide)).trans ((hr14.mono (by decide)).trans ?_))
    exact (hr15.mono (by decide)).trans ((hr16.mono (by decide)).trans (hrt.mono (by decide)))
  have hrt' : Rest [.a1, .a2, .a4, .t0] s1 t := by
    refine ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans
      (u5.rest (by decide))))).trans ?_
    refine (hr10'.mono (by decide)).trans ((hr14.mono (by decide)).trans ?_)
    exact (hr15.mono (by decide)).trans ((hr16.mono (by decide)).trans (hrt.mono (by decide)))
  have hft' : Frame [FA b] s.mem t.mem := by
    rw [← hm5]
    refine hf6.trans (hf7.trans (hf8.trans (hf9.trans (hf10.trans ?_))))
    rw [← hm14]; exact hf15.trans (hf16.trans hft)
  have hr0 : Rest [.a1, .a2, .a4, .t0, .t1] s t :=
    ((u1.rest (ws := [.t1]) (by decide)).mono (by decide)).trans (hrt'.mono (by decide))
  refine ⟨hc.of_rest hrw (by decide), h.stp.trans ⟨hrw, hft'⟩, by rw [hr0.gpr _ (by decide), h.t2], ?_, ?_⟩
  · rw [hrt'.gpr _ (by decide), e12]
  · refine (hSt.mono (by decide)).congr fun q' hq' => ?_
    simp only [SQ, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd, ptV, selP, pick_X, pick_Y, pick_Z, hP.az, hP.rz, basePoint_Z, pick_same, RX, RY, RZ, PX, PY,
        PZ, TX, TY, TZ, DK, X2, Z2, Nat.reduceEqDiff, ↓reduceIte]

/-- A byte above the field area, kept by a frame of it. -/
theorem byte_hi {m m' : Mem} (hf : Frame [FA b] m m') {d : Nat} (hd : ACC + 112 ≤ d)
    (hd' : d < 8184) : m' (b + BitVec.ofNat 64 d) = m (b + BitVec.ofNat 64 d) :=
  hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact fun h => Offset.disjoint_base b (d := d) (n := 1) (k := ACC + 112) hd (by omega_using [hd'])
      _ (Region.contains_self _ _) h

theorem vswap_ok (hL : VCtx b sL) {S K : Nat} (hT : TabIs b sL.mem (tabV S K)) {h : Nat} (hh : h < 1832) {q p : Point}
    {a0 : BitVec 64} {s : State} (hcur : R64.Cur b sL a0 (BitVec.ofNat 64 h) FQ (addV q p) s) :
    WP isa (.block vSwap) s (R64.Cur b sL a0 (BitVec.ofNat 64 h) FQ
      (swapV RZ TZ (tabV S K h) (swapV RY TY (tabV S K h) (swapV RX TX (tabV S K h) (addV q p))))) := by
  have hc := hcur.ctx
  have hv : VCtx b s := hL.of_rest hcur.stp.rest (by decide) (by decide)
  have hTB : TAB = 2104 := rfl
  have hO : OUT = 2048 := rfl
  have hsw := tabV_le S K h
  simp only [vSwap, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_add fun s1 u1 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (TAB + h)) (by decide)
    (by rw [u1.gpr, hv.a0, hcur.t1, Offset.add_add, Offset.add_add]; congr 2; omega_arith)
    (by rw [u1.rd, u1.wr]; exact hv.inR (by omega_arith)) fun s2 u2 => ?_
  have e4 : s2.gpr .a1 = BitVec.ofNat 64 (tabV S K h) := by
    rw [u2.gpr, u1.mem, byte_hi hcur.stp.frame (by unfold ACC; omega_arith) (by omega_arith), hT h hh,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  refine wp_li (by decide) fun s3 u3 => wp_sub fun s4 u4 => ?_
  have e11 : s4.gpr .t0 = 0 - BitVec.ofNat 64 (tabV S K h) := by
    rw [u4.gpr, u3.gpr, u3.other _ (by decide), e4]; rfl
  have hr4 : Rest [.a1, .t0] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have hc4 : Ctx b s4 := hc.of_rest hr4 (by decide)
  have hS4 : SlotsOk s4.mem b FQ (addV q p) := by rw [hm4]; exact hcur.slots
  refine WP.append (R64.cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc4 hsw e11 hS4) fun s5 ⟨hr5, hf5, hS5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  refine WP.append (R64.cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc5 hsw (by rw [hr5.gpr _ (by decide), e11]) hS5) fun s6 ⟨hr6, hf6, hS6⟩ => ?_
  have hc6 : Ctx b s6 := hc5.of_rest hr6 (by decide)
  refine WP.mono (R64.cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc6 hsw (by rw [hr6.gpr _ (by decide), hr5.gpr _ (by decide), e11]) hS6) fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hr7' : Rest [.a1, .a2, .a4, .a5, .t0] s s7 :=
    (hr4.mono (by decide)).trans ((hr5.mono (by decide)).trans ((hr6.mono (by decide)).trans
      (hr7.mono (by decide))))
  exact ⟨hc.of_rest hr7' (by decide), hcur.stp.trans ⟨hr7'.mono (by decide), by
      rw [← hm4]; exact hf5.trans (hf6.trans hf7)⟩,
    by rw [hr7'.gpr _ (by decide), hcur.t2], by rw [hr7'.gpr _ (by decide), hcur.t1], hS7⟩

/-- The loop invariant from `sL` with the counter `c`. -/
structure VInv (b : Addr) (S K : Nat) (a r : Point) (sL : State) (c : Nat) (s : State) : Prop where
  cur : R64.Cur b sL (s.gpr .t2) (BitVec.ofNat 64 c) RQ
    (ptV (Qv (4 * S) (4 * K) a r c) (Qv (4 * S) (4 * K) a r c)) s

theorem vStep_eq : vStep =
    .seq (.block (([.addi .t1 .t1 (-1)] : List Instr) ++ vSelect))
      (.seq (R64.opsCode addOps (R64.fcode (FOp.mul TZ TF TG))) (.block vSwap)) := rfl

theorem vstep_ok (hL : VCtx b sL) {S K : Nat} (hT : TabIs b sL.mem (tabV S K)) (hP : PtsOk b sL.mem a r) {c : Nat}
    (hc1 : 1 ≤ c) (hc2 : c ≤ 1832) {s : State} (h : VInv b S K a r sL c s) :
    WP isa vStep s fun s' => VInv b S K a r sL (c - 1) s' ∧ (s'.gpr .t1 != 0) = decide (c - 1 ≠ 0) := by
  rw [vStep_eq]
  obtain ⟨o1, o2, o3, o4⟩ := last_ok
  refine WP.seq (WP.mono (vhead_ok hP hc1 hc2 h.cur) fun s1 h1 => WP.seq
    (R64.ops_ok addOps SQ _ s1 addOps_ok h1 fun s2 h2 => WP.mono (R64.op_ok (.mul TZ TF TG) o1 o2 o3 o4 h2)
      fun s3 h3 => WP.mono (vswap_ok hL (S := S) (K := K) (q := Qv (4 * S) (4 * K) a r c)
        (p := selP (c - 1) a r (Qv (4 * S) (4 * K) a r c)) hT (by omega_arith) h3) fun s4 h4 => ?_))
  refine ⟨⟨⟨h4.ctx, h4.stp, rfl, h4.t1, ?_⟩⟩, ?_⟩
  · refine (h4.slots.mono (by decide)).congr fun q hq => ?_
    obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := addV_vals (Qv (4 * S) (4 * K) a r c)
      (selP (c - 1) a r (Qv (4 * S) (4 * K) a r c))
    rw [← qv_step S K a r hc1 hc2]
    simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp only [swapV, ptV, pick_X, pick_Y, pick_Z, RX, RY, RZ, PX, PY, PZ, DK, TX, TY, TZ, X2, Z2,
        Nat.reduceEqDiff, ↓reduceIte] at v1 v2 v3 v4 v5 v6 v7 ⊢ <;>
      simp only [v1, v2, v3, v4, v5, v6, v7, pick]
  · rw [h4.t1, ofNat_ne_zero (by omega_arith)]

/-- The loop, from `Q` the neutral point: `Q = [4S]B + [4K]a + [4]r`. -/
theorem vloop_ok {S K : Nat} {s : State} (hv : VCtx b s) (hT : TabIs b s.mem (tabV S K)) (hP : PtsOk b s.mem a r)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa vLoop s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b RQ (ptV (VG.Proof.Ed448.vladder4 (4 * S) (4 * K) 4 a r 458)
        (VG.Proof.Ed448.vladder4 (4 * S) (4 * K) 4 a r 458)) := by
  have hc := hv.ctx
  have hA := X448.RISCV64.ACC_eq
  have hTB : TAB = 2104 := rfl
  unfold vLoop
  simp only [List.append_assoc]
  refine WP.seq (WP.append (constField_ok hc (o := RX) (by decide) (by decide) (v := 0) (by decide)) fun s1 ⟨r1, f1, v1⟩ =>
    WP.append (constField_ok (hc.of_rest r1 (by decide)) (o := RY) (by decide) (by decide) (v := 1) (by decide))
      fun s2 ⟨r2, f2, v2⟩ =>
    WP.append (constField_ok ((hc.of_rest r1 (by decide)).of_rest r2 (by decide)) (o := RZ) (by decide) (by decide) (v := 1)
      (by decide)) fun s3 ⟨r3, f3, v3⟩ => wp_li (by decide) fun s4 u4 => WP.block_nil ?_)
  have hr4 : Rest [.a4, .t1] s s4 := (r1.mono (by decide)).trans ((r2.mono (by decide)).trans
    ((r3.mono (by decide)).trans (u4.rest (by decide))))
  have hc4 : Ctx b s4 := hc.of_rest hr4 (by decide)
  have fFA : ∀ {m m' : Mem} {o : Nat}, o + 56 ≤ ACC → Frame [⟨b + BitVec.ofNat 64 o, 56⟩] m m' →
      Frame [FA b] m m' := fun ho hf => hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)⟩
  have f4 : Frame [FA b] s.mem s4.mem := by
    rw [u4.mem]; exact (fFA (by decide) f1).trans ((fFA (by decide) f2).trans (fFA (by decide) f3))
  have hst : R64.Stp b s s4 := ⟨hr4.mono (by decide), f4⟩
  have hT4 : TabIs b s4.mem (tabV S K) := fun h hh => by
    rw [byte_hi f4 (by omega_arith) (by omega_arith)]; exact hT h hh
  have hP4 := hP.frame f4
  have hS4 : SlotsOk s4.mem b RQ (ptV (Qv (4 * S) (4 * K) a r 1832) (Qv (4 * S) (4 * K) a r 1832)) := by
    rw [qv_1832]
    intro q hq
    simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [u4.mem]
    rcases hq with rfl | rfl | rfl | rfl
    · rw [FS, slot_keep f3 (by decide) (by decide) (by decide), slot_keep f2 (by decide) (by decide) (by decide), v1,
        VG.Proof.X448.toFe_zero]
      rfl
    · rw [FS, slot_keep f3 (by decide) (by decide) (by decide), v2, VG.Proof.X448.toFe_one]; rfl
    · rw [FS, v3, VG.Proof.X448.toFe_one]; rfl
    · rw [FS, slot_keep f3 (by decide) (by decide) (by decide), slot_keep f2 (by decide) (by decide) (by decide),
        slot_keep f1 (by decide) (by decide) (by decide), ← FS, hd]
      rfl
  have h1832 : VInv b S K a r s4 1832 s4 := ⟨⟨hc4, R64.Stp.refl _ _, rfl, by rw [u4.gpr], hS4⟩⟩
  refine WP.mono (Q := VInv b S K a r s4 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 1832 ∧ VInv b S K a r s4 m s') ?_ 1832 s4 ⟨by decide, Nat.le_refl _, h1832⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, by rw [← qv_0]; exact h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (vstep_ok (hv.of_rest hr4 (by decide) (by decide)) hT4 hP4 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

end

end VG.Proof.Ed448.RISCV64
