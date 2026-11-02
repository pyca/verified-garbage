module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowTable
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # The control blocks of the windowed ARMv7 exponentiation

Each reads and writes header words only (and registers): the table's
pointer and index, the digit and the count of pending bits. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov wp_str wp_cmp op2_reg op2_imm op2_lsl op2_lsr dpVal
  ofNat_beq_zero)

/-- A write to a header word leaves the table alone. -/
theorem TableHolds.after_header {m m' : Mem} {base : BitVec 32} {len w M x k d : Nat}
    (h : TableHolds m base w M x k) (fits : arrAt w 16 ≤ 8 * len) (nowrap : base.toNat + 8 * len ≤ 2 ^ 32)
    (hd : d + 4 ≤ 256) (hk : k ≤ 8) (outside : Outside (State.addr base) d 4 m m') :
    TableHolds m' base w M x k := by
  intro j hj
  have bound := Nat.le_trans (array_end_le (w := w) (show 8 + j < 16 by omega_arith)) fits
  have value : numAt m' (State.addr base) w (8 + j) = numAt m (State.addr base) w (8 + j) := by
    rw [numAt_native, numAt_native]
    apply outside.val32
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith
    · omega_arith
  rw [value]
  exact h j hj

/-- The mask bit of an entry: one for the digit's. -/
theorem mask_bit : ∀ d < 8, ∀ j < 8,
    ((BitVec.ofNat 32 d ^^^ BitVec.ofNat 32 j) - 1) >>> 31 = if d = j then (1 : BitVec 32) else 0 := by
  decide

theorem stride_value (w : Nat) :
    (BitVec.ofNat 32 w + BitVec.ofNat 32 2) <<< 3 = BitVec.ofNat 32 (8 * (w + 2)) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change (BitVec.ofNat 32 w + BitVec.ofNat 32 2) * BitVec.ofNat 32 8 = _
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul]
  congr 1
  omega_arith

theorem entry_next (base : BitVec 32) (w j : Nat) :
    base + BitVec.ofNat 32 (arrAt w (8 + j)) + BitVec.ofNat 32 (8 * (w + 2)) =
      base + BitVec.ofNat 32 (arrAt w (8 + (j + 1))) := by
  rw [Offset.add_add]
  congr 2
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  generalize 8 * (w + 2) = a
  rw [show 8 + (j + 1) = (8 + j) + 1 by omega_arith, Nat.add_mul (8 + j), Nat.one_mul]
  omega_arith

/-- The table's first entry, from array 7's address. -/
theorem tableStart_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block tableStart) s fun t =>
      t.gpr .r12 = base + BitVec.ofNat 32 (arrAt w (8 + 0)) ∧ t.mem = s.mem ∧ Rest [.r1, .r12] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)
  unfold tableStart
  refine wp_ldr (a := off (State.addr base) 120) (by decide) (addr 120 (by omega_arith))
    (h.workspace.read (by omega_arith)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 48 (by omega_arith))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun v b => ?_
  refine wp_dp (op2_imm (by decide)) fun z c => ?_
  refine wp_mov (op2_lsl (by decide)) fun q d => ?_
  refine wp_dp (op2_reg _ _) fun t e => WP.block_nil ?_
  refine ⟨?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans (e.rest (by decide)))))⟩
  rw [e.gpr, dpVal, d.other .r12 (by decide), c.other .r12 (by decide), b.other .r12 (by decide), a.gpr,
    d.gpr, c.gpr, dpVal, b.gpr, a.mem, header.array 7 (by decide), header.count]
  change base + BitVec.ofNat 32 (arrAt w 7) + (BitVec.ofNat 32 w + BitVec.ofNat 32 2) <<< 3 = _
  rw [stride_value, Offset.add_add]
  congr 2
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  omega_arith

theorem index_next : ∀ j < 8, (BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 8 == 0) = decide (j + 1 = 8) := by
  decide

theorem pending_next : ∀ q < 3, (BitVec.ofNat 32 (q + 1) - BitVec.ofNat 32 3 == 0) = decide (q + 1 = 3) := by
  decide

/-- The next entry and its index; Z after the last. -/
theorem entryNext_ok (s : State) {base : BitVec 32} {len w j : Nat}
    (h : ArithmeticReady base len w s) (hj : j < 8)
    (entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j)))
    (index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j) :
    WP isa (.block entryNext) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 220)
        (base + BitVec.ofNat 32 (arrAt w (8 + (j + 1))))).writeW
          (off (State.addr base) 228) (BitVec.ofNat 32 (j + 1)) ∧
      t.z = decide (j + 1 = 8) ∧ Rest [.r1, .r2] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)
  unfold entryNext
  refine wp_ldr (a := off (State.addr base) 220) (by decide) (addr 220 (by omega_arith))
    (h.workspace.read (by omega_arith)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 48 (by omega_arith))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun v b => ?_
  refine wp_dp (op2_imm (by decide)) fun z c => ?_
  refine wp_dp (op2_lsl (by decide)) fun q d => ?_
  have r0q : q.gpr .r0 = s.gpr .r0 := by
    rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide)]
  have next : q.gpr .r1 = base + BitVec.ofNat 32 (arrAt w (8 + (j + 1))) := by
    rw [d.gpr, dpVal, c.other .r1 (by decide), b.other .r1 (by decide), a.gpr, entry,
      c.gpr, dpVal, b.gpr, a.mem, header.count]
    change base + BitVec.ofNat 32 (arrAt w (8 + j)) + (BitVec.ofNat 32 w + BitVec.ofNat 32 2) <<< 3 = _
    rw [stride_value, entry_next]
  refine wp_str (a := off (State.addr base) 220) (by decide) (by rw [r0q]; exact addr 220 (by omega_arith))
    (by rw [d.wr, c.wr, b.wr, a.wr]; exact h.workspace.write (by omega_arith)) fun y e => ?_
  have memY : y.mem = s.mem.writeW (off (State.addr base) 220)
      (base + BitVec.ofNat 32 (arrAt w (8 + (j + 1)))) := by
    rw [e.mem, d.mem, c.mem, b.mem, a.mem, next]
  have outsideY := writeW32_outside s.mem (State.addr base) (d := 220)
    (base + BitVec.ofNat 32 (arrAt w (8 + (j + 1)))) (by decide)
  rw [← memY] at outsideY
  refine wp_ldr (a := off (State.addr base) 228) (by decide)
    (by rw [congrFun e.gpr .r0, r0q]; exact addr 228 (by omega_arith))
    (by rw [e.rd, e.wr, d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega_arith))
    fun g f => ?_
  refine wp_dp (op2_imm (by decide)) fun g2 f2 => ?_
  have value : g2.gpr .r1 = BitVec.ofNat 32 (j + 1) := by
    rw [f2.gpr, dpVal, f.gpr, outside_read32 outsideY (d := 228) (by decide) (by decide), index]
    exact (BitVec.ofNat_add _ _).symm
  refine wp_str (a := off (State.addr base) 228) (by decide)
    (by rw [f2.other .r0 (by decide), f.other .r0 (by decide), congrFun e.gpr .r0, r0q]; exact addr 228 (by omega_arith))
    (by rw [f2.wr, f.wr, e.wr, d.wr, c.wr, b.wr, a.wr]; exact h.workspace.write (by omega_arith)) fun g3 f3 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t f4 zz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [f4.mem, f3.mem, f2.mem, f.mem, memY, value]
  · rw [zz, congrFun f3.gpr .r1, value]
    exact index_next j hj
  · exact (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans ((e.rest _).trans ((f.rest (by decide)).trans ((f2.rest (by decide)).trans
        ((f3.rest _).trans (f4.rest _))))))))

/-- The table's first entry and index 0. -/
theorem tableInit_ok (s : State) {base : BitVec 32} {len w : Nat} (h : ArithmeticReady base len w s) :
    WP isa (.block tableInit) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 220) (base + BitVec.ofNat 32 (arrAt w (8 + 0)))).writeW
        (off (State.addr base) 228) (BitVec.ofNat 32 0) ∧ Rest [.r1, .r12] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)
  unfold tableInit
  apply WP.block_append_iff.mpr
  refine WP.mono (tableStart_ok s h) ?_
  rintro u ⟨r12, memU, restU⟩
  have r0u : u.gpr .r0 = s.gpr .r0 := restU.gpr .r0 (by decide)
  refine wp_str (a := off (State.addr base) 220) (by decide) (by rw [r0u]; exact addr 220 (by omega_arith))
    (by rw [restU.wr]; exact h.workspace.write (by omega_arith)) fun v a => ?_
  refine wp_mov (op2_imm (by decide)) fun z b => ?_
  refine wp_str (a := off (State.addr base) 228) (by decide)
    (by rw [b.other .r0 (by decide), congrFun a.gpr .r0, r0u]; exact addr 228 (by omega_arith))
    (by rw [b.wr, a.wr, restU.wr]; exact h.workspace.write (by omega_arith)) fun t c => WP.block_nil ?_
  refine ⟨?_, restU.trans ((a.rest _).trans ((b.rest (by decide)).trans (c.rest _)))⟩
  rw [c.mem, b.mem, a.mem, memU, b.gpr, r12]
  rfl

/-- The mask bit of the entry at index `j` for the digit `d`. -/
theorem scanBit_ok (s : State) {base : BitVec 32} {len w d j : Nat}
    (h : ArithmeticReady base len w s) (hd : d < 8) (hj : j < 8)
    (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d)
    (index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j) :
    WP isa (.block scanBit) s fun t =>
      t.gpr .r11 = (if d = j then 1 else 0) ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r11] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)
  unfold scanBit
  refine wp_ldr (a := off (State.addr base) 196) (by decide) (addr 196 (by omega_arith))
    (h.workspace.read (by omega_arith)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 228) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 228 (by omega_arith))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun v b => ?_
  refine wp_dp (op2_reg _ _) fun z c => ?_
  refine wp_dp (op2_imm (by decide)) fun q e => ?_
  refine wp_mov (op2_lsr (by decide)) fun t f => WP.block_nil ?_
  refine ⟨?_, f.mem.trans (e.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((e.rest (by decide)).trans (f.rest (by decide)))))⟩
  rw [f.gpr, e.gpr, dpVal, c.gpr, dpVal, b.other .r1 (by decide), a.gpr, digit, b.gpr, a.mem, index]
  exact mask_bit d hd j hj

/-- No pending bits. -/
theorem windowReset_ok (s : State) {base : BitVec 32} {len w : Nat} (h : ArithmeticReady base len w s) :
    WP isa (.block windowReset) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 196) (BitVec.ofNat 32 0)).writeW
        (off (State.addr base) 204) (BitVec.ofNat 32 0) ∧ Rest [.r1] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)
  unfold windowReset
  refine wp_mov (op2_imm (by decide)) fun u a => ?_
  refine wp_str (a := off (State.addr base) 196) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 196 (by omega_arith))
    (by rw [a.wr]; exact h.workspace.write (by omega_arith)) fun v b => ?_
  refine wp_str (a := off (State.addr base) 204) (by decide)
    (by rw [congrFun b.gpr .r0, a.other .r0 (by decide)]; exact addr 204 (by omega_arith))
    (by rw [b.wr, a.wr]; exact h.workspace.write (by omega_arith)) fun t c => WP.block_nil ?_
  refine ⟨?_, (a.rest (by decide)).trans ((b.rest _).trans (c.rest _))⟩
  rw [c.mem, b.mem, a.mem, congrFun b.gpr .r1, a.gpr]
  rfl

/-- The next bit joins the digit and the count of pending bits; Z for three. -/
theorem windowBitValue_ok (s : State) {base : BitVec 32} {len w V p q : Nat}
    (h : ArithmeticReady base len w s) (hv : V < 2 ^ 32) (hq : q < 3)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V)
    (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 p)
    (pending : s.mem.readW (off (State.addr base) 204) 32 = BitVec.ofNat 32 q) :
    WP isa (.block windowBitValue) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 196) (BitVec.ofNat 32 (2 * p + V / 128 % 2))).writeW
        (off (State.addr base) 204) (BitVec.ofNat 32 (q + 1)) ∧
      t.z = decide (q + 1 = 3) ∧ Rest [.r1, .r2] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)
  unfold windowBitValue
  refine wp_ldr (a := off (State.addr base) 200) (by decide) (addr 200 (by omega_arith))
    (h.workspace.read (by omega_arith)) fun u a => ?_
  refine wp_mov (op2_lsr (by decide)) fun v b => ?_
  refine wp_dp (op2_imm (by decide)) fun z c => ?_
  have bit : z.gpr .r1 = BitVec.ofNat 32 (V / 128 % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [c.gpr, dpVal, b.gpr, a.gpr, byte, BitVec.toNat_and, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow,
      show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat]
    simp only [Nat.reducePow]
    omega_arith
  have r0z : z.gpr .r0 = s.gpr .r0 := by
    rw [c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide)]
  refine wp_ldr (a := off (State.addr base) 196) (by decide) (by rw [r0z]; exact addr 196 (by omega_arith))
    (by rw [c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun y d => ?_
  refine wp_dp (op2_lsl (by decide)) fun g e => ?_
  have joined : g.gpr .r2 = BitVec.ofNat 32 (2 * p + V / 128 % 2) := by
    rw [e.gpr, dpVal, d.other .r1 (by decide), bit, d.gpr, c.mem, b.mem, a.mem, digit,
      BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (V / 128 % 2) + BitVec.ofNat 32 p * BitVec.ofNat 32 2 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    omega_arith
  refine wp_str (a := off (State.addr base) 196) (by decide)
    (by rw [e.other .r0 (by decide), d.other .r0 (by decide), r0z]; exact addr 196 (by omega_arith))
    (by rw [e.wr, d.wr, c.wr, b.wr, a.wr]; exact h.workspace.write (by omega_arith)) fun k f => ?_
  have memK : k.mem = s.mem.writeW (off (State.addr base) 196) (BitVec.ofNat 32 (2 * p + V / 128 % 2)) := by
    rw [f.mem, e.mem, d.mem, c.mem, b.mem, a.mem, joined]
  have outsideK := writeW32_outside s.mem (State.addr base) (d := 196)
    (BitVec.ofNat 32 (2 * p + V / 128 % 2)) (by decide)
  rw [← memK] at outsideK
  have r0k : k.gpr .r0 = s.gpr .r0 := by
    rw [congrFun f.gpr .r0, e.other .r0 (by decide), d.other .r0 (by decide), r0z]
  refine wp_ldr (a := off (State.addr base) 204) (by decide) (by rw [r0k]; exact addr 204 (by omega_arith))
    (by rw [f.rd, f.wr, e.rd, e.wr, d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]
        exact h.workspace.read (by omega_arith)) fun l g1 => ?_
  refine wp_dp (op2_imm (by decide)) fun l2 g2 => ?_
  have count : l2.gpr .r1 = BitVec.ofNat 32 (q + 1) := by
    rw [g2.gpr, dpVal, g1.gpr, outside_read32 outsideK (d := 204) (by decide) (by decide), pending]
    exact (BitVec.ofNat_add _ _).symm
  refine wp_str (a := off (State.addr base) 204) (by decide)
    (by rw [g2.other .r0 (by decide), g1.other .r0 (by decide), r0k]; exact addr 204 (by omega_arith))
    (by rw [g2.wr, g1.wr, f.wr, e.wr, d.wr, c.wr, b.wr, a.wr]; exact h.workspace.write (by omega_arith))
    fun l3 g3 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t g4 zz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [g4.mem, g3.mem, g2.mem, g1.mem, memK, count]
  · rw [zz, congrFun g3.gpr .r1, count]
    exact pending_next q hq
  · exact (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans ((e.rest (by decide)).trans ((f.rest _).trans ((g1.rest (by decide)).trans
        ((g2.rest (by decide)).trans ((g3.rest _).trans (g4.rest _)))))))))

end VG.Proof.Bignum.Arm
