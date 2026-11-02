module
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Selections among the layout's arrays and the table's entries -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout Keeps)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_reg op2_imm dpVal)

/-- `selectRow` from arrays `a` or `b` (by the bit) to array `o`, any of the
first sixteen, then the workspace pointer from the stack; the registers set
up from `s0`, ready, with the same memory. -/
theorem selectAt_ok (s : State) {s0 : State} {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s0) (mem : s.mem = s0.mem) (rest : Rest roundClobbers s0 s)
    (fits : arrAt w 16 ≤ 8 * len) (ho : o < 16) (ho0 : o ≠ 0) (ha : a < 16) (hb : b < 16)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w o))
    (p10 : s.gpr .r10 = base + BitVec.ofNat 32 (arrAt w a))
    (p12 : s.gpr .r12 = base + BitVec.ofNat 32 (arrAt w b))
    (count : s.gpr .lr = BitVec.ofNat 32 (2 * w)) (bit : (s.gpr .r11).toNat ≤ 1) :
    WP isa (.seq selectRow (.block [.ldrSp .r0 0])) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o = (if (s.gpr .r11).toNat = 0 then
        numAt s0.mem (State.addr base) w a else numAt s0.mem (State.addr base) w b) ∧
      Outside (State.addr base) (arrAt w o) (8 * w) s0.mem t.mem ∧
      Keeps (State.addr base) len w o s0.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s0.mem t.mem ∧ Rest roundClobbers s0 t := by
  have ws := h.workspace.congr rest.wr
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fo := Nat.le_trans (array_end_le (w := w) ho) fits
  have fa := Nat.le_trans (array_end_le (w := w) ha) fits
  have fb := Nat.le_trans (array_end_le (w := w) hb) fits
  have ctx : SelectCtx s base (8 * len) (arrAt w o) (arrAt w a) (arrAt w b) (2 * w) :=
    ⟨ws.nowrap, by omega, by omega, by omega, array_select_separate w o a, array_select_separate w o b,
      ws.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (selectAliasRow_ok s ctx (by omega) p0 p10 p12 count bit) ?_
  intro v inv
  have value := inv.value
  have outside := inv.outside
  rw [mem, ← numAt_native, ← numAt_native, ← numAt_native] at value
  rw [mem, show 4 * (2 * w) = 8 * w by omega] at outside
  have frame := outside_workspace outside (size := 8 * len) (by omega)
  have keeps := outside_array_keeps outside (len := len) (by have := ws.nowrap; omega)
  have restV : Rest roundClobbers s0 v :=
    rest.trans (inv.rest.mono (by decide))
  refine WP.mono (restoreBase_ok v
    (by rw [restV.rd, restV.wr, restV.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved restV.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  rw [← memT] at frame keeps outside value
  have restT' := restV.trans (restT.mono (by decide))
  exact ⟨(h.after_array ho0 keeps frame restT' ptrT).1, value, outside, keeps, frame, restT'⟩

/-- Arrays outside the written one keep their numbers. -/
theorem outside_num {m m' : Mem} {base : BitVec 32} {len w o q : Nat}
    (outside : Outside (State.addr base) (arrAt w o) (8 * w) m m') (fits : arrAt w 16 ≤ 8 * len)
    (nowrap : base.toNat + 8 * len ≤ 2 ^ 32) (hq : q < 16) (neq : q ≠ o) :
    numAt m' (State.addr base) w q = numAt m (State.addr base) w q := by
  have fq := Nat.le_trans (array_end_le (w := w) hq) fits
  rw [numAt_native, numAt_native]
  apply outside.val32
  · have := array_sep (w := w) neq; omega
  · omega

theorem entryCopyArgs_ok (s : State) {base : BitVec 32} {len w a j : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8)
    (entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j))) :
    WP isa (.block (entryCopyArgs a)) s fun t =>
      t.gpr .r11 = 1 ∧ t.gpr .r12 = base + BitVec.ofNat 32 (arrAt w a) ∧
      t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (arrAt w (8 + j)) ∧
      t.gpr .r10 = base + BitVec.ofNat 32 (arrAt w (8 + j)) ∧
      t.mem = s.mem ∧ Rest [.r0, .r10, .r11, .r12, .lr] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold entryCopyArgs
  refine wp_mov (op2_imm (by decide)) fun u a1 => ?_
  refine wp_ldr (a := off (State.addr base) (64 + 8 * a)) (by omega)
    (by rw [a1.other .r0 (by decide)]; exact addr _ (by omega))
    (by rw [a1.rd, a1.wr]; exact h.workspace.read (by omega)) fun v b => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [b.other .r0 (by decide), a1.other .r0 (by decide)]; exact addr 48 (by omega))
    (by rw [b.rd, b.wr, a1.rd, a1.wr]; exact h.workspace.read (by omega)) fun z c => ?_
  refine wp_dp (op2_reg _ _) fun q d => ?_
  refine wp_ldr (a := off (State.addr base) 220) (by decide)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide),
      a1.other .r0 (by decide)]; exact addr 220 (by omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a1.rd, a1.wr]; exact h.workspace.read (by omega)) fun y e => ?_
  refine wp_mov (op2_reg _ _) fun t f => WP.block_nil ?_
  have r0 : y.gpr .r0 = base + BitVec.ofNat 32 (arrAt w (8 + j)) := by
    rw [e.gpr, d.mem, c.mem, b.mem, a1.mem, entry]
  refine ⟨?_, ?_, ?_, by rw [f.other .r0 (by decide)]; exact r0, by rw [f.gpr]; exact r0,
    f.mem.trans (e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a1.mem)))),
    (a1.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans ((e.rest (by decide)).trans (f.rest (by decide))))))⟩
  · rw [f.other .r11 (by decide), e.other .r11 (by decide), d.other .r11 (by decide),
      c.other .r11 (by decide), b.other .r11 (by decide), a1.gpr]
  · rw [f.other .r12 (by decide), e.other .r12 (by decide), d.other .r12 (by decide),
      c.other .r12 (by decide), b.gpr, a1.mem]
    exact header.array a ha
  · rw [f.other .lr (by decide), e.other .lr (by decide), d.gpr, dpVal, c.gpr, b.mem, a1.mem,
      header.count, ← BitVec.ofNat_add, show w + w = 2 * w by omega]

theorem scanArgs_ok (s : State) {base : BitVec 32} {len w j : Nat}
    (h : ArithmeticReady base len w s)
    (entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j))) :
    WP isa (.block scanArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 1) ∧ t.gpr .r10 = base + BitVec.ofNat 32 (arrAt w 1) ∧
      t.gpr .r12 = base + BitVec.ofNat 32 (arrAt w (8 + j)) ∧ t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧
      t.mem = s.mem ∧ Rest [.r0, .r10, .r12, .lr] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold scanArgs
  refine wp_ldr (a := off (State.addr base) 72) (by decide) (addr 72 (by omega))
    (h.workspace.read (by omega)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 220) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 220 (by omega))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega)) fun v b => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 48 (by omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega)) fun z c => ?_
  refine wp_dp (op2_reg _ _) fun q d => ?_
  refine wp_ldr (a := off (State.addr base) 72) (by decide)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide),
      a.other .r0 (by decide)]; exact addr 72 (by omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega))
    fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans (e.rest (by decide)))))⟩
  · rw [e.gpr, d.mem, c.mem, b.mem, a.mem]
    exact header.array 1 (by decide)
  · rw [e.other .r10 (by decide), d.other .r10 (by decide), c.other .r10 (by decide),
      b.other .r10 (by decide), a.gpr]
    exact header.array 1 (by decide)
  · rw [e.other .r12 (by decide), d.other .r12 (by decide), c.other .r12 (by decide), b.gpr, a.mem, entry]
  · rw [e.other .lr (by decide), d.gpr, dpVal, c.gpr, b.mem, a.mem, header.count,
      ← BitVec.ofNat_add, show w + w = 2 * w by omega]

/-- Array `a` is copied to entry `j`; nothing else changes. -/
theorem entryCopy_ok (s : State) {base : BitVec 32} {len w a j : Nat}
    (h : ArithmeticReady base len w s) (fits : arrAt w 16 ≤ 8 * len) (ha : a < 8) (hj : j < 8)
    (entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j))) :
    WP isa (entryCopy a) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w (8 + j) = numAt s.mem (State.addr base) w a ∧
      Outside (State.addr base) (arrAt w (8 + j)) (8 * w) s.mem t.mem ∧
      Keeps (State.addr base) len w (8 + j) s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [entryCopy, WP.seq_iff]
  refine WP.mono (entryCopyArgs_ok s h ha entry) ?_
  rintro u ⟨bit, p12, count, p0, p10, memU, restU⟩
  refine WP.mono (selectAt_ok u h memU (restU.mono (by decide)) fits (by omega) (by omega)
    (by omega) (by omega) p0 p10 p12 count (by rw [bit]; decide)) ?_
  rintro t ⟨ready, value, outside, keeps, frame, rest⟩
  rw [bit] at value
  exact ⟨ready, value, outside, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
