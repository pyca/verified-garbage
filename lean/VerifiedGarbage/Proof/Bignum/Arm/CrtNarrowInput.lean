module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowReduce
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Copy the reduced input into the narrow workspace

The reduced input is below the factor, which fits the narrow width, so its
low words, as many as the narrow workspace has, are the whole value.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_reg op2_lsl)

/-- A value below `2^(64 v)` is its low `8 v` bytes. -/
theorem read_low_of_lt {m : Mem} {a : Addr} {v w : Nat} (hv : v ≤ w)
    (lt : (m.read a (8 * w)).toNat < 2 ^ (64 * v)) : (m.read a (8 * v)).toNat = (m.read a (8 * w)).toNat := by
  have split := read_toNat_add m (8 * (w - v)) (8 * v) a
  have pe : (2 : Nat) ^ (8 * (8 * v)) = 2 ^ (64 * v) := by rw [show 8 * (8 * v) = 64 * v by omega_arith]
  rw [show 8 * (w - v) + 8 * v = 8 * w by omega_arith] at split
  rw [pe] at split
  rw [split] at lt ⊢
  have high : (m.read (a + BitVec.ofNat 64 (8 * v)) (8 * (w - v))).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (m.read (a + BitVec.ofNat 64 (8 * v)) (8 * (w - v))).toNat with zero | pos
    · exact zero
    · have := Nat.mul_le_mul_left (2 ^ (64 * v)) pos
      omega_arith
  rw [high, Nat.mul_zero, Nat.add_zero]

theorem numAt_lt_pow (m : Mem) (base : Addr) (w j : Nat) : numAt m base w j < 2 ^ (64 * w) := by
  have := (m.read (base + BitVec.ofNat 64 (arrAt w j)) (8 * w)).isLt
  have pe : (2 : Nat) ^ (8 * (8 * w)) = 2 ^ (64 * w) := by rw [show 8 * (8 * w) = 64 * w by omega_arith]
  rw [pe] at this
  exact this

theorem crt_narrowSource_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (childWs : Workspace s child (8 * workspaceWords g.words))
    (layout : CrtLayoutState child (workspaceWords g.words) g.words s.mem)
    (slotFit : slot + 4 ≤ 8 * workspaceWords g.words) (hs : slot < 4096)
    (link : s.mem.readW (off (State.addr g.base) slot) 32 = child) :
    WP isa (.block (narrowSource slot)) s fun t =>
      t.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words 1) ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  have main := h.buffers.context.main
  have header := nativeHeader_of_layout s.mem child childWs.nowrap (Nat.le_refl _) layout.layout
  rw [layout.width] at header
  have size := layout.size
  unfold narrowSource
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (addr_add (by have := h.stack.nowrap; omega_arith)) (h.stack.read (by decide)) fun u a => ?_
  refine wp_ldr (a := off (State.addr g.base) slot) hs
    (by rw [a.gpr, h.savedMain]; exact addr_add (by have := main.nowrap; omega_arith))
    (by rw [a.rd, a.wr]; exact main.read slotFit) fun z b => ?_
  refine wp_ldr (a := off (State.addr child) 72) (by decide)
    (by rw [b.gpr, a.mem, link]; exact addr_add (by have := childWs.nowrap; omega_arith))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact childWs.read (by omega_arith)) fun t c => WP.block_nil ?_
  refine ⟨?_, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans (c.rest (by decide)))⟩
  rw [c.gpr, b.mem, a.mem]
  exact header.array 1 (by decide)

theorem crt_narrowInputArgs_ok (s : State) {base : BitVec 32} {len v : Nat}
    (h : ArithmeticReady base len v s) :
    WP isa (.block narrowInputArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arrAt v 1) ∧ t.gpr .r5 = base ∧
      t.gpr .lr = BitVec.ofNat 32 (8 * v) ∧ t.mem = s.mem ∧ Rest [.r0, .r4, .r5, .lr] s t := by
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have fits : arrAt v 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  unfold narrowInputArgs
  refine wp_ldr (a := off (State.addr base) 72) (by decide)
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)) (h.workspace.read (by omega_arith)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [a.other .r0 (by decide), h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun z b => ?_
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun y c => ?_
  refine wp_mov (op2_reg _ _) fun x d => ?_
  refine wp_mov (op2_reg _ _) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans (e.rest (by decide)))))⟩
  · rw [e.gpr, d.other .r4 (by decide), c.other .r4 (by decide), b.other .r4 (by decide), a.gpr]
    exact header.array 1 (by decide)
  · rw [e.other .r5 (by decide), d.gpr, c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide), h.ptr]
  · rw [e.other .lr (by decide), d.other .lr (by decide), c.gpr, b.gpr, a.mem, header.count,
      BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 v * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]

theorem crt_narrowInput_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v M x : Nat} (h : CrtShared g bs s)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s)
    (childWs : Workspace s child (8 * workspaceWords g.words))
    (sep : Region.Disjoint ⟨State.addr child, 8 * workspaceWords g.words⟩
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩)
    (slotFit : slot + 4 ≤ 8 * workspaceWords g.words) (hs : slot < 4096)
    (link : s.mem.readW (off (State.addr g.base) slot) 32 = child)
    (reduced : CrtReducedState child (workspaceWords g.words) g.words M x s.mem)
    (narrowM : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M) (le : v ≤ g.words) :
    WP isa (narrowInput slot) s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 1 = x % M ∧
      Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v 1 s.mem t.mem ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have nowrapN := ready.workspace.nowrap
  have nowrapC := childWs.nowrap
  have hv : 2 ≤ v := ready.width ▸ ready.layout.1
  have fitsN : arrAt v 8 ≤ 8 * (workspaceWords g.words) := ready.width ▸ ready.layout.2.2.1
  have fitsC : arrAt g.words 8 ≤ 8 * (workspaceWords g.words) := reduced.layout.width ▸ reduced.layout.layout.2.2.1
  have endN := Nat.le_trans (array_end_le (w := v) (by decide : 1 < 8)) fitsN
  have endC := Nat.le_trans (array_end_le (w := g.words) (by decide : 1 < 8)) fitsC
  let src := child + BitVec.ofNat 32 (arrAt g.words 1)
  let dst := (crtN g.base g.words) + BitVec.ofNat 32 (arrAt v 1)
  have srcAddr : State.addr src = off (State.addr child) (arrAt g.words 1) := addr_add (by omega_arith)
  have dstAddr : State.addr dst = off (State.addr (crtN g.base g.words)) (arrAt v 1) := addr_add (by omega_arith)
  have srcNat : src.toNat = child.toNat + arrAt g.words 1 := by
    simp only [src, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith : arrAt g.words 1 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_arith : child.toNat + arrAt g.words 1 < 2 ^ 32)]
  have dstNat : dst.toNat = (crtN g.base g.words).toNat + arrAt v 1 := by
    simp only [dst, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith : arrAt v 1 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_arith : (crtN g.base g.words).toNat + arrAt v 1 < 2 ^ 32)]
  rw [narrowInput, WP.seq_iff]
  refine WP.mono (crt_narrowSource_ok s h childWs reduced.layout slotFit hs link) ?_
  rintro u ⟨sourceU, memU, restU⟩
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready.ptr)
  rw [WP.seq_iff]
  refine WP.mono (crt_narrowInputArgs_ok u readyU) ?_
  rintro z ⟨dstZ, savedZ, countZ, memZ, restZ⟩
  have read : InRegions (z.rd ++ z.wr) (State.addr src) (8 * v) := by
    rw [restZ.rd, restZ.wr, restU.rd, restU.wr, srcAddr]
    exact ⟨_, List.mem_append_right _ childWs.writable, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have write : InRegions z.wr (State.addr dst) (8 * v) := by
    rw [restZ.wr, restU.wr, dstAddr]
    exact ⟨_, ready.workspace.writable, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have sepSD : Region.Disjoint ⟨State.addr src, 8 * v⟩ ⟨State.addr dst, 8 * v⟩ := by
    rw [srcAddr, dstAddr]
    exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  rw [WP.seq_iff]
  refine WP.mono (copyBuffer_ok z (n := 8 * v) (by omega_arith) (by rw [srcNat]; omega_arith) (by rw [dstNat]; omega_arith)
    (by omega_arith) read write sepSD dstZ ((restZ.gpr .r1 (by decide)).trans sourceU) countZ) ?_
  rintro y ⟨value, frameY, _, restY⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  rw [memZ, memU, srcAddr, dstAddr] at value
  rw [memZ, memU, dstAddr] at frameY
  have outside := frame_array_outside (by omega_arith : arrAt v 1 + 8 * v < 2 ^ 64) frameY
  have frame := outside_workspace outside (size := 8 * (workspaceWords g.words)) (by omega_arith)
  have keeps := outside_array_prefix_keeps outside (by omega_arith : 8 * (workspaceWords g.words) < 2 ^ 64) (by omega_arith : 8 * v ≤ 8 * (v + 2))
  have rest : Rest roundClobbers s t := (restU.mono (by decide)).trans
    ((restZ.mono (by decide)).trans ((restY.mono (by decide)).trans
      (moved.rest (by decide))))
  have ptr : t.gpr .r0 = (crtN g.base g.words) := by
    rw [moved.gpr, restY.gpr .r5 (by decide), savedZ]
  have memT : t.mem = y.mem := moved.mem
  refine ⟨(ready.after_array (o := 1) (by decide) (by rw [memT]; exact keeps) (by rw [memT]; exact frame) rest ptr).1,
    ?_, by rw [memT]; exact keeps, by rw [memT]; exact frame, rest⟩
  have total : numAt s.mem (State.addr child) g.words 1 = x % M := reduced.input
  have bound : numAt s.mem (State.addr child) g.words 1 < 2 ^ (64 * v) := by
    rw [total]
    have := numAt_lt_pow s.mem (State.addr (crtN g.base g.words)) v 0
    rw [narrowM] at this
    exact Nat.lt_trans (Nat.mod_lt _ (by have := reduced.positive; omega_arith)) this
  change (t.mem.read (off (State.addr (crtN g.base g.words)) (arrAt v 1)) (8 * v)).toNat = _
  rw [memT, value, read_low_of_lt le bound]
  exact total

end VG.Proof.Bignum.Arm
