module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
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
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Layout

import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.TransferPadded
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBuffer
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.Words32

/-! # Copies between the narrow workspace and a full-width one

`copyLow` copies the low `v` limbs of a full-width array into a narrow one,
`copyHigh` the limbs from `v` on (none when `w = v`) into a cleared narrow
array, and `copyOut` a narrow array into the low `v` limbs of a full-width one.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp wp_cmp op2_reg op2_lsl op2_imm dpVal)

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

/-- The low `8 v` bytes of `8 w` are their value modulo `2^(64 v)`, and the rest its quotient. -/
theorem read_split {m : Mem} {a : Addr} {v w : Nat} (hv : v ≤ w) :
    (m.read a (8 * v)).toNat = (m.read a (8 * w)).toNat % 2 ^ (64 * v) ∧
      (m.read (a + BitVec.ofNat 64 (8 * v)) (8 * (w - v))).toNat = (m.read a (8 * w)).toNat / 2 ^ (64 * v) := by
  have split := read_toNat_add m (8 * (w - v)) (8 * v) a
  have pe : (2 : Nat) ^ (8 * (8 * v)) = 2 ^ (64 * v) := by rw [show 8 * (8 * v) = 64 * v by omega_arith]
  rw [show 8 * (w - v) + 8 * v = 8 * w by omega_arith, pe] at split
  have low := (m.read a (8 * v)).isLt
  rw [show (2 : Nat) ^ (8 * (8 * v)) = 2 ^ (64 * v) by rw [show 8 * (8 * v) = 64 * v by omega_arith]] at low
  have positive : 0 < 2 ^ (64 * v) := Nat.two_pow_pos _
  rw [split]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low]
  · rw [Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt low, Nat.zero_add]

theorem numAt_lt_pow (m : Mem) (base : Addr) (w j : Nat) : numAt m base w j < 2 ^ (64 * w) := by
  have := (m.read (base + BitVec.ofNat 64 (arrAt w j)) (8 * w)).isLt
  have pe : (2 : Nat) ^ (8 * (8 * w)) = 2 ^ (64 * w) := by rw [show 8 * (8 * w) = 64 * w by omega_arith]
  rw [pe] at this
  exact this

/-- The full-width source array's address in r1. -/
theorem crt_fullSource_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot j : Nat}
    (h : CrtShared g bs s) (childWs : Workspace s child (8 * workspaceWords g.words))
    (layout : CrtLayoutState child (workspaceWords g.words) g.words s.mem)
    (slotFit : slot + 4 ≤ 8 * workspaceWords g.words) (hs : slot < 4096)
    (link : s.mem.readW (off (State.addr g.base) slot) 32 = child) (hj : j < 8) :
    WP isa (.block (fullSource slot j)) s fun t =>
      t.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words j) ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  have main := h.buffers.context.main
  have header := nativeHeader_of_layout s.mem child childWs.nowrap (Nat.le_refl _) layout.layout
  rw [layout.width] at header
  have size := layout.size
  unfold fullSource
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (addr_add (by have := h.stack.nowrap; omega_arith)) (h.stack.read (by decide)) fun u a => ?_
  refine wp_ldr (a := off (State.addr g.base) slot) hs
    (by rw [a.gpr, h.savedMain]; exact addr_add (by have := main.nowrap; omega_arith))
    (by rw [a.rd, a.wr]; exact main.read slotFit) fun z b => ?_
  refine wp_ldr (a := off (State.addr child) (64 + 8 * j)) (by omega_arith)
    (by rw [b.gpr, a.mem, link]; exact addr_add (by have := childWs.nowrap; omega_arith))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact childWs.read (by omega_arith)) fun t c => WP.block_nil ?_
  refine ⟨?_, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans (c.rest (by decide)))⟩
  rw [c.gpr, b.mem, a.mem]
  exact header.array j hj

/-- The narrow array `d` in r0 and its `8 v` bytes in lr. -/
theorem crt_lowArgs_ok (s : State) {base : BitVec 32} {len v d : Nat}
    (h : ArithmeticReady base len v s) (hd : d < 8) :
    WP isa (.block (lowArgs d)) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arrAt v d) ∧ t.gpr .r5 = base ∧
      t.gpr .lr = BitVec.ofNat 32 (8 * v) ∧ t.gpr .r1 = s.gpr .r1 ∧ t.mem = s.mem ∧
      Rest [.r0, .r4, .r5, .lr] s t := by
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have fits : arrAt v 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  unfold lowArgs
  refine wp_ldr (a := off (State.addr base) (64 + 8 * d)) (by omega_arith)
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith))
    (h.workspace.read (by omega_arith)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [a.other .r0 (by decide), h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun z b => ?_
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun y c => ?_
  refine wp_mov (op2_reg _ _) fun x d' => ?_
  refine wp_mov (op2_reg _ _) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, e.mem.trans (d'.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d'.rest (by decide)).trans (e.rest (by decide)))))⟩
  · rw [e.gpr, d'.other .r4 (by decide), c.other .r4 (by decide), b.other .r4 (by decide), a.gpr]
    exact header.array d hd
  · rw [e.other .r5 (by decide), d'.gpr, c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide), h.ptr]
  · rw [e.other .lr (by decide), d'.other .lr (by decide), c.gpr, b.gpr, a.mem, header.count,
      BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 v * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  · rw [e.other .r1 (by decide), d'.other .r1 (by decide), c.other .r1 (by decide), b.other .r1 (by decide),
      a.other .r1 (by decide)]

/-- The common context of the copies: the narrow workspace selected, and a
full-width one linked from the main header. -/
structure CrtCopyCtx (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (slot v : Nat)
    (s : State) : Prop where
  shared : CrtShared g bs s
  ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s
  childWs : Workspace s child (8 * workspaceWords g.words)
  member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈
    crtRegions g.base (workspaceWords g.words) g.words
  layout : CrtLayoutState child (workspaceWords g.words) g.words s.mem
  sep : Region.Disjoint ⟨State.addr child, 8 * workspaceWords g.words⟩
    ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩
  slotFit : slot + 4 ≤ 8 * workspaceWords g.words
  slotSmall : slot < 4096
  link : s.mem.readW (off (State.addr g.base) slot) 32 = child
  le : v ≤ g.words

theorem CrtCopyCtx.child_array {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8) :
    arrAt g.words j + 8 * g.words + 16 ≤ 8 * workspaceWords g.words ∧ child.toNat + 8 * workspaceWords g.words ≤ 2 ^ 32 := by
  have fits : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.layout.width ▸ h.layout.layout.2.2.1
  exact ⟨by have := Nat.le_trans (array_end_le (w := g.words) hj) fits; omega_arith, h.childWs.nowrap⟩


theorem CrtCopyCtx.narrow_array {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v d : Nat} (h : CrtCopyCtx g bs child slot v s) (hd : d < 8) :
    arrAt v d + 8 * v + 16 ≤ 8 * workspaceWords g.words ∧
      (crtN g.base g.words).toNat + 8 * workspaceWords g.words ≤ 2 ^ 32 := by
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.ready.width ▸ h.ready.layout.2.2.1
  exact ⟨by have := Nat.le_trans (array_end_le (w := v) hd) fits; omega_arith, h.ready.workspace.nowrap⟩

/-- `n` bytes from offset `a` of one workspace to offset `b` of another, disjoint one. -/
theorem copyBetween_ok (s : State) {src dst : BitVec 32} {size a b n : Nat}
    (srcWs : Workspace s src size) (dstWs : Workspace s dst size)
    (sep : Region.Disjoint ⟨State.addr src, size⟩ ⟨State.addr dst, size⟩)
    (hn : 0 < n) (small : n < 2 ^ 32) (ha : a + n ≤ size) (hb : b + n ≤ size)
    (p0 : s.gpr .r0 = dst + BitVec.ofNat 32 b) (p1 : s.gpr .r1 = src + BitVec.ofNat 32 a)
    (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa copyBytes s fun t =>
      t.mem.read (off (State.addr dst) b) n = s.mem.read (off (State.addr src) a) n ∧
      Frame [⟨off (State.addr dst) b, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have nowrapS := srcWs.nowrap
  have nowrapD := dstWs.nowrap
  have srcAddr : State.addr (src + BitVec.ofNat 32 a) = off (State.addr src) a := addr_add (by omega_arith)
  have dstAddr : State.addr (dst + BitVec.ofNat 32 b) = off (State.addr dst) b := addr_add (by omega_arith)
  have srcNat : (src + BitVec.ofNat 32 a).toNat = src.toNat + a := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : a < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_arith : src.toNat + a < 2 ^ 32)]
  have dstNat : (dst + BitVec.ofNat 32 b).toNat = dst.toNat + b := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : b < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_arith : dst.toNat + b < 2 ^ 32)]
  have read : InRegions (s.rd ++ s.wr) (State.addr (src + BitVec.ofNat 32 a)) n := by
    rw [srcAddr]
    exact ⟨_, List.mem_append_right _ srcWs.writable, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have write : InRegions s.wr (State.addr (dst + BitVec.ofNat 32 b)) n := by
    rw [dstAddr]
    exact ⟨_, dstWs.writable, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have sepSD : Region.Disjoint ⟨State.addr (src + BitVec.ofNat 32 a), n⟩ ⟨State.addr (dst + BitVec.ofNat 32 b), n⟩ := by
    rw [srcAddr, dstAddr]
    exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  refine WP.mono (copyBuffer_ok s (n := n) hn (by rw [srcNat]; omega_arith) (by rw [dstNat]; omega_arith)
    small read write sepSD p0 p1 count) ?_
  rintro t ⟨value, frame, _, rest⟩
  rw [srcAddr, dstAddr] at value
  rw [dstAddr] at frame
  exact ⟨value, frame, rest⟩

theorem crt_copyLow_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j d : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8) (hd : d < 8) (hd0 : d ≠ 0) :
    WP isa (copyLow slot j d) s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v d =
        numAt s.mem (State.addr child) g.words j % 2 ^ (64 * v) ∧
      Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v d s.mem t.mem ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have hv : 2 ≤ v := h.ready.width ▸ h.ready.layout.1
  have le := h.le
  obtain ⟨endN, _⟩ := h.narrow_array hd
  obtain ⟨endC, _⟩ := h.child_array hj
  rw [copyLow, WP.seq_iff]
  refine WP.mono (crt_fullSource_ok s h.shared h.childWs h.layout h.slotFit h.slotSmall h.link hj) ?_
  rintro u ⟨sourceU, memU, restU⟩
  have readyU := h.ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  rw [WP.seq_iff]
  refine WP.mono (crt_lowArgs_ok u readyU hd) ?_
  rintro z ⟨dstZ, savedZ, countZ, srcZ, memZ, restZ⟩
  rw [WP.seq_iff]
  refine WP.mono (copyBetween_ok z (size := 8 * workspaceWords g.words) (a := arrAt g.words j) (b := arrAt v d)
    (n := 8 * v) (h.childWs.congr (restZ.wr.trans restU.wr)) (h.ready.workspace.congr (restZ.wr.trans restU.wr)) h.sep
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) dstZ (by rw [srcZ, sourceU]) countZ) ?_
  rintro y ⟨value, frameY, restY⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  rw [memZ, memU] at value frameY
  have outside := frame_array_outside (by omega_arith : arrAt v d + 8 * v < 2 ^ 64) frameY
  have frame := outside_workspace outside (size := 8 * workspaceWords g.words) (by omega_arith)
  have keeps := outside_array_prefix_keeps outside (by omega_arith : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega_arith : 8 * v ≤ 8 * (v + 2))
  have rest : Rest roundClobbers s t := (restU.mono (by decide)).trans
    ((restZ.mono (by decide)).trans ((restY.mono (by decide)).trans (moved.rest (by decide))))
  have ptr : t.gpr .r0 = crtN g.base g.words := by rw [moved.gpr, restY.gpr .r5 (by decide), savedZ]
  have memT : t.mem = y.mem := moved.mem
  refine ⟨(h.ready.after_array hd0 (by rw [memT]; exact keeps) (by rw [memT]; exact frame) rest ptr).1,
    ?_, by rw [memT]; exact keeps, by rw [memT]; exact frame, rest⟩
  change (t.mem.read (off (State.addr (crtN g.base g.words)) (arrAt v d)) (8 * v)).toNat = _
  rw [memT, value]
  exact (read_split le).1

theorem crt_highArgs_ok (s : State) {base main : BitVec 32} {len v w d : Nat}
    (h : ArithmeticReady base len v s) (hd : d < 8) (p2 : s.gpr .r2 = main)
    (mainAddr : State.addr (main + BitVec.ofNat 32 48) = off (State.addr main) 48)
    (mainRead : InRegions (s.rd ++ s.wr) (off (State.addr main) 48) 4)
    (count : s.mem.readW (off (State.addr main) 48) 32 = BitVec.ofNat 32 w) (hv : v ≤ w) (hw : w < 2 ^ 24) :
    WP isa (.block (highArgs d)) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arrAt v d) ∧ t.gpr .r5 = base ∧
      t.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * v) ∧ t.gpr .lr = BitVec.ofNat 32 (8 * (w - v)) ∧
      t.z = decide (w = v) ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .lr] s t := by
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have fits : arrAt v 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have hvw : v < 2 ^ 24 := by omega_arith
  unfold highArgs
  refine wp_ldr (a := off (State.addr main) 48) (by decide) (by rw [p2]; exact mainAddr) mainRead fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [a.other .r0 (by decide), h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun z b => ?_
  refine wp_dp (op2_lsl ⟨by decide, by decide⟩) fun y c => ?_
  refine wp_dp (op2_reg _ _) fun x d' => ?_
  refine wp_ldr (a := off (State.addr base) (64 + 8 * d)) (by omega_arith)
    (by rw [d'.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide),
      h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith))
    (by rw [d'.rd, d'.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun r e => ?_
  refine wp_mov (op2_reg _ _) fun q f => ?_
  refine wp_mov (op2_reg _ _) fun p g => ?_
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun o i => ?_
  refine wp_cmp (op2_imm (by decide)) fun t j zT => WP.block_nil ?_
  have memE : r.mem = s.mem := e.mem.trans (d'.mem.trans (c.mem.trans (b.mem.trans a.mem)))
  have r3 : z.gpr .r3 = BitVec.ofNat 32 v := by rw [b.gpr, a.mem, header.count]
  have r2 : x.gpr .r2 = BitVec.ofNat 32 (w - v) := by
    rw [d'.gpr, dpVal, c.other .r2 (by decide), c.other .r3 (by decide), b.other .r2 (by decide), r3, a.gpr, count]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  have lr : t.gpr .lr = BitVec.ofNat 32 (8 * (w - v)) := by
    rw [j.gpr, i.gpr, g.other .r2 (by decide), f.other .r2 (by decide), e.other .r2 (by decide), r2,
      BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (w - v) * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  refine ⟨?_, ?_, ?_, lr, ?_, j.mem.trans (i.mem.trans (g.mem.trans (f.mem.trans memE))), ?_⟩
  · rw [j.gpr, i.other .r0 (by decide), g.gpr, f.other .r4 (by decide), e.gpr, d'.mem, c.mem, b.mem, a.mem]
    exact header.array d hd
  · rw [j.gpr, i.other .r5 (by decide), g.other .r5 (by decide), f.gpr, e.other .r0 (by decide),
      d'.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide), h.ptr]
  · rw [j.gpr, i.other .r1 (by decide), g.other .r1 (by decide), f.other .r1 (by decide), e.other .r1 (by decide),
      d'.other .r1 (by decide), c.gpr, dpVal, b.other .r1 (by decide), r3, a.other .r1 (by decide),
      BitVec.shiftLeft_eq_mul_twoPow]
    change _ + BitVec.ofNat 32 v * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  · rw [zT, i.gpr, g.other .r2 (by decide), f.other .r2 (by decide), e.other .r2 (by decide), r2,
      BitVec.shiftLeft_eq_mul_twoPow]
    change (BitVec.ofNat 32 (w - v) * BitVec.ofNat 32 8 - 0 == 0) = _
    rw [← BitVec.ofNat_mul]
    by_cases eq : w = v
    · simp only [eq, Nat.sub_self, Nat.zero_mul, BitVec.ofNat_eq_ofNat, decide_true]
      decide
    · rw [decide_eq_false eq]
      apply Bool.eq_false_iff.mpr
      intro hz
      have := congrArg BitVec.toNat (eq_of_beq hz)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow] at this
      omega_arith
  · exact (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d'.rest (by decide)).trans ((e.rest (by decide)).trans ((f.rest (by decide)).trans
        ((g.rest (by decide)).trans ((i.rest (by decide)).trans (j.rest _))))))))

/-- A narrow array whose first `n` bytes may have changed: the workspace is still ready. -/
theorem CrtCopyCtx.finish_ok (s q : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v d n : Nat} {P : Mem → Prop} (h : CrtCopyCtx g bs child slot v s) (hd : d < 8) (hd0 : d ≠ 0)
    (hn : n ≤ 8 * v) (outside : Outside (State.addr (crtN g.base g.words)) (arrAt v d) n s.mem q.mem)
    (r5 : q.gpr .r5 = crtN g.base g.words) (rest : Rest roundClobbers s q) (value : P q.mem) :
    WP isa (.block [.mov .r0 (.reg .r5)]) q fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧ P t.mem ∧
      Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v d s.mem t.mem ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨endN, _⟩ := h.narrow_array hd
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  have frame := outside_workspace outside (size := 8 * workspaceWords g.words) (by omega_arith)
  have keeps := outside_array_prefix_keeps outside (by omega_arith : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega_arith : n ≤ 8 * (v + 2))
  have restT : Rest roundClobbers s t := rest.trans (moved.rest (by decide))
  have ptr : t.gpr .r0 = crtN g.base g.words := by rw [moved.gpr, r5]
  rw [← moved.mem] at frame keeps value
  exact ⟨(h.ready.after_array hd0 keeps frame restT ptr).1, value, keeps, frame, restT⟩

theorem crt_copyHigh_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j d : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8) (hd : d < 8) (hd0 : d ≠ 0)
    (half : g.words ≤ 2 * v) :
    WP isa (copyHigh slot j d) s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      (val32 s.mem (State.addr (crtN g.base g.words)) (arrAt v d) (2 * v + 2) = 0 →
        numAt t.mem (State.addr (crtN g.base g.words)) v d =
          numAt s.mem (State.addr child) g.words j / 2 ^ (64 * v)) ∧
      Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v d s.mem t.mem ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have hv : 2 ≤ v := h.ready.width ▸ h.ready.layout.1
  have le := h.le
  have words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  have main := h.shared.buffers.context.main
  have mainSize := h.shared.buffers.context.size
  obtain ⟨endN, _⟩ := h.narrow_array hd
  obtain ⟨endC, _⟩ := h.child_array hj
  rw [copyHigh, WP.seq_iff]
  refine WP.mono (crt_fullSource_ok s h.shared h.childWs h.layout h.slotFit h.slotSmall h.link hj) ?_
  rintro u ⟨sourceU, memU, restU⟩
  rw [WP.seq_iff]
  refine wp_loadStack (a := off (State.addr u.sp) 8) (by decide)
    (addr_add (by rw [restU.sp]; have := h.shared.stack.nowrap; omega_arith))
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.shared.stack.read (by decide)) fun z a => WP.block_nil ?_
  have mainZ : z.gpr .r2 = g.base := by rw [a.gpr, memU, restU.sp]; exact h.shared.savedMain
  have memZ : z.mem = s.mem := a.mem.trans memU
  have restZ : Rest roundClobbers s z := (restU.mono (by decide)).trans (a.rest (by decide))
  have r0Z : z.gpr .r0 = crtN g.base g.words := by rw [a.other .r0 (by decide), restU.gpr .r0 (by decide), h.ready.ptr]
  have readyZ := h.ready.of_mem memZ restZ r0Z
  rw [WP.seq_iff]
  refine WP.mono (crt_highArgs_ok z readyZ hd mainZ (addr_add (by have := main.nowrap; omega_arith))
    (by rw [restZ.rd, restZ.wr]; exact main.read (by have := h.shared.buffers.context.size; omega_arith))
    (by rw [memZ]; exact h.shared.main.toCrtLayoutState.nativeCount main) le (by omega_arith)) ?_
  rintro y ⟨dstY, savedY, srcY, countY, zY, memY, restY⟩
  have memYS : y.mem = s.mem := memY.trans memZ
  have restSY : Rest roundClobbers s y := restZ.trans (restY.mono (by decide))
  have src : y.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words j + 8 * v) := by
    rw [srcY, a.other .r1 (by decide), sourceU, Offset.add_add]
  rw [WP.seq_iff]
  refine WP.ite (decide (g.words = v)) (by change some y.z = _; rw [zY]) ?_ ?_
  · intro equal
    have eq : g.words = v := of_decide_eq_true equal
    refine WP.block_nil (CrtCopyCtx.finish_ok s y h hd hd0 (n := 0) (by omega_arith)
      (P := fun m => val32 s.mem (State.addr (crtN g.base g.words)) (arrAt v d) (2 * v + 2) = 0 →
        numAt m (State.addr (crtN g.base g.words)) v d =
          numAt s.mem (State.addr child) g.words j / 2 ^ (64 * v))
      (by rw [memYS]; exact Outside.refl _ _ _ _) savedY restSY ?_)
    intro cleared
    have zeroLow := (val32_zero_split cleared).1
    have lt := numAt_lt_pow s.mem (State.addr child) g.words j
    rw [show 64 * g.words = 64 * v by rw [eq]] at lt
    rw [numAt_native, memYS, zeroLow, Nat.div_eq_of_lt lt]
  · intro unequal
    have ne : g.words ≠ v := of_decide_eq_false unequal
    refine WP.mono (copyBetween_ok y (size := 8 * workspaceWords g.words) (a := arrAt g.words j + 8 * v)
      (b := arrAt v d) (n := 8 * (g.words - v)) (h.childWs.congr restSY.wr) (h.ready.workspace.congr restSY.wr)
      h.sep (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) dstY src countY) ?_
    rintro q ⟨value, frameQ, restQ⟩
    rw [memYS] at value frameQ
    have outside := frame_array_outside (by omega_arith : arrAt v d + 8 * (g.words - v) < 2 ^ 64) frameQ
    refine CrtCopyCtx.finish_ok s q h hd hd0 (n := 8 * (g.words - v))
      (P := fun m => val32 s.mem (State.addr (crtN g.base g.words)) (arrAt v d) (2 * v + 2) = 0 →
        numAt m (State.addr (crtN g.base g.words)) v d =
          numAt s.mem (State.addr child) g.words j / 2 ^ (64 * v)) (by omega_arith) outside
      (by rw [restQ.gpr .r5 (by decide), savedY]) (restSY.trans (restQ.mono (by decide))) ?_
    intro cleared
    have zero := cleared
    rw [show 2 * v + 2 = 2 * (g.words - v) + ((2 * v - 2 * (g.words - v)) + 2) by omega_arith] at zero
    have high := (val32_zero_split (val32_zero_split zero).2).1
    rw [numAt_native, show 2 * v = 2 * (g.words - v) + (2 * v - 2 * (g.words - v)) by omega_arith, val32_append,
      outside.val32 (d := arrAt v d + 4 * (2 * (g.words - v))) (Or.inr (by omega_arith)) (by omega_arith), high,
      Nat.mul_zero, Nat.add_zero, ← read_eq_val32, show 4 * (2 * (g.words - v)) = 8 * (g.words - v) by omega_arith,
      value]
    have split := (read_split (m := s.mem) (a := off (State.addr child) (arrAt g.words j)) le).2
    unfold VG.Proof.Mont.off at split ⊢
    rw [Offset.add_add] at split
    exact split

/-- The narrow array `a` as the source, the full array (in r1) as the destination. -/
theorem crt_outArgs_ok (s : State) {base : BitVec 32} {len v a : Nat}
    (h : ArithmeticReady base len v s) (ha : a < 8) :
    WP isa (.block (outArgs a)) s fun t =>
      t.gpr .r0 = s.gpr .r1 ∧ t.gpr .r1 = base + BitVec.ofNat 32 (arrAt v a) ∧ t.gpr .r5 = base ∧
      t.gpr .lr = BitVec.ofNat 32 (8 * v) ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r4, .r5, .lr] s t := by
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have fits : arrAt v 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  unfold outArgs
  refine wp_mov (op2_reg _ _) fun u a' => ?_
  refine wp_ldr (a := off (State.addr base) (64 + 8 * a)) (by omega_arith)
    (by rw [a'.other .r0 (by decide), h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith))
    (by rw [a'.rd, a'.wr]; exact h.workspace.read (by omega_arith)) fun z b => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [b.other .r0 (by decide), a'.other .r0 (by decide), h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith))
    (by rw [b.rd, b.wr, a'.rd, a'.wr]; exact h.workspace.read (by omega_arith)) fun y c => ?_
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun x d => ?_
  refine wp_mov (op2_reg _ _) fun r e => ?_
  refine wp_mov (op2_reg _ _) fun t f => WP.block_nil ?_
  have r0 : x.gpr .r0 = base := by
    rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide),
      a'.other .r0 (by decide), h.ptr]
  refine ⟨?_, ?_, ?_, ?_, f.mem.trans (e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a'.mem)))),
    (a'.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans ((e.rest (by decide)).trans (f.rest (by decide))))))⟩
  · rw [f.gpr, e.other .r4 (by decide), d.other .r4 (by decide), c.other .r4 (by decide), b.other .r4 (by decide),
      a'.gpr]
  · rw [f.other .r1 (by decide), e.other .r1 (by decide), d.other .r1 (by decide), c.other .r1 (by decide), b.gpr,
      a'.mem]
    exact header.array a ha
  · rw [f.other .r5 (by decide), e.gpr, r0]
  · rw [f.other .lr (by decide), e.other .lr (by decide), d.gpr, c.gpr, b.mem, a'.mem, header.count,
      BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 v * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]

theorem crt_copyOut_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j a : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8) (ha : a < 8) :
    WP isa (copyOut slot j a) s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      t.mem.read (off (State.addr child) (arrAt g.words j)) (8 * v) =
        s.mem.read (off (State.addr (crtN g.base g.words)) (arrAt v a)) (8 * v) ∧
      Outside (State.addr child) (arrAt g.words j) (8 * v) s.mem t.mem ∧ Rest roundClobbers s t := by
  have le := h.le
  have hv : 2 ≤ v := h.ready.width ▸ h.ready.layout.1
  obtain ⟨endN, _⟩ := h.narrow_array ha
  obtain ⟨endC, _⟩ := h.child_array hj
  rw [copyOut, WP.seq_iff]
  refine WP.mono (crt_fullSource_ok s h.shared h.childWs h.layout h.slotFit h.slotSmall h.link hj) ?_
  rintro u ⟨sourceU, memU, restU⟩
  have readyU := h.ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  rw [WP.seq_iff]
  refine WP.mono (crt_outArgs_ok u readyU ha) ?_
  rintro z ⟨dstZ, srcZ, savedZ, countZ, memZ, restZ⟩
  have restSZ : Rest roundClobbers s z := (restU.mono (by decide)).trans (restZ.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (copyBetween_ok z (size := 8 * workspaceWords g.words) (a := arrAt v a) (b := arrAt g.words j)
    (n := 8 * v) (h.ready.workspace.congr restSZ.wr) (h.childWs.congr restSZ.wr) h.sep.symm
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [dstZ, sourceU]) srcZ countZ) ?_
  rintro y ⟨value, frameY, restY⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  rw [memZ, memU] at value frameY
  have outside := frame_array_outside (by omega_arith : arrAt g.words j + 8 * v < 2 ^ 64) frameY
  have rest : Rest roundClobbers s t := restSZ.trans ((restY.mono (by decide)).trans (moved.rest (by decide)))
  have ptr : t.gpr .r0 = crtN g.base g.words := by rw [moved.gpr, restY.gpr .r5 (by decide), savedZ]
  have sub : Region.Sub ⟨off (State.addr child) (arrAt g.words j), 8 * v⟩
      ⟨State.addr child, 8 * workspaceWords g.words⟩ := Offset.sub_base _ (by omega_arith)
  have frameT : Frame [⟨off (State.addr child) (arrAt g.words j), 8 * v⟩] s.mem t.mem := by
    rw [moved.mem]; exact frameY
  obtain ⟨ready, _⟩ := h.ready.after_external frameT
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep.symm.sub_right sub)
    (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact (((h.shared.stack.separate.symm.sub_right (Region.sub_prefix (by decide))).sub_left
        (crt_region_sub_workspace h.shared.buffers.workspace h.shared.buffers.storageFits h.member)).sub_left sub).symm)
    rest ptr
  exact ⟨ready, by rw [moved.mem]; exact value, by rw [moved.mem]; exact outside, rest⟩

/-- Clearing an array of a workspace with its layout, whatever its values. -/
theorem clearLayout_ok (s : State) {base : BitVec 32} {len w o : Nat}
    (h : LayoutFrameReady base len w s) (ho : o < 8) :
    WP isa (clearOperandBuffer (64 + 8 * o)) s fun t => LayoutFrameReady base len w t ∧
      val32 t.mem (State.addr base) (arrAt w o) (2 * w + 2) = 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := Nat.le_trans (array_end_le ho) fits
  have small : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have nowrap := h.workspace.nowrap
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  refine WP.mono (clearOperandBuffer_ok s h.workspace (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) h.ptr header.count (header.array o ho) h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨zero, outside, frame, ptr, rest⟩
  have keeps := outside_array_prefix_keeps outside (by omega_arith : 8 * len < 2 ^ 64) (by omega_arith)
  exact ⟨h.after_array keeps frame rest ptr, zero, keeps, frame, rest⟩

/-- A cleared array whose low `v` limbs were then written holds them. -/
theorem numAt_of_copied {m m' : Mem} {base : Addr} {w v o : Nat} (hv : v ≤ w)
    (cleared : val32 m base (arrAt w o) (2 * w + 2) = 0)
    (outside : Outside base (arrAt w o) (8 * v) m m') (fit : arrAt w o + 8 * w + 8 ≤ 2 ^ 64) :
    numAt m' base w o = (m'.read (off base (arrAt w o)) (8 * v)).toNat := by
  rw [show 2 * w + 2 = 2 * v + ((2 * w - 2 * v) + 2) by omega_arith] at cleared
  have high := (val32_zero_split (val32_zero_split cleared).2).1
  rw [numAt_native, show 2 * w = 2 * v + (2 * w - 2 * v) by omega_arith, val32_append,
    outside.val32 (d := arrAt w o + 4 * (2 * v)) (Or.inr (by omega_arith)) (by omega_arith), high,
    Nat.mul_zero, Nat.add_zero, ← read_eq_val32, show 4 * (2 * v) = 8 * v by omega_arith]

end VG.Proof.Bignum.Arm
