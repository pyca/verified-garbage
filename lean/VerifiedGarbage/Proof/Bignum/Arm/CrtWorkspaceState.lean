module

public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Stable public layout facts while another CRT workspace is active -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (Layout wOf arrAt)

structure CrtLayoutState (base : BitVec 32) (len w : Nat) (mem : Mem) : Prop where
  layout : Layout mem (State.addr base) len
  width : wOf mem (State.addr base) = w

structure CrtMainState (base : BitVec 32) (len w : Nat) (mem : Mem) : Prop
    extends CrtLayoutState base len w mem where
  p : mem.readW (off (State.addr base) 224) 32 = base + BitVec.ofNat 32 (pOffset w)
  q : mem.readW (off (State.addr base) 228) 32 = base + BitVec.ofNat 32 (qOffset w)
  product : mem.readW (off (State.addr base) 232) 32 = base + BitVec.ofNat 32 (productOffset w)
  compare : mem.readW (off (State.addr base) 236) 32 = base + BitVec.ofNat 32 (compareOffset w)
  modulus : mem.readW (off (State.addr base) 240) 32 = base + BitVec.ofNat 32 (modulusOffset w)

structure CrtPrimeState (base parent : BitVec 32) (len w : Nat) (mem : Mem) : Prop
    extends CrtLayoutState base len w mem where
  link : mem.readW (off (State.addr base) 216) 32 = parent

theorem CrtLayoutState.size {base : BitVec 32} {len w : Nat} {mem : Mem}
    (h : CrtLayoutState base len w mem) : 256 ≤ 8 * len := by
  have := h.layout.2.2.1
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
  omega

theorem CrtLayoutState.congr {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (h : CrtLayoutState base len w m) (eq : WorkspaceEq (State.addr base) (8 * len) m m') :
    CrtLayoutState base len w m' :=
  ⟨eq.layout h.layout, (eq.width (by have := h.size; omega)).trans h.width⟩

theorem CrtMainState.congr {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (h : CrtMainState base len w m) (eq : WorkspaceEq (State.addr base) (8 * len) m m') :
    CrtMainState base len w m' := by
  have size := h.toCrtLayoutState.size
  exact ⟨h.toCrtLayoutState.congr eq,
    (eq.word (d := 224) (bits := 32) (by omega)).trans h.p,
    (eq.word (d := 228) (bits := 32) (by omega)).trans h.q,
    (eq.word (d := 232) (bits := 32) (by omega)).trans h.product,
    (eq.word (d := 236) (bits := 32) (by omega)).trans h.compare,
    (eq.word (d := 240) (bits := 32) (by omega)).trans h.modulus⟩

theorem CrtPrimeState.congr {base parent : BitVec 32} {len w : Nat} {m m' : Mem}
    (h : CrtPrimeState base parent len w m) (eq : WorkspaceEq (State.addr base) (8 * len) m m') :
    CrtPrimeState base parent len w m' :=
  ⟨h.toCrtLayoutState.congr eq, (eq.word (d := 216) (bits := 32) (by have := h.toCrtLayoutState.size; omega)).trans h.link⟩

theorem CrtLayoutState.nativeCount {s : State} {base : BitVec 32} {len w : Nat}
    (h : CrtLayoutState base len w s.mem) (ws : Workspace s base (8 * len)) :
    s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w := by
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  exact header.count

end VG.Proof.Bignum.Arm
