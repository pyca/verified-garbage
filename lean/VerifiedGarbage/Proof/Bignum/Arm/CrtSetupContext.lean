module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Separated writable workspaces for CRT setup -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

def crtP (base : BitVec 32) (w : Nat) : BitVec 32 := base + BitVec.ofNat 32 (pOffset w)
def crtQ (base : BitVec 32) (w : Nat) : BitVec 32 := base + BitVec.ofNat 32 (qOffset w)
/-- The narrow workspace, in which each factor's exponentiation runs at its own width. -/
def crtN (base : BitVec 32) (w : Nat) : BitVec 32 := base + BitVec.ofNat 32 (narrowOffset w)
def crtRegions (base : BitVec 32) (len w : Nat) : List Region :=
  [⟨State.addr base, 8 * len⟩, ⟨State.addr (crtP base w), 8 * len⟩, ⟨State.addr (crtQ base w), 8 * len⟩,
    ⟨State.addr (crtN base w), 8 * len⟩]

structure CrtSetupContext (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  main : Workspace s base (8 * len)
  p : Workspace s (crtP base w) (8 * len)
  q : Workspace s (crtQ base w) (8 * len)
  narrow : Workspace s (crtN base w) (8 * len)
  width : 2 ≤ w
  widthFit : w < 2 ^ 31
  arraysFit : arrAt w 8 ≤ 8 * len
  sepMP : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr (crtP base w), 8 * len⟩
  sepMQ : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr (crtQ base w), 8 * len⟩
  sepPQ : Region.Disjoint ⟨State.addr (crtP base w), 8 * len⟩ ⟨State.addr (crtQ base w), 8 * len⟩
  sepMN : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr (crtN base w), 8 * len⟩
  sepPN : Region.Disjoint ⟨State.addr (crtP base w), 8 * len⟩ ⟨State.addr (crtN base w), 8 * len⟩
  sepQN : Region.Disjoint ⟨State.addr (crtQ base w), 8 * len⟩ ⟨State.addr (crtN base w), 8 * len⟩

theorem CrtSetupContext.congr {s t : State} {base : BitVec 32} {len w : Nat}
    (h : CrtSetupContext base len w s) (wr : t.wr = s.wr) : CrtSetupContext base len w t :=
  ⟨h.main.congr wr, h.p.congr wr, h.q.congr wr, h.narrow.congr wr, h.width, h.widthFit, h.arraysFit,
    h.sepMP, h.sepMQ, h.sepPQ, h.sepMN, h.sepPN, h.sepQN⟩

theorem CrtSetupContext.size {s : State} {base : BitVec 32} {len w : Nat}
    (h : CrtSetupContext base len w s) : 256 ≤ 8 * len := by
  have := h.arraysFit
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
  omega

theorem Workspace.eq_of_frame {s : State} {base other : BitVec 32} {size otherSize : Nat} {m m' : Mem}
    (ws : Workspace s base size) (sep : Region.Disjoint ⟨State.addr base, size⟩ ⟨State.addr other, otherSize⟩)
    (frame : Frame [⟨State.addr other, otherSize⟩] m m') : WorkspaceEq (State.addr base) size m m' :=
  WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep)

end VG.Proof.Bignum.Arm
