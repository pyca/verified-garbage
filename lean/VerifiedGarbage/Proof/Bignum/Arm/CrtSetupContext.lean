module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Separated writable workspaces for CRT setup -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt)

def crtP (base : BitVec 32) (w : Nat) : BitVec 32 := base + BitVec.ofNat 32 (pOffset w)
def crtQ (base : BitVec 32) (w : Nat) : BitVec 32 := base + BitVec.ofNat 32 (qOffset w)
def crtRegions (base : BitVec 32) (len w : Nat) : List Region :=
  [⟨State.addr base, 8 * len⟩, ⟨State.addr (crtP base w), 8 * len⟩, ⟨State.addr (crtQ base w), 8 * len⟩]

structure CrtSetupContext (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  main : Workspace s base (8 * len)
  p : Workspace s (crtP base w) (8 * len)
  q : Workspace s (crtQ base w) (8 * len)
  width : 2 ≤ w
  widthFit : w < 2 ^ 31
  arraysFit : arrAt w 8 ≤ 8 * len
  sepMP : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr (crtP base w), 8 * len⟩
  sepMQ : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr (crtQ base w), 8 * len⟩
  sepPQ : Region.Disjoint ⟨State.addr (crtP base w), 8 * len⟩ ⟨State.addr (crtQ base w), 8 * len⟩

theorem CrtSetupContext.congr {s t : State} {base : BitVec 32} {len w : Nat}
    (h : CrtSetupContext base len w s) (wr : t.wr = s.wr) : CrtSetupContext base len w t :=
  ⟨h.main.congr wr, h.p.congr wr, h.q.congr wr, h.width, h.widthFit, h.arraysFit, h.sepMP, h.sepMQ, h.sepPQ⟩

theorem CrtSetupContext.size {s : State} {base : BitVec 32} {len w : Nat}
    (h : CrtSetupContext base len w s) : 256 ≤ 8 * len := by
  have := h.arraysFit
  simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at this
  omega

theorem Workspace.eq_of_frame {s : State} {base other : BitVec 32} {size otherSize : Nat} {m m' : Mem}
    (ws : Workspace s base size) (sep : Region.Disjoint ⟨State.addr base, size⟩ ⟨State.addr other, otherSize⟩)
    (frame : Frame [⟨State.addr other, otherSize⟩] m m') : WorkspaceEq (State.addr base) size m m' :=
  WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep)

end VG.Proof.Bignum.Arm
