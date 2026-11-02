module
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-! # Saving registers outside the workspace preserves its shared RSA precondition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout)

structure WorkspaceEq (base : Addr) (size : Nat) (mem mem' : Mem) : Prop where
  read : ∀ d n, d + n ≤ size → mem'.read (off base d) n = mem.read (off base d) n

theorem WorkspaceEq.of_frame {base : Addr} {size : Nat} {mem mem' : Mem} {regions : List Region}
    (fit : size < 2 ^ 64) (frame : Frame regions mem mem')
    (sep : ∀ r ∈ regions, (⟨base, size⟩ : Region).Disjoint r) : WorkspaceEq base size mem mem' := by
  refine ⟨fun d n hn => frame.read (r := ⟨base, size⟩)
    (Offset.contains_base _ hn (by omega)) sep (by omega)⟩

theorem WorkspaceEq.word {base : Addr} {size : Nat} {mem mem' : Mem}
    (h : WorkspaceEq base size mem mem') {d bits : Nat} (fit : d + bits / 8 ≤ size) :
    mem'.readW (off base d) bits = mem.readW (off base d) bits := by
  simp only [Mem.readW, h.read d (bits / 8) fit]

theorem WorkspaceEq.width {base : Addr} {size : Nat} {mem mem' : Mem}
    (h : WorkspaceEq base size mem mem') (fit : 56 ≤ size) : wOf mem' base = wOf mem base := by
  exact congrArg BitVec.toNat (h.word (d := 48) (bits := 64) fit)

theorem WorkspaceEq.layout {base : Addr} {len : Nat} {mem mem' : Mem}
    (h : WorkspaceEq base (8 * len) mem mem') (layout : Layout mem base len) : Layout mem' base len := by
  have fit := layout.2.2.1
  have small : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit
    omega
  have width := h.width (by omega)
  unfold Layout
  rw [width]
  refine ⟨layout.1, layout.2.1, layout.2.2.1, ?_⟩
  intro j hj
  unfold wordAt
  rw [h.word (bits := 64) (by simp only [Proof.Rsa.Mont.arrWord]; omega)]
  exact layout.2.2.2 j hj

theorem WorkspaceEq.number {base : Addr} {len w j : Nat} {mem mem' : Mem}
    (h : WorkspaceEq base (8 * len) mem mem') (fit : arrAt w 8 ≤ 8 * len) (hj : j < 8) :
    numAt mem' base w j = numAt mem base w j := by
  have bound := array_end_le (w := w) hj
  unfold numAt
  rw [h.read (arrAt w j) (8 * w) (by omega)]

end VG.Proof.Bignum.Arm
